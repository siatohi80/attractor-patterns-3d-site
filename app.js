// Attractor Patterns 3D: project an attractor-driven pattern onto a model, then cut, extrude or recess it.
// Units are mm, Z is up. The pattern engine (engine.js, shared with the 2D playground) works on a flat "sheet":
// the model's footprint seen from the projection direction.
import * as THREE from 'three';
import {OrbitControls} from 'three/addons/controls/OrbitControls.js';
import {STLLoader} from 'three/addons/loaders/STLLoader.js';
import {OBJLoader} from 'three/addons/loaders/OBJLoader.js';
import {PLYLoader} from 'three/addons/loaders/PLYLoader.js';
import {GLTFLoader} from 'three/addons/loaders/GLTFLoader.js';
import {STLExporter} from 'three/addons/exporters/STLExporter.js';
import {OBJExporter} from 'three/addons/exporters/OBJExporter.js';
import {GLTFExporter} from 'three/addons/exporters/GLTFExporter.js';
import * as BGU from 'three/addons/utils/BufferGeometryUtils.js';
import {computeBoundsTree,disposeBoundsTree,acceleratedRaycast} from 'three-mesh-bvh';

THREE.BufferGeometry.prototype.computeBoundsTree=computeBoundsTree;
THREE.BufferGeometry.prototype.disposeBoundsTree=disposeBoundsTree;
THREE.Mesh.prototype.raycast=acceleratedRaycast;

const E=window.APE,S=E.S,PC=window.polygonClipping,EARCUT=window.earcut.default||window.earcut;
const $=id=>document.getElementById(id);
const css=n=>getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const clamp=E.clamp;
const isDark=()=>{const t=document.documentElement.dataset.theme;return t==='dark'||(t!=='light'&&matchMedia('(prefers-color-scheme: dark)').matches);};
const CDN='https://cdn.jsdelivr.net/npm/';
const FACING=Math.cos(70*Math.PI/180);   // faces steeper than 70° to the projection stay plain
const PAD=62;                             // sheet padding (mm), leaves room for the pattern shift
const HIDDEN=new Set(['rd','jewel']);     // live simulation and facet texture don't make 3D openings

// ---------- state ----------
Object.assign(S,{pattern:'holes',s:12,b:1.5,m:1.5,margin:4,fillet:0.5,R:200,atts:[]});
const A={geo:null,orig:null,history:[],name:'',info:'',closed:false,sample:'grille',
  dir:'wrap',viewFrame:null,rot:0,ox:0,oy:0,op:'cut',depth:1.5,units:1,up:'z',
  atts:[],sel:-1,selP:-1,tool:'select',pending:null,applied:false,busy:false};
let F=null;          // mapping frame for the original model
let raw=null;        // last imported geometry before units and axis, so those selects can re-apply

// ---------- three.js scene ----------
const canvas=$('view');
const renderer=new THREE.WebGLRenderer({canvas,antialias:true,preserveDrawingBuffer:true});
renderer.setPixelRatio(Math.min(devicePixelRatio||1,2));
const scene=new THREE.Scene();
const camera=new THREE.PerspectiveCamera(35,1,1,100000);camera.up.set(0,0,1);
const controls=new OrbitControls(camera,canvas);controls.enableDamping=true;controls.dampingFactor=0.12;
controls.mouseButtons={LEFT:THREE.MOUSE.ROTATE,MIDDLE:THREE.MOUSE.DOLLY,RIGHT:THREE.MOUSE.PAN};
scene.add(new THREE.HemisphereLight(0xffffff,0x8a8f99,1.6));
const key=new THREE.DirectionalLight(0xffffff,1.6);scene.add(key);scene.add(key.target);
const fill=new THREE.DirectionalLight(0xffffff,0.5);scene.add(fill);
const tex=new THREE.CanvasTexture(document.createElement('canvas'));tex.colorSpace=THREE.SRGBColorSpace;tex.anisotropy=8;
const mat=new THREE.MeshStandardMaterial({map:tex,vertexColors:true,roughness:0.55,metalness:0.05,side:THREE.DoubleSide,flatShading:false});
const mesh=new THREE.Mesh(new THREE.BufferGeometry(),mat);scene.add(mesh);
const edges=new THREE.LineSegments(new THREE.BufferGeometry(),new THREE.LineBasicMaterial({transparent:true,opacity:0.35}));scene.add(edges);
const handles=new THREE.Group();scene.add(handles);
const grid=new THREE.GridHelper(1,10);grid.rotation.x=Math.PI/2;grid.material.transparent=true;grid.material.opacity=0.35;scene.add(grid);

function resize(){const r=$('cwrap').getBoundingClientRect();renderer.setSize(r.width,r.height,false);camera.aspect=r.width/Math.max(1,r.height);camera.updateProjectionMatrix();}
new ResizeObserver(resize).observe($('cwrap'));
function loop(){controls.update();renderer.render(scene,camera);requestAnimationFrame(loop);}

// ---------- geometry helpers ----------
const v3=(a)=>new THREE.Vector3(a[0],a[1],a[2]);
// positions-only, welded, indexed copy. fid gives a face id per triangle (from STEP/3DM faces); -1 or missing
// triangles are grouped into faces by a 30° crease. The ids live in g.userData.fid.
function cleanGeometry(g,fid){
  let p=g.index?g.toNonIndexed():g.clone();for(const k of Object.keys(p.attributes))if(k!=='position')p.deleteAttribute(k);
  p.computeBoundingBox();const diag=p.boundingBox.getSize(new THREE.Vector3()).length()||1;
  p=BGU.mergeVertices(p,diag*1e-6);p.userData={};return dropDegenerate(p,fid);
}
function dropDegenerate(g,fid){const P=g.attributes.position,I=g.index.array,o=[],f=[],a=new THREE.Vector3(),b=new THREE.Vector3(),c=new THREE.Vector3();
  for(let t=0;t<I.length;t+=3){const i=I[t],j=I[t+1],k=I[t+2];if(i===j||j===k||i===k)continue;a.fromBufferAttribute(P,i);b.fromBufferAttribute(P,j);c.fromBufferAttribute(P,k);
    if(b.sub(a).cross(c.sub(a)).lengthSq()<1e-14)continue;o.push(i,j,k);f.push(fid?fid[t/3]:-1);}
  g.setIndex(o);g.userData.fid=Int32Array.from(f);segment(g);return g;}
// edge -> triangles map on the welded index
function edgeMap(g){const I=g.index.array,m=new Map();for(let t=0;t<I.length/3;t++)for(let e=0;e<3;e++){const a=I[3*t+e],b=I[3*t+(e+1)%3],k=a<b?a*4294967296+b:b*4294967296+a;const l=m.get(k);if(l)l.push(t);else m.set(k,[t]);}return m;}
// give triangles without a face id their own faces, split at creases sharper than 30°
function segment(g){const fid=g.userData.fid;if(!fid.some(v=>v<0))return;const N=triNormals(g),em=edgeMap(g),nt=fid.length,nb=Array.from({length:nt},()=>[]);
  for(const l of em.values())if(l.length===2){nb[l[0]].push(l[1]);nb[l[1]].push(l[0]);}
  let next=fid.reduce((m,v)=>Math.max(m,v),-1)+1;const cos=Math.cos(30*Math.PI/180);
  for(let t=0;t<nt;t++){if(fid[t]>=0)continue;const id=next++;fid[t]=id;const st=[t];
    while(st.length){const u=st.pop();for(const w of nb[u])if(fid[w]<0&&N[3*u]*N[3*w]+N[3*u+1]*N[3*w+1]+N[3*u+2]*N[3*w+2]>cos){fid[w]=id;st.push(w);}}}}
// per face: area, area-weighted normal, neighbours
function faceInfo(g){const fid=g.userData.fid,N=triNormals(g),P=g.attributes.position,I=g.index.array,info=new Map(),a=new THREE.Vector3(),b=new THREE.Vector3(),c=new THREE.Vector3();
  const get=id=>info.get(id)||info.set(id,{area:0,n:new THREE.Vector3(),adj:new Set()}).get(id);
  for(let t=0;t<fid.length;t++){a.fromBufferAttribute(P,I[3*t]);b.fromBufferAttribute(P,I[3*t+1]);c.fromBufferAttribute(P,I[3*t+2]);const ar=b.sub(a).cross(c.sub(a)).length()/2,f=get(fid[t]);f.area+=ar;f.n.x+=N[3*t]*ar;f.n.y+=N[3*t+1]*ar;f.n.z+=N[3*t+2]*ar;}
  for(const l of edgeMap(g).values())for(let i=0;i<l.length;i++)for(let j=i+1;j<l.length;j++){const p=fid[l[i]],q=fid[l[j]];if(p!==q){get(p).adj.add(q);get(q).adj.add(p);}}
  return info;}
function isClosed(g){const I=g.index.array,m=new Map();for(let t=0;t<I.length;t+=3)for(let e=0;e<3;e++){const a=I[t+e],b=I[t+(e+1)%3],k=a<b?a+','+b:b+','+a;m.set(k,(m.get(k)||0)+1);}
  // CAD solids often have a handful of open or shared edges where bodies touch; treat those as closed
  let open=0;for(const c of m.values())if(c===1)open++;return m.size>0&&open<=m.size*0.001;}
function triCount(g){return g?(g.index?g.index.count:g.attributes.position.count)/3:0;}

// ---------- samples ----------
function gridSurface(nu,nv,fn){const p=[],idx=[];for(let j=0;j<=nv;j++)for(let i=0;i<=nu;i++)p.push(...fn(i/nu,j/nv));
  for(let j=0;j<nv;j++)for(let i=0;i<nu;i++){const a=j*(nu+1)+i,b=a+1,c=a+nu+1,d=c+1;idx.push(a,b,d,a,d,c);}
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(p,3));g.setIndex(idx);return g;}
const grilleFn=(u,v)=>{const x=(u-.5)*600,y=(v-.5)*240,z=70*(1-((u-.5)*2)**2)-22*((v-.5)*2)**2+0.12*y;return[x,y,z];};
// a closed plate: top grid, bottom grid offset down, side walls
function thickPlate(fn,nu,nv,t){const top=gridSurface(nu,nv,fn),bot=gridSurface(nu,nv,(u,v)=>{const q=fn(u,v);return[q[0],q[1],q[2]-t];});
  const tp=top.attributes.position.array,bp=bot.attributes.position.array,n=tp.length/3,pos=[...tp,...bp],idx=[...top.index.array];
  const bi=bot.index.array;for(let i=0;i<bi.length;i+=3)idx.push(bi[i]+n,bi[i+2]+n,bi[i+1]+n);
  const ring=[];for(let i=0;i<=nu;i++)ring.push(i);for(let j=1;j<=nv;j++)ring.push(j*(nu+1)+nu);for(let i=nu-1;i>=0;i--)ring.push(nv*(nu+1)+i);for(let j=nv-1;j>=1;j--)ring.push(j*(nu+1));
  for(let k=0;k<ring.length;k++){const a=ring[k],b=ring[(k+1)%ring.length];idx.push(a,a+n,b,b,a+n,b+n);}
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(pos,3));g.setIndex(idx);return g;}
function dome(){const R=200,amax=Math.PI/3,nr=48,na=144,p=[[0,0,R]],idx=[];
  for(let r=1;r<=nr;r++)for(let a=0;a<na;a++){const t=amax*r/nr,ph=a/na*2*Math.PI;p.push([R*Math.sin(t)*Math.cos(ph),R*Math.sin(t)*Math.sin(ph),R*Math.cos(t)]);}
  for(let a=0;a<na;a++)idx.push(0,1+a,1+(a+1)%na);
  for(let r=1;r<nr;r++)for(let a=0;a<na;a++){const i=1+(r-1)*na+a,j=1+(r-1)*na+(a+1)%na,k=i+na,l=j+na;idx.push(i,k,l,i,l,j);}
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(p.flat(),3));g.setIndex(idx);return g;}
const SAMPLES=[
  ['grille','Grille surface','Curved open surface',()=>gridSurface(150,60,grilleFn),'M4 22 Q22 8 40 22'],
  ['plate','Curved plate','Closed solid, 4 mm thick',()=>thickPlate(grilleFn,150,60,4),'M4 20 Q22 6 40 20 L40 25 Q22 11 4 25Z'],
  ['dome','Dome','Open spherical cap',dome,'M6 26 A18 18 0 0 1 38 26'],
];
function loadSample(id){const s=SAMPLES.find(q=>q[0]===id);A.sample=id;raw=null;setModel(s[3](),s[1],s[2]);}

// ---------- model ----------
function setModel(g,name,info,fid){
  g=cleanGeometry(g,fid);g.computeBoundingBox();const c=g.boundingBox.getCenter(new THREE.Vector3());g.translate(-c.x,-c.y,-c.z);
  if(isClosed(g))orientFaces(g);   // normals point out of the solid
  A.orig=g;A.geo=g;A.history=[];A.name=name;A.info=info||'';A.closed=isClosed(g);A.atts=[];A.sel=-1;A.selP=-1;A.applied=false;A.viewFrame=null;
  A.finfo=faceInfo(g);A.faces=defaultFaces();
  // scale the pattern to the starting face, so a small part still gets a readable number of openings
  const fa=[...A.faces].reduce((t,id)=>t+A.finfo.get(id).area,0);if(fa>0){S.s=clamp(Math.round(Math.sqrt(fa)/8*2)/2,4,12);if(typeof syncFields==='function')syncFields();}
  // one point attractor in the middle of the facing area to start with
  F=null;computeFrame();const mid=centerHit();if(mid)A.atts.push({t:'point',w:mid});
  // influence radius in proportion to the patterned area, so the attractor visibly grades the pattern on small and large parts alike
  if(F.any){S.R=clamp(Math.round(0.5*Math.hypot(F.W-2*PAD,F.H-2*PAD)),10,800);syncFields();}
  showGeometry();frameCamera();changed(true);
}
function applyImport(){if(!raw)return;const g=raw.g.clone(),k=raw.unitsFixed?1:A.units;
  if(A.up==='y')g.applyMatrix4(new THREE.Matrix4().makeRotationX(Math.PI/2));if(k!==1)g.scale(k,k,k);setModel(g,raw.name,raw.info,raw.fid);}
// start with the face that covers the most of the model seen from straight above (a grid of rays looking down)
function defaultFaces(){
  const g=A.geo,fid=g.userData.fid;g.computeBoundsTree({indirect:true});   // indirect keeps the index (and so the face ids) in order
  g.computeBoundingBox();const bb=g.boundingBox,n=36,hits=new Map();
  const m=new THREE.Mesh(g,new THREE.MeshBasicMaterial({side:THREE.DoubleSide})),ray=new THREE.Raycaster(),down=new THREE.Vector3(0,0,-1),o=new THREE.Vector3();ray.firstHitOnly=true;
  for(let i=0;i<n;i++)for(let j=0;j<n;j++){o.set(bb.min.x+(i+.5)/n*(bb.max.x-bb.min.x),bb.min.y+(j+.5)/n*(bb.max.y-bb.min.y),bb.max.z+10);ray.set(o,down);
    const h=ray.intersectObject(m)[0];if(h){const id=fid[h.faceIndex];hits.set(id,(hits.get(id)||0)+1);}}
  g.disposeBoundsTree();let best=null,bv=0;for(const[id,v]of hits)if(v>bv){bv=v;best=id;}
  if(best===null)for(const[id,f]of A.finfo){const v=Math.abs(f.n.z);if(v>bv){bv=v;best=id;}}
  return new Set(best===null?[]:[best]);}
// faces stay one connected patch: a face can be added only next to the selection, and removed only if the rest stays connected
function connected(set){if(set.size<2)return true;const ids=[...set],seen=new Set([ids[0]]),st=[ids[0]];while(st.length){const u=st.pop();for(const w of A.finfo.get(u).adj)if(set.has(w)&&!seen.has(w)){seen.add(w);st.push(w);}}return seen.size===set.size;}
let faceMsg='';
function pickFace(id,add){
  if(!add){A.faces=new Set([id]);faceMsg='';}
  else{const n=new Set(A.faces);if(n.has(id))n.delete(id);else n.add(id);
    if(!n.size){faceMsg='At least one face stays selected.';}else if(!connected(n)){faceMsg='Faces must touch each other. Pick a face that shares an edge with the selection.';}else{A.faces=n;faceMsg='';}}
  A.applied=false;changed(true);}

// ---------- mapping ----------
// Two ways to put the flat pattern sheet on the model:
//  wrap: the selected faces are unrolled with a discrete exponential map (geodesic polar coordinates
//        grown outward from a seed vertex), so spacing is measured along the surface;
//  top/front/right/view: a straight planar projection along a fixed direction.
// Either way F.vs holds sheet coordinates per vertex and F.reg marks the triangles that carry the pattern.
function baseFrame(){
  if(A.dir==='view'&&A.viewFrame)return A.viewFrame;
  if(A.dir==='front')return{d:v3([0,1,0]),U:v3([1,0,0]),V:v3([0,0,1])};
  if(A.dir==='right')return{d:v3([-1,0,0]),U:v3([0,1,0]),V:v3([0,0,1])};
  return{d:v3([0,0,-1]),U:v3([1,0,0]),V:v3([0,1,0])};
}
function captureView(){const d=new THREE.Vector3();camera.getWorldDirection(d);
  A.viewFrame={d,U:new THREE.Vector3().setFromMatrixColumn(camera.matrixWorld,0).normalize(),V:new THREE.Vector3().setFromMatrixColumn(camera.matrixWorld,1).normalize()};}
function triNormals(g){const P=g.attributes.position,I=g.index.array,N=new Float32Array(I.length),a=new THREE.Vector3(),b=new THREE.Vector3(),c=new THREE.Vector3();
  for(let t=0;t<I.length;t+=3){a.fromBufferAttribute(P,I[t]);b.fromBufferAttribute(P,I[t+1]);c.fromBufferAttribute(P,I[t+2]);b.sub(a);c.sub(a);b.cross(c).normalize();N[t]=b.x;N[t+1]=b.y;N[t+2]=b.z;}return N;}
// a triangle "faces" the projection when its normal points back toward the projector (either side for open surfaces)
function facingOf(g,d){const N=triNormals(g),n=N.length/3,o=new Uint8Array(n),fid=g.userData.fid,sel=A.faces&&A.faces.size?A.faces:null;
  for(let t=0;t<n;t++){const dot=-(N[3*t]*d.x+N[3*t+1]*d.y+N[3*t+2]*d.z);o[t]=(A.closed?dot:Math.abs(dot))>FACING&&(!sel||sel.has(fid[t]))?1:0;}return o;}
let wrapCache=null;
function wrapMap(g){
  const key=[...A.faces].sort((a,b)=>a-b).join(',');if(wrapCache&&wrapCache.g===g&&wrapCache.key===key)return wrapCache;
  const P=g.attributes.position,I=g.index.array,nt=I.length/3,nv=P.count,fid=g.userData.fid,N=triNormals(g),reg=new Uint8Array(nt),sg=new Int8Array(nt),em=edgeMap(g);
  for(let t=0;t<nt;t++)reg[t]=A.faces.has(fid[t])?1:0;
  // make the region's triangles agree on which side is up (open surfaces can mix them)
  const dirIn=(u,a,b)=>{for(let e=0;e<3;e++)if(I[3*u+e]===a&&I[3*u+(e+1)%3]===b)return true;return false;};
  for(let t0=0;t0<nt;t0++){if(!reg[t0]||sg[t0])continue;sg[t0]=1;const st=[t0];
    while(st.length){const t=st.pop();for(let e=0;e<3;e++){const a=I[3*t+e],b=I[3*t+(e+1)%3],l=em.get(a<b?a*4294967296+b:b*4294967296+a);
      for(const u of l)if(u!==t&&reg[u]&&!sg[u]){sg[u]=dirIn(u,a,b)?-sg[t]:sg[t];st.push(u);}}}}
  // area-weighted vertex normals and the region's centroid
  const VN=new Float32Array(nv*3),q=new THREE.Vector3(),r=new THREE.Vector3(),w=new THREE.Vector3(),cen=new THREE.Vector3();let at=0,flip=0;
  for(let t=0;t<nt;t++){if(!reg[t])continue;q.fromBufferAttribute(P,I[3*t]);r.fromBufferAttribute(P,I[3*t+1]);w.fromBufferAttribute(P,I[3*t+2]);
    const ar=r.clone().sub(q).cross(w.clone().sub(q)).length()/2;cen.addScaledVector(q.add(r).add(w),ar/3);at+=ar;
    for(let e=0;e<3;e++){const i=I[3*t+e];for(let k=0;k<3;k++)VN[3*i+k]+=sg[t]*N[3*t+k]*ar;}flip+=sg[t]*N[3*t+2]*ar;}
  // keep the side that faces the viewer for closed solids (outward), and the upward side for open surfaces
  const s0=A.closed?1:(flip<0?-1:1);if(s0<0){for(let i=0;i<VN.length;i++)VN[i]=-VN[i];for(let t=0;t<nt;t++)sg[t]=-sg[t];}
  if(A.closed)for(let t=0;t<nt;t++)if(reg[t])sg[t]=1;
  for(let i=0;i<nv;i++){const l=Math.hypot(VN[3*i],VN[3*i+1],VN[3*i+2]);if(l){VN[3*i]/=l;VN[3*i+1]/=l;VN[3*i+2]/=l;}}
  if(!at)return wrapCache={g,key,reg,sg,VN,u:new Float32Array(nv*2).fill(NaN),seed:-1};
  cen.multiplyScalar(1/at);
  // vertex adjacency inside the region
  const deg=new Int32Array(nv+1);for(let t=0;t<nt;t++)if(reg[t])for(let e=0;e<3;e++){deg[I[3*t+e]+1]+=2;}
  for(let i=0;i<nv;i++)deg[i+1]+=deg[i];const adj=new Int32Array(deg[nv]),fill=deg.slice(0,nv);
  for(let t=0;t<nt;t++)if(reg[t])for(let e=0;e<3;e++){const a=I[3*t+e],b=I[3*t+(e+1)%3];adj[fill[a]++]=b;adj[fill[b]++]=a;}
  let seed=-1,bd=Infinity;for(let i=0;i<nv;i++)if(deg[i+1]>deg[i]){q.fromBufferAttribute(P,i);const d=q.distanceToSquared(cen);if(d<bd){bd=d;seed=i;}}
  // seed frame: x along world X (or Y when the surface faces along X), y = n × x
  const n0=new THREE.Vector3(VN[3*seed],VN[3*seed+1],VN[3*seed+2]),e1=new THREE.Vector3(Math.abs(n0.x)>0.9?0:1,Math.abs(n0.x)>0.9?1:0,0);
  e1.addScaledVector(n0,-e1.dot(n0)).normalize();
  // Dijkstra over edge lengths; each vertex gets the average of its finished neighbours' predictions
  const u=new Float32Array(nv*2).fill(NaN),E1=new Float32Array(nv*3),dist=new Float64Array(nv).fill(Infinity),done=new Uint8Array(nv);
  const heap=[];const push=(d,v)=>{heap.push([d,v]);let i=heap.length-1;while(i){const p=(i-1)>>1;if(heap[p][0]<=heap[i][0])break;[heap[p],heap[i]]=[heap[i],heap[p]];i=p;}};
  const pop=()=>{const top=heap[0],last=heap.pop();if(heap.length){heap[0]=last;let i=0;for(;;){const l=2*i+1,r2=l+1;let m=i;if(l<heap.length&&heap[l][0]<heap[m][0])m=l;if(r2<heap.length&&heap[r2][0]<heap[m][0])m=r2;if(m===i)break;[heap[m],heap[i]]=[heap[i],heap[m]];i=m;}}return top;};
  dist[seed]=0;push(0,seed);const pv=new THREE.Vector3(),np=new THREE.Vector3(),ep=new THREE.Vector3(),fp=new THREE.Vector3(),dv=new THREE.Vector3();
  while(heap.length){const[d,v]=pop();if(done[v]||d>dist[v])continue;done[v]=1;q.fromBufferAttribute(P,v);const nv3=[VN[3*v],VN[3*v+1],VN[3*v+2]];
    if(v===seed){u[2*v]=0;u[2*v+1]=0;E1[3*v]=e1.x;E1[3*v+1]=e1.y;E1[3*v+2]=e1.z;}
    else{let sx=0,sy=0,sw=0,par=-1,pd=Infinity;
      for(let k=deg[v];k<deg[v+1];k++){const p=adj[k];if(!done[p]||p===v)continue;pv.fromBufferAttribute(P,p);dv.subVectors(q,pv);const L=dv.length();if(!L)continue;
        np.set(VN[3*p],VN[3*p+1],VN[3*p+2]);ep.set(E1[3*p],E1[3*p+1],E1[3*p+2]);fp.crossVectors(np,ep);
        dv.addScaledVector(np,-dv.dot(np));const lt=dv.length()||1;dv.multiplyScalar(L/lt);const wt=1/L;
        sx+=wt*(u[2*p]+dv.dot(ep));sy+=wt*(u[2*p+1]+dv.dot(fp));sw+=wt;if(dist[p]+L<pd){pd=dist[p]+L;par=p;}}
      u[2*v]=sx/sw;u[2*v+1]=sy/sw;
      ep.set(E1[3*par],E1[3*par+1],E1[3*par+2]);np.set(nv3[0],nv3[1],nv3[2]);ep.addScaledVector(np,-ep.dot(np));if(ep.lengthSq()<1e-12)ep.set(E1[3*par],E1[3*par+1],E1[3*par+2]);ep.normalize();
      E1[3*v]=ep.x;E1[3*v+1]=ep.y;E1[3*v+2]=ep.z;}
    for(let k=deg[v];k<deg[v+1];k++){const p=adj[k];if(done[p])continue;pv.fromBufferAttribute(P,p);const nd=dist[v]+pv.distanceTo(q);if(nd<dist[p]){dist[p]=nd;push(nd,p);}}}
  return wrapCache={g,key,reg,sg,VN,u,seed,n0,e1};
}
function computeFrame(){
  const g=A.geo;if(!g)return;const P=g.attributes.position,I=g.index.array,nt=I.length/3,nv=P.count,r=A.rot*Math.PI/180,cr=Math.cos(r),sr=Math.sin(r);
  const raw=new Float32Array(nv*2).fill(NaN),q=new THREE.Vector3();let reg,sg,VN=null,d,U,V,W=null;
  if(A.dir==='wrap'){W=wrapMap(g);reg=W.reg;sg=W.sg;VN=W.VN;
    for(let i=0;i<nv;i++){const x=W.u[2*i],y=W.u[2*i+1];if(x===x){raw[2*i]=x*cr+y*sr;raw[2*i+1]=y*cr-x*sr;}}
    const n0=W.seed>=0?W.n0:v3([0,0,1]),e1=W.seed>=0?W.e1:v3([1,0,0]),e2=new THREE.Vector3().crossVectors(n0,e1);
    d=n0.clone().negate();U=e1.clone().multiplyScalar(cr).addScaledVector(e2,sr);V=e2.clone().multiplyScalar(cr).addScaledVector(e1,-sr);}
  else{const B=baseFrame();U=B.U.clone().multiplyScalar(cr).addScaledVector(B.V,sr);V=B.V.clone().multiplyScalar(cr).addScaledVector(B.U,-sr);d=B.d.clone();
    reg=facingOf(g,d);const N=triNormals(g);sg=new Int8Array(nt);
    for(let t=0;t<nt;t++){const dot=-(N[3*t]*d.x+N[3*t+1]*d.y+N[3*t+2]*d.z);sg[t]=A.closed||dot>=0?1:-1;}
    for(let i=0;i<nv;i++){q.fromBufferAttribute(P,i);raw[2*i]=q.dot(U);raw[2*i+1]=q.dot(V);}}
  let a0=1e9,a1=-1e9,b0=1e9,b1=-1e9,any=false;
  for(let t=0;t<nt;t++)if(reg[t])for(let e=0;e<3;e++){const i=I[3*t+e],a=raw[2*i],b=raw[2*i+1];if(a!==a)continue;a0=Math.min(a0,a);a1=Math.max(a1,a);b0=Math.min(b0,b);b1=Math.max(b1,b);any=true;}
  if(!any){a0=b0=-1;a1=b1=1;}
  const vs=new Float32Array(nv*2);for(let i=0;i<nv;i++){vs[2*i]=raw[2*i]-a0+PAD+A.ox;vs[2*i+1]=b1-raw[2*i+1]+PAD+A.oy;}
  F={d,U,V,a0,b1,W:a1-a0+2*PAD,H:b1-b0+2*PAD,any,reg,sg,vs,VN,wrap:A.dir==='wrap',seed:W?W.seed:-1};
  F.tri=t=>[0,1,2].map(e=>{const i=I[3*t+e];return[vs[2*i],vs[2*i+1]];});
  if(F.wrap){F.toSheet=p=>wrapToSheet(g,p);F.toPlane=null;}
  else{F.toSheet=(p)=>[p.dot(U)-a0+PAD+A.ox,b1-p.dot(V)+PAD+A.oy];F.toPlane=(x,y)=>new THREE.Vector3().addScaledVector(U,x-PAD-A.ox+a0).addScaledVector(V,b1+PAD+A.oy-y);}
  F.mask=buildMask(g);E.setSheet(F.W,F.H);E.setMask(F.mask);
}
// how a triangle's sheet coordinates turn into world directions: dP/dx and dP/dy
function triJacobian(Pw,T){const e1=Pw[1].clone().sub(Pw[0]),e2=Pw[2].clone().sub(Pw[0]),t1x=T[1][0]-T[0][0],t1y=T[1][1]-T[0][1],t2x=T[2][0]-T[0][0],t2y=T[2][1]-T[0][1],det=t1x*t2y-t2x*t1y||1e-12;
  return[e1.clone().multiplyScalar(t2y/det).addScaledVector(e2,-t1y/det),e2.clone().multiplyScalar(t1x/det).addScaledVector(e1,-t2x/det)];}
function triWorld(g,t){const P=g.attributes.position,I=g.index.array;return[0,1,2].map(e=>new THREE.Vector3().fromBufferAttribute(P,I[3*t+e]));}
// world point -> sheet in wrap mode: nearest point on the wrapped faces, then a tangent-plane step for points just off them
function wrapToSheet(g,p){
  const W=wrapCache;if(!W.rg){const I=g.index.array,P=g.attributes.position,list=[],pos=[];for(let t=0;t<W.reg.length;t++)if(W.reg[t]){list.push(t);for(let e=0;e<3;e++){const i=I[3*t+e];pos.push(P.getX(i),P.getY(i),P.getZ(i));}}
    const rg=new THREE.BufferGeometry();rg.setAttribute('position',new THREE.Float32BufferAttribute(pos,3));if(list.length)rg.computeBoundsTree({indirect:true});W.rg=rg;W.list=list;}
  if(!W.list.length)return[F.W/2,F.H/2];
  const h=W.rg.boundsTree.closestPointToPoint(p,{});const t=W.list[h.faceIndex],Pw=triWorld(g,t),T=F.tri(t);
  const bc=new THREE.Triangle(Pw[0],Pw[1],Pw[2]).getBarycoord(h.point,new THREE.Vector3());let x=bc.x*T[0][0]+bc.y*T[1][0]+bc.z*T[2][0],y=bc.x*T[0][1]+bc.y*T[1][1]+bc.z*T[2][1];
  const dl=p.clone().sub(h.point);if(dl.lengthSq()>1e-12){const[jx,jy]=triJacobian(Pw,T),a=jx.dot(jx),b=jx.dot(jy),c=jy.dot(jy),det=a*c-b*b;if(Math.abs(det)>1e-12){const r1=jx.dot(dl),r2=jy.dot(dl);x+=(c*r1-b*r2)/det;y+=(a*r2-b*r1)/det;}}
  return[x,y];}
// sheet -> surface point, normal and local sheet directions (a grid over the patterned triangles in sheet space)
function unmap(x,y){
  const g=A.geo;if(!F.grid){const cell=Math.max(F.W,F.H)/160,nx=Math.ceil(F.W/cell)+1,ny=Math.ceil(F.H/cell)+1,cells=new Map();
    for(let t=0;t<F.reg.length;t++){if(!F.reg[t])continue;const T=F.tri(t),x0=Math.floor(Math.min(T[0][0],T[1][0],T[2][0])/cell),x1=Math.floor(Math.max(T[0][0],T[1][0],T[2][0])/cell),y0=Math.floor(Math.min(T[0][1],T[1][1],T[2][1])/cell),y1=Math.floor(Math.max(T[0][1],T[1][1],T[2][1])/cell);
      for(let i=x0;i<=x1;i++)for(let j=y0;j<=y1;j++){const k=i*100003+j;const l=cells.get(k);if(l)l.push(t);else cells.set(k,[t]);}}
    F.grid={cell,cells};}
  const l=F.grid.cells.get(Math.floor(x/F.grid.cell)*100003+Math.floor(y/F.grid.cell));if(!l)return null;
  for(const t of l){const T=F.tri(t),den=(T[1][1]-T[2][1])*(T[0][0]-T[2][0])+(T[2][0]-T[1][0])*(T[0][1]-T[2][1]);if(Math.abs(den)<1e-14)continue;
    const l0=((T[1][1]-T[2][1])*(x-T[2][0])+(T[2][0]-T[1][0])*(y-T[2][1]))/den,l1=((T[2][1]-T[0][1])*(x-T[2][0])+(T[0][0]-T[2][0])*(y-T[2][1]))/den,l2=1-l0-l1;
    if(l0<-1e-6||l1<-1e-6||l2<-1e-6)continue;const Pw=triWorld(g,t),p=Pw[0].clone().multiplyScalar(l0).addScaledVector(Pw[1],l1).addScaledVector(Pw[2],l2);
    const N=Pw[1].clone().sub(Pw[0]).cross(Pw[2].clone().sub(Pw[0])).normalize().multiplyScalar(F.sg[t]||1);
    return{p,n:N,J:triJacobian(Pw,T),t};}
  return null;}
// rasterise the facing triangles onto the sheet, then a distance transform gives "mm to the footprint edge"
function buildMask(g){
  const res=Math.max(0.25,Math.max(F.W,F.H)/1400),nx=Math.ceil(F.W/res)+1,ny=Math.ceil(F.H/res)+1,M=new Uint8Array(nx*ny);
  const fac=F.reg;
  for(let t=0;t<fac.length;t++){if(!fac[t])continue;const T=F.tri(t);
    const x0=Math.max(0,Math.floor(Math.min(T[0][0],T[1][0],T[2][0])/res)),x1=Math.min(nx-1,Math.ceil(Math.max(T[0][0],T[1][0],T[2][0])/res));
    const y0=Math.max(0,Math.floor(Math.min(T[0][1],T[1][1],T[2][1])/res)),y1=Math.min(ny-1,Math.ceil(Math.max(T[0][1],T[1][1],T[2][1])/res));
    const[ax,ay]=T[0],[bx,by]=T[1],[cx,cy]=T[2],den=(by-cy)*(ax-cx)+(cx-bx)*(ay-cy);if(Math.abs(den)<1e-12)continue;
    for(let j=y0;j<=y1;j++)for(let i=x0;i<=x1;i++){const px=(i+.5)*res,py=(j+.5)*res,l0=((by-cy)*(px-cx)+(cx-bx)*(py-cy))/den,l1=((cy-ay)*(px-cx)+(ax-cx)*(py-cy))/den;if(l0>=-1e-6&&l1>=-1e-6&&l0+l1<=1+1e-6)M[j*nx+i]=1;}}
  // chamfer distance (3-4) to the nearest outside cell
  const D=new Float32Array(nx*ny),BIG=1e9;for(let k=0;k<D.length;k++)D[k]=M[k]?BIG:0;
  for(let j=0;j<ny;j++)for(let i=0;i<nx;i++){const k=j*nx+i;if(!D[k])continue;let v=D[k];
    v=Math.min(v,i>0?D[k-1]+3:3,j>0?D[k-nx]+3:3,i>0&&j>0?D[k-nx-1]+4:4,i<nx-1&&j>0?D[k-nx+1]+4:4);D[k]=v;}
  for(let j=ny-1;j>=0;j--)for(let i=nx-1;i>=0;i--){const k=j*nx+i;if(!D[k])continue;let v=D[k];
    v=Math.min(v,i<nx-1?D[k+1]+3:3,j<ny-1?D[k+nx]+3:3,i<nx-1&&j<ny-1?D[k+nx+1]+4:4,i>0&&j<ny-1?D[k+nx-1]+4:4);D[k]=v;}
  for(let k=0;k<D.length;k++)D[k]=D[k]/3*res;
  return{res,nx,ny,d:D};
}
function centerHit(){if(!F||!F.any)return null;if(F.wrap)return F.seed>=0?new THREE.Vector3().fromBufferAttribute(A.geo.attributes.position,F.seed).toArray():null;const ray=new THREE.Raycaster(),o=F.toPlane(F.W/2,F.H/2).addScaledVector(F.d,-1e5);ray.set(o,F.d);
  const m=new THREE.Mesh(A.geo,new THREE.MeshBasicMaterial({side:THREE.DoubleSide}));const h=ray.intersectObject(m)[0];return h?h.point.toArray():null;}

// ---------- pattern ----------
function syncAttractors(){
  S.atts=A.atts.map(at=>at.t==='point'?{t:'point',a:F.toSheet(v3(at.w))}:{t:'line',pts:at.pts.map(q=>({p:F.toSheet(v3(q.w)),sm:q.sm}))}).filter(at=>at.t==='point'||at.pts.length>=2);
}
let raf=0,needFrame=false;
function changed(frame){if(frame)needFrame=true;if(!raf)raf=requestAnimationFrame(()=>{raf=0;if(needFrame){computeFrame();needFrame=false;}rebuildPattern();});}
function rebuildPattern(){if(!F)return;E.setSheet(F.W,F.H);E.setMask(F.mask);syncAttractors();E.rebuild();paint();uvs();refresh();}
// texture: the engine's own 2D drawing of the sheet, then attractors on top
function paint(){
  const k=Math.min(8,4096/Math.max(F.W,F.H)),c=tex.image,w=Math.ceil(F.W*k),h=Math.ceil(F.H*k);
  if(c.width!==w||c.height!==h){c.width=w;c.height=h;tex.dispose();}   // GPU texture storage is fixed-size, so a new size needs a fresh upload
  const g=c.getContext('2d');
  const base=css('--model')||'#c9ced6',P=css('--primary');
  const saved=E.built().shapes;if(A.applied)E.built().shapes=[];
  E.renderScene(g,k,{metal:base,sheet:base,hole:css('--hole-3d')||'#22252b',field:S.showField,fieldColor:P,outlineColor:'rgba(0,0,0,0)'});
  if(A.applied)E.built().shapes=saved;
  g.lineCap='round';g.lineJoin='round';
  const all=S.atts.slice();if(A.pending&&A.pending.length)all.push({t:'line',pts:A.pending.map(w=>({p:F.toSheet(v3(w)),sm:false})),draft:true});
  all.forEach((at,i)=>{const on=i===A.sel;g.strokeStyle=P;g.fillStyle=P;
    if(at.t==='point'){g.beginPath();g.arc(at.a[0]*k,at.a[1]*k,Math.max(3,F.W*k/300),0,7);g.fill();}
    else{const pts=E.openCurve(at.pts);g.lineWidth=Math.max(2,F.W*k/(on?260:400));g.setLineDash(at.draft?[8,6]:[]);g.beginPath();pts.forEach((q,j)=>g[j?'lineTo':'moveTo'](q[0]*k,q[1]*k));g.stroke();g.setLineDash([]);}});
  tex.needsUpdate=true;handlesUpdate();
}
// each display vertex gets its sheet position as UV; faces that don't face the projector get a corner texel (plain)
function uvs(){const g=mesh.geometry;if(!g.attributes.position)return;const P=g.attributes.position,n=P.count,uv=new Float32Array(n*2),fac=F.reg,I=A.geo.index.array;
  for(let t=0;t<n/3;t++)for(let e=0;e<3;e++){const i=3*t+e,v=I[i];if(fac[t]){uv[2*i]=F.vs[2*v]/F.W;uv[2*i+1]=1-F.vs[2*v+1]/F.H;}else{uv[2*i]=0.001;uv[2*i+1]=0.999;}}
  g.setAttribute('uv',new THREE.BufferAttribute(uv,2));
  const col=new Float32Array(n*3),fid=A.geo.userData.fid,dim=isDark()?0.55:0.7;
  for(let t=0;t<n/3;t++){const on=A.faces.has(fid[t]),v=on?1:dim,tint=on&&!fac[t]?0.93:1;for(let e=0;e<3;e++){const i=3*(3*t+e);col[i]=v*tint;col[i+1]=v*tint;col[i+2]=v;}}
  g.setAttribute('color',new THREE.BufferAttribute(col,3));}
function showGeometry(){
  const g=BGU.toCreasedNormals(A.geo.toNonIndexed(),30*Math.PI/180);if(mesh.geometry.boundsTree)mesh.geometry.disposeBoundsTree();mesh.geometry.dispose();mesh.geometry=g;g.computeBoundsTree({indirect:true});
  edges.geometry.dispose();edges.geometry=new THREE.EdgesGeometry(A.geo,30);
  if(F)uvs();
}
function frameCamera(view){const b=new THREE.Box3().setFromObject(mesh),c=b.getCenter(new THREE.Vector3()),r=b.getSize(new THREE.Vector3()).length()/2||100;
  // the camera keeps Z up (OrbitControls needs a fixed up); looking straight down gets a tiny tilt
  const d=view==='dir'&&F?F.d.clone().negate().addScaledVector(F.V,-0.002).normalize():new THREE.Vector3(0.55,-0.95,0.75).normalize();
  camera.position.copy(c).addScaledVector(d,r/Math.tan(camera.fov*Math.PI/360)*1.15);camera.near=r/100;camera.far=r*100;camera.updateProjectionMatrix();controls.target.copy(c);controls.update();
  key.position.copy(c).add(new THREE.Vector3(r,-r*1.5,r*2.5));key.target.position.copy(c);fill.position.copy(c).add(new THREE.Vector3(-r*2,r,r*0.5));
  grid.scale.setScalar(r*3);grid.position.set(c.x,c.y,b.min.z-0.01);}

// ---------- handles (attractor control points) ----------
function handleSize(){const b=new THREE.Box3().setFromObject(mesh);return b.getSize(new THREE.Vector3()).length()*0.009||2;}
function handlesUpdate(){
  handles.traverse(o=>{if(o.geometry)o.geometry.dispose();if(o.material)o.material.dispose();});handles.clear();const r=handleSize(),P=new THREE.Color(css('--primary')),W=new THREE.Color('#ffffff');
  const mk=(w,on,ai,pi)=>{const s=new THREE.Mesh(new THREE.SphereGeometry(on?r*1.35:r,20,14),new THREE.MeshBasicMaterial({color:on?P:W,depthTest:false}));s.position.fromArray(w);s.renderOrder=10;s.userData={ai,pi};
    const ring=new THREE.Mesh(new THREE.SphereGeometry((on?r*1.35:r)*1.25,20,14),new THREE.MeshBasicMaterial({color:P,side:THREE.BackSide,depthTest:false}));ring.renderOrder=9;s.add(ring);handles.add(s);};
  A.atts.forEach((at,i)=>{if(at.t==='point')mk(at.w,i===A.sel,i,-1);else at.pts.forEach((q,j)=>mk(q.w,i===A.sel&&(A.selP<0||A.selP===j),i,j));});
  if(A.pending)A.pending.forEach((w,j)=>mk(w,true,-1,j));
}

// ---------- pointer interaction ----------
const ray=new THREE.Raycaster();
function setRay(e){const r=canvas.getBoundingClientRect();ray.setFromCamera(new THREE.Vector2((e.clientX-r.left)/r.width*2-1,-(e.clientY-r.top)/r.height*2+1),camera);}
function hitModel(e){setRay(e);const h=ray.intersectObject(mesh)[0];return h?h.point.toArray():null;}
let drag=null,down=null;
canvas.addEventListener('pointerdown',e=>{
  if(e.button!==0||A.busy)return;down={x:e.clientX,y:e.clientY};
  if(A.tool==='point'||A.tool==='line'){e.stopImmediatePropagation();const w=hitModel(e);if(!w)return;
    if(A.tool==='point'){A.atts.push({t:'point',w});A.sel=A.atts.length-1;A.selP=-1;setTool('select');changed();return;}
    const d=A.pending||(A.pending=[]),last=d[d.length-1];if(last&&v3(last).distanceTo(v3(w))<handleSize()*1.5){finishLine();return;}d.push(w);paint();hint();return;}
  setRay(e);const h=ray.intersectObjects(handles.children,false)[0];
  if(h&&h.object.userData.ai>=0){e.stopImmediatePropagation();const{ai,pi}=h.object.userData;A.sel=ai;A.selP=pi;drag={ai,pi};canvas.setPointerCapture(e.pointerId);controls.enabled=false;A.applied=false;refresh();paint();}
},{capture:true});
canvas.addEventListener('pointermove',e=>{if(!drag)return;const w=hitModel(e);if(!w)return;const at=A.atts[drag.ai];if(at.t==='point')at.w=w;else at.pts[drag.pi].w=w;changed();});
canvas.addEventListener('pointerup',e=>{
  if(drag){drag=null;controls.enabled=true;return;}
  if(down&&Math.hypot(e.clientX-down.x,e.clientY-down.y)<4&&A.tool==='select'){setRay(e);const h=ray.intersectObject(mesh)[0];A.sel=-1;A.selP=-1;
    if(h)pickFace(A.geo.userData.fid[h.faceIndex],e.shiftKey||e.metaKey||e.ctrlKey);else{refresh();paint();}}down=null;});
canvas.addEventListener('dblclick',e=>{if(A.tool==='line'){finishLine();return;}
  // double-click a line handle: smooth / sharp point
  setRay(e);const h=ray.intersectObjects(handles.children,false)[0];if(h&&h.object.userData.pi>=0){const at=A.atts[h.object.userData.ai],q=at.pts[h.object.userData.pi];q.sm=!q.sm;changed();}});
function finishLine(){const d=A.pending;A.pending=null;if(d&&d.length>=2){A.atts.push({t:'line',pts:d.map(w=>({w,sm:false}))});A.sel=A.atts.length-1;A.selP=-1;}setTool('select');changed();}
function setTool(t){if(A.pending&&t!=='line')A.pending=null;A.tool=t;if(t==='line'&&!A.pending)A.pending=[];canvas.style.cursor=t==='select'?'grab':'crosshair';refresh();paint();}
function removeSelected(){const at=A.atts[A.sel];if(!at)return;
  if(at.t==='line'&&A.selP>=0&&at.pts.length>2){at.pts.splice(A.selP,1);A.selP=-1;}else{A.atts.splice(A.sel,1);A.sel=-1;A.selP=-1;}A.applied=false;changed();}
function toggleCurve(){const at=A.atts[A.sel];if(!at||at.t!=='line')return;
  if(A.selP>0&&A.selP<at.pts.length-1){at.pts[A.selP].sm=!at.pts[A.selP].sm;}
  else{const to=!at.pts.some(q=>q.sm);if(to&&at.pts.length===2){const m=centerOn([at.pts[0].w,at.pts[1].w]);if(m)at.pts.splice(1,0,{w:m,sm:true});}at.pts.forEach((q,j)=>q.sm=to&&j>0&&j<at.pts.length-1);}
  A.applied=false;changed();}
// a point on the model half-way between two points, nudged sideways so a new curve is visible
function centerOn(ws){const a=v3(ws[0]),b=v3(ws[1]),m=a.clone().add(b).multiplyScalar(.5),side=new THREE.Vector3().crossVectors(b.clone().sub(a),F.d).normalize().multiplyScalar(a.distanceTo(b)*0.2);
  m.add(side);const r=new THREE.Raycaster(m.clone().addScaledVector(F.d,-1e5),F.d);const h=r.intersectObject(mesh)[0];return h?h.point.toArray():null;}

window.addEventListener('keydown',e=>{
  if(/^(INPUT|SELECT|TEXTAREA)$/.test(e.target.tagName))return;const k=e.key.toLowerCase();
  if(k==='escape'){closeMenus();$('help').hidden=true;A.pending=null;setTool('select');return;}
  if(e.metaKey||e.ctrlKey){if(k==='z'){e.preventDefault();undo();}return;}
  if(k==='enter'&&A.tool==='line'){e.preventDefault();finishLine();return;}
  const map={v:'select',p:'point',l:'line'};if(map[k])setTool(map[k]);
  else if(k==='s')toggleCurve();else if(k==='f')frameCamera();
  else if(k==='delete'||k==='backspace'){e.preventDefault();removeSelected();}
});

// ---------- operations ----------
// pattern openings as polygons on the sheet (MultiPolygon geometry for polygon-clipping)
function shapePolys(){const out=[];
  for(const sh of E.built().shapes){let mp;
    if(sh.k==='circ'){const n=clamp(Math.ceil(2*Math.PI*sh.r/0.6),16,96),r=[];for(let i=0;i<n;i++){const a=i/n*2*Math.PI;r.push([sh.x+sh.r*Math.cos(a),sh.y+sh.r*Math.sin(a)]);}mp=[[r]];}
    else if(sh.k==='poly'){mp=[[sh.p.map(q=>[q[0],q[1]])]];}
    else if(sh.k==='line'){const caps=[];for(let i=1;i<sh.p.length;i++)caps.push([[capsule(sh.p[i-1],sh.p[i],sh.w/2)]]);try{mp=PC.union(...caps);}catch(err){continue;}}
    else continue;
    let x0=1e9,y0=1e9,x1=-1e9,y1=-1e9;for(const poly of mp)for(const q of poly[0]){x0=Math.min(x0,q[0]);x1=Math.max(x1,q[0]);y0=Math.min(y0,q[1]);y1=Math.max(y1,q[1]);}
    out.push({mp,x0,y0,x1,y1});}
  return out;}
function capsule(a,b,r){const dx=b[0]-a[0],dy=b[1]-a[1],L=Math.hypot(dx,dy)||1e-9,ang=Math.atan2(dy,dx),o=[],n=10;
  for(let i=0;i<=n;i++){const t=ang-Math.PI/2+i*Math.PI/n;o.push([b[0]+r*Math.cos(t),b[1]+r*Math.sin(t)]);}
  for(let i=0;i<=n;i++){const t=ang+Math.PI/2+i*Math.PI/n;o.push([a[0]+r*Math.cos(t),a[1]+r*Math.sin(t)]);}return o;}
function shapeGrid(polys){const cell=Math.max(S.s*2,10),m=new Map();polys.forEach((p,i)=>{for(let x=Math.floor(p.x0/cell);x<=Math.floor(p.x1/cell);x++)for(let y=Math.floor(p.y0/cell);y<=Math.floor(p.y1/cell);y++){const k=x+','+y;(m.get(k)||m.set(k,[]).get(k)).push(i);}});
  return(x0,y0,x1,y1)=>{const s=new Set();for(let x=Math.floor(x0/cell);x<=Math.floor(x1/cell);x++)for(let y=Math.floor(y0/cell);y<=Math.floor(y1/cell);y++){const l=m.get(x+','+y);if(l)for(const i of l){const p=polys[i];if(p.x1>=x0&&p.x0<=x1&&p.y1>=y0&&p.y0<=y1)s.add(i);}}return[...s];};}
const sarea=r=>{let s=0;for(let i=0,n=r.length;i<n;i++){const a=r[i],b=r[(i+1)%n];s+=a[0]*b[1]-b[0]*a[1];}return s/2;};
const openRing=r=>{const n=r.length;return n>1&&r[0][0]===r[n-1][0]&&r[0][1]===r[n-1][1]?r.slice(0,-1):r.slice();};
const tick=()=>new Promise(r=>requestAnimationFrame(()=>r()));

// Split every facing triangle along the pattern outlines (exact, in sheet space), then drop, raise or sink the pieces inside.
async function clipOp(op,depth,progress){
  const g=A.geo,P=g.attributes.position,I=g.index.array,nt=I.length/3,fac=F.reg,N=triNormals(g),polys=shapePolys(),query=shapeGrid(polys);
  // displacement direction per vertex: averaged from facing triangles only, so sharp edges don't skew it
  const VN=new Float32Array(P.count*3);for(let t=0;t<nt;t++)if(fac[t]){const s=F.sg[t]||1;
    for(let e=0;e<3;e++){const i=I[3*t+e];VN[3*i]+=s*N[3*t];VN[3*i+1]+=s*N[3*t+1];VN[3*i+2]+=s*N[3*t+2];}}
  for(let i=0;i<P.count;i++){const l=Math.hypot(VN[3*i],VN[3*i+1],VN[3*i+2])||1;VN[3*i]/=l;VN[3*i+1]/=l;VN[3*i+2]/=l;}
  const out=[],ofid=[],FID=g.userData.fid;let cur=-1;const push=(a,b,c)=>{out.push(a.x,a.y,a.z,b.x,b.y,b.z,c.x,c.y,c.z);ofid.push(cur);},sgn=op==='emboss'?1:op==='recess'?-1:0;
  const Pw=[new THREE.Vector3(),new THREE.Vector3(),new THREE.Vector3()],Nw=[new THREE.Vector3(),new THREE.Vector3(),new THREE.Vector3()];
  let touched=0,failed=0;
  for(let t=0;t<nt;t++){
    if(t%1500===0){progress(t/nt);await tick();}
    for(let e=0;e<3;e++){const i=I[3*t+e];Pw[e].fromBufferAttribute(P,i);Nw[e].set(VN[3*i],VN[3*i+1],VN[3*i+2]);}cur=FID[t];
    if(!fac[t]){push(Pw[0],Pw[1],Pw[2]);continue;}
    const T=F.tri(t),s0=sarea(T),[Jx,Jy]=triJacobian(Pw,T);
    const cand=Math.abs(s0)<1e-10?[]:query(Math.min(T[0][0],T[1][0],T[2][0]),Math.min(T[0][1],T[1][1],T[2][1]),Math.max(T[0][0],T[1][0],T[2][0]),Math.max(T[0][1],T[1][1],T[2][1]));
    if(!cand.length){push(Pw[0],Pw[1],Pw[2]);continue;}
    const tri=[[s0>0?T:[T[0],T[2],T[1]]]];let outside,inside=[];
    try{outside=PC.difference(tri,...cand.map(i=>polys[i].mp));if(sgn)for(const i of cand)inside.push(...PC.intersection(tri,polys[i].mp));}
    catch(err){failed++;push(Pw[0],Pw[1],Pw[2]);continue;}
    touched++;
    const den=(T[1][1]-T[2][1])*(T[0][0]-T[2][0])+(T[2][0]-T[1][0])*(T[0][1]-T[2][1]);
    const bary=q=>{const l0=((T[1][1]-T[2][1])*(q[0]-T[2][0])+(T[2][0]-T[1][0])*(q[1]-T[2][1]))/den,l1=((T[2][1]-T[0][1])*(q[0]-T[2][0])+(T[0][0]-T[2][0])*(q[1]-T[2][1]))/den;return[l0,l1,1-l0-l1];};
    const lift=(q,off)=>{const l=bary(q),p=new THREE.Vector3();for(let e=0;e<3;e++)p.addScaledVector(Pw[e],l[e]);
      if(off){const n=new THREE.Vector3();for(let e=0;e<3;e++)n.addScaledVector(Nw[e],l[e]);p.addScaledVector(n.normalize(),off);}return p;};
    const emit=(poly,off)=>{const rings=poly.map(openRing),flat=[],holes=[];rings.forEach((r,k)=>{if(k)holes.push(flat.length/2);for(const q of r)flat.push(q[0],q[1]);});
      const tris=EARCUT(flat,holes),pts=[];for(let i=0;i<flat.length;i+=2)pts.push([flat[i],flat[i+1]]);const W=pts.map(q=>lift(q,off));
      for(let i=0;i<tris.length;i+=3){const a=tris[i],b=tris[i+1],c=tris[i+2],s=sarea([pts[a],pts[b],pts[c]]);if(Math.abs(s)<1e-12)continue;
        if((s>0)===(s0>0))push(W[a],W[b],W[c]);else push(W[a],W[c],W[b]);}};
    for(const poly of outside)emit(poly,0);
    if(!sgn)continue;
    for(const poly of inside){emit(poly,sgn*depth);
      // side walls along the pattern outline (edges that aren't on the triangle's own edges)
      poly.forEach((ring,k)=>{let r=openRing(ring);const s=sarea(r);if((k===0&&s<0)||(k>0&&s>0))r=r.reverse();
        for(let i=0;i<r.length;i++){const a=r[i],b=r[(i+1)%r.length],la=bary(a),lb=bary(b);if([0,1,2].some(e=>Math.abs(la[e])<1e-7&&Math.abs(lb[e])<1e-7))continue;
          const A0=lift(a,0),B0=lift(b,0),A1=lift(a,sgn*depth),B1=lift(b,sgn*depth);
          const ex=b[1]-a[1],ey=-(b[0]-a[0]),want=Jx.clone().multiplyScalar(ex).addScaledVector(Jy,ey).multiplyScalar(sgn);
          const n=new THREE.Vector3().subVectors(B0,A0).cross(new THREE.Vector3().subVectors(B1,A0));
          if(n.dot(want)>=0){push(A0,B0,B1);push(A0,B1,A1);}else{push(A0,B1,B0);push(A0,A1,B1);}}});}
  }
  progress(1);
  const res=new THREE.BufferGeometry();res.setAttribute('position',new THREE.Float32BufferAttribute(out,3));
  return{geo:cleanGeometry(res,ofid),touched,failed};
}
// through-cut a closed solid: one prism per opening, along the projection direction, subtracted with CSG
async function csgCut(progress){
  const {Brush,Evaluator,SUBTRACTION}=await import('three-bvh-csg');
  const polys=shapePolys(),g=A.geo;g.computeBoundingBox();const bb=g.boundingBox,cs=[];
  for(const x of[bb.min.x,bb.max.x])for(const y of[bb.min.y,bb.max.y])for(const z of[bb.min.z,bb.max.z])cs.push(new THREE.Vector3(x,y,z).dot(F.d));
  const t0=Math.min(...cs)-5,t1=Math.max(...cs)+5,diag=bb.getSize(new THREE.Vector3()).length(),pos=[];let skipped=0;
  let probe=null;const ray=new THREE.Raycaster();if(F.wrap){g.computeBoundsTree({indirect:true});probe=new THREE.Mesh(g,new THREE.MeshBasicMaterial({side:THREE.DoubleSide}));}
  for(const p of polys)for(const poly of p.mp){let ring=openRing(poly[0]);if(sarea(ring)<0)ring=ring.reverse();if(ring.length<3)continue;
    let lo,hi;
    if(F.wrap){// each outline point lands on the surface; the prism runs along the opening's average normal, out 5 mm and in right through
      const hits=ring.map(q=>unmap(q[0],q[1]));if(hits.some(h=>!h)){skipped++;continue;}
      const n=hits.reduce((m,h)=>m.add(h.n),new THREE.Vector3()).normalize(),c=hits.reduce((m,h)=>m.add(h.p),new THREE.Vector3()).multiplyScalar(1/hits.length);
      // only as deep as the wall: the first surface the inward ray meets, plus a little (short prisms keep CSG fast)
      ray.set(c.clone().addScaledVector(n,1),n.clone().negate());const hh=ray.intersectObject(probe).find(h=>h.distance>1.02);const depth=hh?hh.distance+1:diag;
      lo=hits.map(h=>h.p.clone().addScaledVector(n,-depth));hi=hits.map(h=>h.p.clone().addScaledVector(n,2));}
    else{const base=ring.map(q=>F.toPlane(q[0],q[1]));lo=base.map(b=>b.clone().addScaledVector(F.d,t0));hi=base.map(b=>b.clone().addScaledVector(F.d,t1));}
    const tris=EARCUT(ring.flat()),one=[],add=(a,b,c)=>one.push(a.x,a.y,a.z,b.x,b.y,b.z,c.x,c.y,c.z);
    for(let i=0;i<tris.length;i+=3){add(lo[tris[i]],lo[tris[i+1]],lo[tris[i+2]]);add(hi[tris[i]],hi[tris[i+2]],hi[tris[i+1]]);}
    for(let i=0;i<ring.length;i++){const j=(i+1)%ring.length;add(lo[i],hi[i],hi[j]);add(lo[i],hi[j],lo[j]);}
    // each prism faces outward on its own (signed volume)
    let v=0;for(let i=0;i<one.length;i+=9)v+=one[i]*(one[i+4]*one[i+8]-one[i+5]*one[i+7])-one[i+1]*(one[i+3]*one[i+8]-one[i+5]*one[i+6])+one[i+2]*(one[i+3]*one[i+7]-one[i+4]*one[i+6]);
    if(v<0)for(let i=0;i<one.length;i+=9)for(let k=0;k<3;k++){const t=one[i+3+k];one[i+3+k]=one[i+6+k];one[i+6+k]=t;}
    for(const x of one)pos.push(x);}
  if(probe)g.disposeBoundsTree();
  progress(0.3);await tick();
  let cutter=new THREE.BufferGeometry();cutter.setAttribute('position',new THREE.Float32BufferAttribute(pos,3));
  cutter=BGU.mergeVertices(cutter,1e-6);
  cutter.computeVertexNormals();const model=A.geo.clone();model.computeVertexNormals();
  const ev=new Evaluator();ev.attributes=['position','normal'];ev.useGroups=false;
  const r=ev.evaluate(new Brush(model),new Brush(cutter),SUBTRACTION);progress(0.9);await tick();
  return{geo:cleanGeometry(r.geometry),touched:polys.length,failed:0,skipped};
}
// make every face's normals point out of the solid: shoot a ray from a few of its triangles along the normal
// and count crossings (odd = it starts inside). CAD files often mix orientations between bodies and faces.
function orientFaces(g){const I=g.index.array,P=g.attributes.position,fid=g.userData.fid,N=triNormals(g),tris=new Map();
  for(let t=0;t<fid.length;t++){const l=tris.get(fid[t]);if(l)l.push(t);else tris.set(fid[t],[t]);}
  g.computeBoundsTree({indirect:true});const m=new THREE.Mesh(g,new THREE.MeshBasicMaterial({side:THREE.DoubleSide})),ray=new THREE.Raycaster(),c=new THREE.Vector3(),q=new THREE.Vector3(),n=new THREE.Vector3();
  g.computeBoundingSphere();const eps=g.boundingSphere.radius*1e-5;let flipped=0;
  for(const[id,l]of tris){let inside=0,votes=0;
    for(let k=0;k<Math.min(5,l.length);k++){const t=l[Math.floor((k+.5)/Math.min(5,l.length)*l.length)];c.set(0,0,0);for(let e=0;e<3;e++)c.add(q.fromBufferAttribute(P,I[3*t+e]));c.multiplyScalar(1/3);
      n.set(N[3*t],N[3*t+1],N[3*t+2]);if(!n.lengthSq())continue;ray.set(c.clone().addScaledVector(n,eps),n);
      const hs=ray.intersectObject(m);let cnt=0,last=-1;for(const h of hs){if(h.distance-last>eps*10)cnt++;last=h.distance;}
      votes++;if(cnt%2)inside++;}
    if(votes&&inside*2>votes){flipped++;for(const t of l){const k=I[3*t+1];I[3*t+1]=I[3*t+2];I[3*t+2]=k;}}}
  g.disposeBoundsTree();return flipped;}
async function applyOp(){
  if(A.busy||!A.geo)return;if(!E.built().shapes.length){showErr('There are no openings to apply. Place an attractor closer to the model, raise the influence radius, or lower the minimum hole size.');return;}
  A.busy=true;showErr('');setBusy(true,'Applying…');const pr=$('progress'),bar=pr.firstElementChild;pr.hidden=false;const progress=f=>{bar.style.width=Math.round(f*100)+'%';};
  try{
    let r;
    if(A.op==='cut'&&A.closed){try{r=await csgCut(progress);}catch(err){console.warn('CSG failed',err);r=null;}
      if(!r||!triCount(r.geo)){showErr('The solid could not be cut right through (it may not be watertight), so the openings were cut from the facing side only.');r=await clipOp('cut',0,progress);}}
    else r=await clipOp(A.op,A.depth,progress);
    A.history.push({geo:A.geo,faces:A.faces,finfo:A.finfo});A.geo=r.geo;A.closed=isClosed(A.geo);A.finfo=faceInfo(A.geo);
    if(![...A.faces].every(id=>A.finfo.has(id)))A.faces=defaultFaces();A.applied=true;showGeometry();computeFrame();paint();refresh();
    if(r.skipped)showErr(`${r.skipped} opening${r.skipped>1?'s':''} ran off the selected faces and were left out.`);
    if(r.failed)showErr(`${r.failed} small triangle${r.failed>1?'s':''} could not be split and were left as they were.`);
  }catch(err){console.error(err);showErr('Something went wrong while applying the pattern: '+err.message);}
  finally{A.busy=false;setBusy(false);pr.hidden=true;bar.style.width='0';}
}
function undo(){if(!A.history.length||A.busy)return;const h=A.history.pop();A.geo=h.geo;A.faces=h.faces;A.finfo=h.finfo;A.closed=isClosed(A.geo);A.applied=false;showGeometry();changed(true);}
function resetModel(){if(!A.history.length||A.busy)return;const h=A.history[0];A.history=[];A.geo=h.geo;A.faces=h.faces;A.finfo=h.finfo;A.closed=isClosed(A.geo);A.applied=false;showGeometry();changed(true);}
function showErr(t){$('applyErr').hidden=!t;$('applyErrText').textContent=t;}
function setBusy(on,t){$('busy').hidden=!on;if(t)$('busyText').textContent=t;}

// ---------- import ----------
async function openFile(f){
  const ext=f.name.split('.').pop().toLowerCase(),buf=await f.arrayBuffer();setBusy(true,'Opening '+f.name+'…');showErr('');
  try{let g,fid=null,unitsFixed=false,up='z';
    if(ext==='stl')g=new STLLoader().parse(buf);
    else if(ext==='ply')g=new PLYLoader().parse(buf);
    else if(ext==='obj'){const o=new OBJLoader().parse(new TextDecoder().decode(buf));g=mergeObject(o);up='y';}
    else if(ext==='glb'||ext==='gltf'){const o=await new GLTFLoader().parseAsync(buf,'');g=mergeObject(o.scene);if(g)g.scale(1000,1000,1000);up='y';unitsFixed=true;}   // glTF is always in metres
    else if(ext==='3dm'){({g,fid}=await read3dm(buf));unitsFixed=true;}
    else if(['step','stp','iges','igs','brep'].includes(ext)){({g,fid}=await readOcct(ext,buf));unitsFixed=true;}
    else throw new Error('Unsupported file type .'+ext);
    if(!g||!g.attributes.position||!g.attributes.position.count)throw new Error('No surfaces or meshes were found in the file.');
    A.up=up;$('upAxis').value=up;if(!unitsFixed){A.units=+$('units').value;}
    const n=triCount(g.index?g:g);raw={g,fid,name:f.name,info:`${unitsFixed?'Units from the file':'Units: '+$('units').selectedOptions[0].text}`,unitsFixed};A.sample=null;
    applyImport();if(n>600000)showErr('This model is very dense. Applying a pattern may take a while.');
  }catch(err){console.error(err);showErr('Could not open '+f.name+': '+err.message);}
  finally{setBusy(false);}
}
function mergeObject(o){o.updateMatrixWorld(true);const gs=[];o.traverse(m=>{if(m.isMesh&&m.geometry.attributes.position){const g=m.geometry.clone();g.applyMatrix4(m.matrixWorld);const p=new THREE.BufferGeometry();p.setAttribute('position',(g.index?g.toNonIndexed():g).attributes.position);gs.push(p);}});
  return gs.length?BGU.mergeGeometries(gs):null;}
let rhinoP=null;
function rhino(){return rhinoP||(rhinoP=import(CDN+'rhino3dm@8.17.0/rhino3dm.module.min.js').then(m=>m.default({locateFile:f=>CDN+'rhino3dm@8.17.0/'+f})));}
async function read3dm(buf){
  const rh=await rhino(),file=rh.File3dm.fromByteArray(new Uint8Array(buf));if(!file)throw new Error('This is not a readable Rhino file.');
  const us=file.settings().modelUnitSystem,U=rh.UnitSystem,k=us===U.Centimeters?10:us===U.Meters?1000:us===U.Inches?25.4:us===U.Feet?304.8:us===U.Micrometers?0.001:1;
  const loader=new THREE.BufferGeometryLoader(),gs=[],fid=[];let breps=0,next=0;const objs=file.objects();
  // each Brep face keeps its own id; plain meshes get -1 and are split at creases later
  const addMesh=(m,face)=>{if(!m)return;const g=loader.parse(m.toThreejsJSON());const p=new THREE.BufferGeometry();p.setAttribute('position',(g.index?g.toNonIndexed():g).attributes.position);gs.push(p);
    const id=face?next++:-1;for(let i=0;i<p.attributes.position.count/3;i++)fid.push(id);};
  for(let i=0;i<objs.count;i++){const geo=objs.get(i).geometry(),T=geo.objectType;
    if(T===rh.ObjectType.Mesh)addMesh(geo,false);
    else if(T===rh.ObjectType.Brep){breps++;const fs=geo.faces();for(let j=0;j<fs.count;j++)addMesh(fs.get(j).getMesh(rh.MeshType.Any),true);}
    else if(T===rh.ObjectType.Extrusion){breps++;addMesh(geo.getMesh(rh.MeshType.Any),false);}
    else if(T===rh.ObjectType.SubD){breps++;try{addMesh(rh.Mesh.createFromSubDControlNet(geo),false);}catch(e){}}}
  if(!gs.length&&breps)throw new Error('The surfaces have no render meshes. In Rhino, shade the model once and save without "Save small", or export as STEP.');
  const g=gs.length?BGU.mergeGeometries(gs):null;if(g&&k!==1)g.scale(k,k,k);return{g,fid};
}
let occtP=null;
function occt(){return occtP||(occtP=new Promise((res,rej)=>{const s=document.createElement('script');s.src=CDN+'occt-import-js@0.0.23/dist/occt-import-js.js';s.onload=()=>window.occtimportjs({locateFile:f=>CDN+'occt-import-js@0.0.23/dist/'+f}).then(res,rej);s.onerror=()=>rej(new Error('Could not load the STEP/IGES reader.'));document.head.appendChild(s);}));}
async function readOcct(ext,buf){
  setBusy(true,'Loading the STEP/IGES reader…');const oc=await occt();setBusy(true,'Meshing the surfaces…');await tick();
  const params={linearUnit:'millimeter',linearDeflectionType:'bounding_box_ratio',linearDeflection:0.0015,angularDeflection:0.25},u8=new Uint8Array(buf);
  const r=ext==='brep'?oc.ReadBrepFile(u8,params):ext.startsWith('i')?oc.ReadIgesFile(u8,params):oc.ReadStepFile(u8,params);
  if(!r||!r.success)throw new Error('The file could not be read.');
  const fid=[];let off=0;
  const gs=r.meshes.map(m=>{const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(m.attributes.position.array,3));g.setIndex(m.index.array);const p=new THREE.BufferGeometry();p.setAttribute('position',g.toNonIndexed().attributes.position);
    // b-rep faces: triangle ranges first..last
    const nt=m.index.array.length/3,f=new Array(nt).fill(-1);m.brep_faces.forEach((bf,k)=>{for(let t=bf.first;t<=bf.last;t++)f[t]=off+k;});off+=m.brep_faces.length;fid.push(...f);return p;});
  return{g:gs.length?BGU.mergeGeometries(gs):null,fid};
}

// ---------- export ----------
function download(name,data,type){const b=data instanceof Blob?data:new Blob([data],{type:type||'application/octet-stream'});const u=URL.createObjectURL(b),a=document.createElement('a');a.href=u;a.download=name;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),2000);}
const baseName=()=>(A.name||'model').replace(/\.[^.]+$/,'').replace(/[^\w-]+/g,'-')+'-'+S.pattern;
function exportMesh(){const g=A.geo.clone();g.computeVertexNormals();return new THREE.Mesh(g,new THREE.MeshStandardMaterial({color:0xc9ced6}));}
async function exportAs(t){
  setBusy(true,'Exporting…');await tick();
  try{
    if(t==='stl')download(baseName()+'.stl',new STLExporter().parse(exportMesh(),{binary:true}));
    else if(t==='obj')download(baseName()+'.obj',new OBJExporter().parse(exportMesh()),'text/plain');
    else if(t==='glb'){const m=exportMesh();m.rotation.x=-Math.PI/2;m.scale.setScalar(0.001);   // glTF is Y-up in metres
      const r=await new GLTFExporter().parseAsync(m,{binary:true});download(baseName()+'.glb',r,'model/gltf-binary');}
    else if(t==='3dm'){const rh=await rhino(),g=A.geo.clone();g.computeVertexNormals();const m=rh.Mesh.createFromThreejsJSON({data:g.toJSON().data});
      const f=new rh.File3dm();f.settings().modelUnitSystem=rh.UnitSystem.Millimeters;f.objects().addMesh(m,null);download(baseName()+'.3dm',f.toByteArray());}
  }catch(err){console.error(err);showErr('Export failed: '+err.message);}
  finally{setBusy(false);}
}

// ---------- panel ----------
function refresh(){
  document.querySelectorAll('.tool[data-tool]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.tool===A.tool));
  const at=A.atts[A.sel];$('smoothTool').disabled=!(at&&at.t==='line');const curved=at&&at.t==='line'&&at.pts.some(q=>q.sm);$('smoothIcon').textContent=curved?'timeline':'line_curve';
  $('delTool').disabled=!at;$('legend').hidden=!S.color;
  $('chipField').setAttribute('aria-pressed',S.showField);$('chipField').querySelector('.ms').hidden=!S.showField;
  $('chipColor').setAttribute('aria-pressed',S.color);$('chipColor').querySelector('.ms').hidden=!S.color;
  $('undoBtn').disabled=!A.history.length;$('resetBtn').disabled=!A.history.length;
  document.querySelectorAll('#dirSeg button').forEach(b=>b.setAttribute('aria-pressed',b.dataset.v===A.dir));
  document.querySelectorAll('#opSeg button').forEach(b=>b.setAttribute('aria-pressed',b.dataset.v===A.op));
  document.querySelectorAll('.sample').forEach(b=>b.setAttribute('aria-pressed',b.dataset.id===A.sample));
  $('depthField').hidden=A.op==='cut';
  $('opNote').textContent=A.op==='cut'?(A.closed?'The model is a closed solid, so the openings are cut right through it along the projection direction.':'The model is an open surface, so the openings become holes in it.')
    :A.op==='emboss'?'The openings are raised by the depth along the surface normal, with side walls.':'The openings are sunk by the depth along the surface normal, with side walls.';
  $('modelName').textContent=A.name;$('modelInfo').textContent=`${A.closed?'Closed solid':'Open surface'} · ${Math.round(triCount(A.geo)).toLocaleString()} triangles${A.info?' · '+A.info:''}${size()}`;
  stats();summaries();attList();hint();
}
function size(){if(!A.geo)return'';A.geo.computeBoundingBox();const s=A.geo.boundingBox.getSize(new THREE.Vector3());return` · ${Math.round(s.x)} × ${Math.round(s.y)} × ${Math.round(s.z)} mm`;}
function stats(){const b=E.built();let minD=Infinity;for(const sh of b.shapes){if(sh.k==='circ')minD=Math.min(minD,2*sh.r);else if(sh.k==='line')minD=Math.min(minD,sh.w);}
  const st=[['Openings',A.applied?'applied':b.shapes.length.toLocaleString()],['Model',A.closed?'solid':'surface']];if(isFinite(minD))st.push(['Smallest',(Math.round(minD*10)/10)+' mm']);
  let h=st.map(([l,v])=>`<span class="stat"><span>${l}</span><b>${v}</b></span>`).join('');if(b.dropped)h+=`<span class="stat"><span>Too small</span><b>${b.dropped}</b></span>`;$('stats').innerHTML=h;}
function summaries(){
  $('sumModel').textContent=A.name?`${A.name} · ${A.closed?'solid':'surface'}`:'';
  $('sumPlace').textContent=`${A.faces.size} face${A.faces.size===1?'':'s'} · ${{wrap:'wrapped',top:'from top',front:'from front',right:'from side',view:'from view'}[A.dir]} · ${A.rot}° · ${S.margin} mm margin`;
  $('sumAttr').textContent=`${A.atts.length} attractor${A.atts.length===1?'':'s'} · ${S.R} mm radius`;
  const p=E.PMAP[S.pattern];$('sumPattern').textContent=`${p.name} · ${S.s} mm cell`;
  $('sumApply').textContent=A.op==='cut'?'Cut out':`${A.op==='emboss'?'Extrude':'Recess'} ${A.depth} mm`;
}
function attList(){const box=$('attList');box.innerHTML='';
  A.atts.forEach((at,i)=>{const row=document.createElement('div');row.className='att';row.setAttribute('aria-current',i===A.sel);const curved=at.t==='line'&&at.pts.some(q=>q.sm);
    row.innerHTML=`<button class="att-pick"><span class="ms s20">${at.t==='point'?'adjust':curved?'line_curve':'timeline'}</span><span>${at.t==='point'?'Point':curved?'Curve':'Polyline'} ${i+1}</span><small>${at.t==='point'?'on the model':at.pts.length+' points'}</small></button>`+
      (at.t==='line'?`<button class="icon-btn" data-curve title="${curved?'Make straight segments':'Make it a smooth curve'}" aria-pressed="${curved}"><span class="ms s20">${curved?'timeline':'line_curve'}</span></button>`:'')+
      `<button class="icon-btn" data-del title="Remove" aria-label="Remove attractor ${i+1}"><span class="ms s20">close</span></button>`;
    row.querySelector('.att-pick').onclick=()=>{A.sel=i;A.selP=-1;refresh();paint();};
    const c=row.querySelector('[data-curve]');if(c)c.onclick=()=>{A.sel=i;A.selP=-1;toggleCurve();};
    row.querySelector('[data-del]').onclick=()=>{A.atts.splice(i,1);A.sel=-1;A.selP=-1;A.applied=false;changed();};box.appendChild(row);});}
const K_=(k,l)=>`<span class="key"><kbd>${k}</kbd>${l}</span>`;
function hint(){let h;
  if(A.tool==='point')h=['adjust','Point attractor','Click on the model to place it.',[['Esc','cancel']]];
  else if(A.tool==='line')h=['timeline','Line attractor',A.pending&&A.pending.length?'Click to add more points on the model. Double-click, press Enter or click the last point to finish.':'Click on the model to set the start point.',[['Enter','finish'],['Esc','cancel']]];
  else if(A.atts[A.sel]&&A.atts[A.sel].t==='line')h=['timeline','Line selected','Drag a handle to move that point along the surface. Double-click a handle to make it smooth or sharp.',[['S','curve'],['Del','remove']]];
  else if(A.atts[A.sel])h=['adjust','Point selected','Drag the handle to move it along the surface.',[['Del','remove']]];
  else h=['arrow_selector_tool','Orbit and select',faceMsg||'Click a face to put the pattern on it, Shift-click to add touching faces. Drag to orbit, right-drag to pan, scroll to zoom.',[['Shift','add face'],['P','point'],['L','line'],['F','fit']]];
  $('hintIcon').textContent=h[0];$('hintTitle').textContent=h[1];$('hintText').textContent=h[2];$('hintKeys').innerHTML=h[3].map(([k,l])=>K_(k,l)).join('');}

// fields: S keys go to the engine, the rest to the 3D state
const AKEYS=new Set(['rot','ox','oy','depth']),FRAMEKEYS=new Set(['rot','ox','oy']);
function getV(k){return AKEYS.has(k)?A[k]:S[k];}
document.querySelectorAll('.field').forEach(f=>{
  const k=f.dataset.key,mn=f.dataset.min,mx=f.dataset.max,stp=f.dataset.step,unit=f.dataset.unit||'mm',top=f.querySelector('.field-top'),label=top.firstElementChild.textContent;
  const box=document.createElement('span');box.className='numbox';box.innerHTML=`<input type="number" min="${mn}" max="${mx}" step="${stp}" aria-label="${label} in ${unit}"><span>${unit}</span>`;top.appendChild(box);
  const r=document.createElement('input');r.type='range';r.min=mn;r.max=mx;r.step=stp;r.setAttribute('aria-label',label);f.appendChild(r);const num=box.firstChild;num.value=r.value=getV(k);fillRange(r);
  const apply=v=>{v=parseFloat(v);if(isNaN(v))return;v=clamp(v,+mn,+mx);if(AKEYS.has(k))A[k]=v;else S[k]=v;if(k!=='depth')A.applied=false;changed(FRAMEKEYS.has(k));summaries();};
  r.addEventListener('input',()=>{num.value=r.value;fillRange(r);apply(r.value);});
  num.addEventListener('change',()=>{const v=clamp(parseFloat(num.value)||0,+mn,+mx);num.value=r.value=v;fillRange(r);apply(v);});
});
function syncFields(){document.querySelectorAll('.field').forEach(f=>{const v=getV(f.dataset.key),r=f.querySelector('input[type=range]');if(!r)return;r.value=v;f.querySelector('.numbox input').value=v;fillRange(r);});}
function setOpen(sec,on){const el=document.querySelector(`[data-sec=${sec}]`),hd=el.querySelector('.acc-head');hd.setAttribute('aria-expanded',on);el.querySelector('.acc-body').hidden=!on;hd.querySelector('.ms').textContent=on?'expand_less':'expand_more';}
document.querySelectorAll('.acc').forEach(sec=>{const hd=sec.querySelector('.acc-head');hd.onclick=()=>setOpen(sec.dataset.sec,hd.getAttribute('aria-expanded')!=='true');});
document.querySelectorAll('#dirSeg button').forEach(b=>b.onclick=()=>{A.dir=b.dataset.v;if(A.dir==='view')captureView();A.applied=false;changed(true);});
document.querySelectorAll('#opSeg button').forEach(b=>b.onclick=()=>{A.op=b.dataset.v;refresh();});
document.querySelectorAll('.switch').forEach(b=>{b.setAttribute('aria-checked',!!S[b.dataset.key]);b.onclick=()=>{S[b.dataset.key]=!S[b.dataset.key];b.setAttribute('aria-checked',S[b.dataset.key]);A.applied=false;changed();};});
$('fall').value=S.fall;$('fall').onchange=e=>{S.fall=e.target.value;A.applied=false;changed();};
$('chipField').onclick=()=>{S.showField=!S.showField;paint();refresh();};
$('chipColor').onclick=()=>{S.color=!S.color;paint();refresh();};
document.querySelectorAll('.tool[data-tool]').forEach(b=>b.onclick=()=>setTool(b.dataset.tool));
$('smoothTool').onclick=toggleCurve;$('delTool').onclick=removeSelected;
$('addPoint').onclick=()=>setTool('point');$('addLine').onclick=()=>setTool('line');
$('applyBtn').onclick=applyOp;$('undoBtn').onclick=undo;$('resetBtn').onclick=resetModel;
$('reseed').onclick=()=>{S.seed=(S.seed*9301+49297)%233280||1;A.applied=false;changed();};
document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>frameCamera(b.dataset.view==='fit'?undefined:b.dataset.view));
$('openBtn').onclick=()=>$('fileIn').click();$('fileIn').onchange=e=>{const f=e.target.files[0];if(f)openFile(f);e.target.value='';};
$('units').onchange=()=>{A.units=+$('units').value;if(raw&&!raw.unitsFixed){raw.info='Units: '+$('units').selectedOptions[0].text;applyImport();}};
$('upAxis').onchange=()=>{A.up=$('upAxis').value;if(raw)applyImport();};
// drag and drop a model onto the page
['dragover','drop'].forEach(t=>window.addEventListener(t,e=>{e.preventDefault();if(t==='drop'&&e.dataTransfer.files[0])openFile(e.dataTransfer.files[0]);}));
$('imgBtn').onclick=()=>$('imgIn').click();
$('imgIn').onchange=e=>{const f=e.target.files[0];if(!f)return;const im=new Image();im.onload=()=>{E.drawImage(im);$('imgName').textContent=f.name;A.applied=false;changed();};im.src=URL.createObjectURL(f);};
// samples
const sb=$('samples');for(const[id,name,info,,path]of SAMPLES){const b=document.createElement('button');b.className='sample';b.dataset.id=id;b.title=info;
  b.innerHTML=`<svg width="44" height="30" viewBox="0 0 44 30" aria-hidden="true"><path d="${path}" fill="none" stroke="currentColor" stroke-width="2" stroke-linejoin="round" stroke-linecap="round"/></svg>${name}`;b.onclick=()=>loadSample(id);sb.appendChild(b);}
// pattern menu
const groupOf=p=>p.group.split(' · ')[0];
function patternUI(){const p=E.PMAP[S.pattern];$('patGroup').textContent=p.group;$('patName').textContent=p.name;$('patDrive').textContent=p.drive;
  $('imgRow').hidden=S.pattern!=='halftone';$('reseed').hidden=!['voronoi','delaunay','truchet','packing'].includes(S.pattern);
  const m=$('patMenu');m.innerHTML='';const groups={};for(const q of E.PATTERNS)if(!HIDDEN.has(q.id))(groups[groupOf(q)]||(groups[groupOf(q)]=[])).push(q);
  for(const g in groups){const h=document.createElement('div');h.className='dd-group';h.textContent=g;m.appendChild(h);
    for(const q of groups[g]){const b=document.createElement('button');b.className='dd-item';b.setAttribute('role','option');b.setAttribute('aria-selected',q.id===S.pattern);b.innerHTML=`<span>${q.name}</span><span class="ms s20">check</span>`;
      b.onclick=()=>{S.pattern=q.id;closeMenus();patternUI();A.applied=false;changed();$('patBtn').focus();};m.appendChild(b);}}}
function closeMenus(){$('patMenu').hidden=true;$('patBtn').setAttribute('aria-expanded','false');$('patArrow').textContent='arrow_drop_down';$('exportMenu').hidden=true;$('exportBtn').setAttribute('aria-expanded','false');}
$('patBtn').onclick=e=>{e.stopPropagation();const open=$('patMenu').hidden;closeMenus();if(open){$('patMenu').hidden=false;$('patBtn').setAttribute('aria-expanded','true');$('patArrow').textContent='arrow_drop_up';}};
$('exportBtn').onclick=e=>{e.stopPropagation();const open=$('exportMenu').hidden;closeMenus();if(open){$('exportMenu').hidden=false;$('exportBtn').setAttribute('aria-expanded','true');}};
document.addEventListener('click',e=>{if(!e.target.closest('.dd,.menu-wrap'))closeMenus();});
document.querySelectorAll('[data-ex]').forEach(b=>b.onclick=()=>{closeMenus();exportAs(b.dataset.ex);});
// help
$('helpBtn').onclick=()=>{$('help').hidden=false;$('helpClose').focus();};$('helpClose').onclick=()=>{$('help').hidden=true;};$('help').onclick=e=>{if(e.target===$('help'))$('help').hidden=true;};
// theme: auto, light, dark (shared with the 2D playground on the same site origin)
const THEMES={auto:'brightness_auto',light:'light_mode',dark:'dark_mode'};let theme='auto';try{theme=localStorage.getItem('ap-theme')||'auto';}catch(e){}if(!THEMES[theme])theme='auto';
function applyTheme(t){document.documentElement.setAttribute('data-theme',t);$('themeIcon').textContent=THEMES[t];$('themeBtn').title=`Theme: ${t} (click to change)`;try{localStorage.setItem('ap-theme',t);}catch(e){}themeScene();}
function themeScene(){if(F)uvs();scene.background=new THREE.Color(css('--sc-low'));edges.material.color.set(css('--outline'));grid.material.color=new THREE.Color(css('--outline-v'));if(F)paint();}
$('themeBtn').onclick=()=>{theme={auto:'light',light:'dark',dark:'auto'}[theme];applyTheme(theme);};
matchMedia('(prefers-color-scheme: dark)').addEventListener('change',themeScene);

// ---------- boot ----------
applyTheme(theme);patternUI();resize();loadSample('grille');setTool('select');loop();
window.__AP3={A,S,E,applyOp,loadSample,openFile,exportAs,frame:()=>F,setTool,finishLine,camera,mesh,undo,THREE};
