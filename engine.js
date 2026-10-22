// Attractor pattern engine, shared with the 2D playground (siatohi80/attractor-patterns).
// In 3D the sheet is the model's footprint in the projection plane, in mm, and MASK says where the model is.
window.APE=(function(){'use strict';
let PW=640, PH=360;                 // sheet in mm; the 3D app resizes it to the model's footprint
const $=id=>document.getElementById(id);
const css=n=>getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v)), lerp=(a,b,t)=>a+(b-a)*t;

// ---------- state ----------
const S={
  pattern:'honey', atts:[{t:'line',pts:[{p:[110,250],sm:false},{p:[530,110],sm:false}]},{t:'point',a:[470,250]}], sel:-1,
  R:220, fall:'smooth', comb:'max', inv:false, align:false, showField:true, color:false,
  s:24, b:2, m:2, margin:8, fillet:1, seed:7, ctrl:null, outline:null, holes:[], selHole:-1, outlineVer:0, smoothNew:false, drawing:null
};

// ---------- outline presets ----------
function presetOutline(k){
  const cx=PW/2, cy=PH/2;
  if(k==='rect') return sharp([[20,20],[PW-20,20],[PW-20,PH-20],[20,PH-20]]);
  if(k==='circle'){const r=160,o=[];for(let i=0;i<8;i++){const a=i/8*Math.PI*2;o.push({p:[cx+r*Math.cos(a),cy+r*Math.sin(a)],sm:true});}return o;}
  if(k==='blob') return [[120,90],[330,50],[560,110],[590,250],[420,320],[200,310],[60,220]].map(p=>({p,sm:true}));
  if(k==='hex'){const r=170,o=[];for(let i=0;i<6;i++){const a=i/6*Math.PI*2;o.push([cx+r*Math.cos(a),cy+r*0.95*Math.sin(a)]);}return sharp(o);}
  // car grille: wide top, tapered bottom, chamfered corners
  return sharp([[70,60],[570,60],[610,110],[560,300],[480,330],[160,330],[80,300],[30,110]]);
}
function sharp(a){return a.map(p=>({p,sm:false}));}
// Closed Catmull-Rom through control points; a sharp point keeps a corner.
function buildOutline(){S.outline=curveOf(S.ctrl);for(const h of S.holes)h.poly=curveOf(h.ctrl);S.outlineVer++;}
function curveOf(C){
  const n=C.length,o=[];
  if(!C.some(c=>c.sm))return C.map(c=>c.p.slice());
  for(let i=0;i<n;i++){
    const P1=C[i],P2=C[(i+1)%n],P0=P1.sm?C[(i+n-1)%n]:P1,P3=P2.sm?C[(i+2)%n]:P2;
    const L=Math.hypot(P2.p[0]-P1.p[0],P2.p[1]-P1.p[1]),N=Math.max(2,Math.min(40,Math.ceil(L/6)));
    for(let k=0;k<N;k++){const t=k/N,t2=t*t,t3=t2*t;const f=(a,b,c,d)=>0.5*(2*b+(-a+c)*t+(2*a-5*b+4*c-d)*t2+(-a+3*b-3*c+d)*t3);
      o.push([clamp(f(P0.p[0],P1.p[0],P2.p[0],P3.p[0]),0,PW),clamp(f(P0.p[1],P1.p[1],P2.p[1],P3.p[1]),0,PH)]);}
  }
  return o;
}
function roundHole(x,y,r){const o=[];for(let i=0;i<8;i++){const a=i/8*Math.PI*2;o.push({p:[x+r*Math.cos(a),y+r*Math.sin(a)],sm:true});}return{ctrl:o,poly:null};}
function rdp(pts,tol){if(pts.length<3)return pts;let dm=0,ix=0;const A=pts[0],B=pts[pts.length-1];for(let i=1;i<pts.length-1;i++){const d=segDist(pts[i][0],pts[i][1],A,B);if(d>dm){dm=d;ix=i;}}
  if(dm<=tol)return[A,B];return rdp(pts.slice(0,ix+1),tol).slice(0,-1).concat(rdp(pts.slice(ix),tol));}
S.ctrl=presetOutline('grille');

// ---------- geometry helpers ----------
function area(p){let a=0;for(let i=0,n=p.length;i<n;i++){const q=p[i],r=p[(i+1)%n];a+=q[0]*r[1]-r[0]*q[1];}return a/2;}
function perim(p){let l=0;for(let i=0,n=p.length;i<n;i++){const q=p[i],r=p[(i+1)%n];l+=Math.hypot(r[0]-q[0],r[1]-q[1]);}return l;}
function inDia(p){const P=perim(p);return P?4*Math.abs(area(p))/P:0;}   // approx. inscribed diameter
function centroid(p){let x=0,y=0;for(const q of p){x+=q[0];y+=q[1];}return[x/p.length,y/p.length];}
function clipHalf(poly,px,py,nx,ny,d){ // keep points with (pt-p)·n >= d
  const out=[],n=poly.length; if(!n) return out;
  for(let i=0;i<n;i++){
    const A=poly[i],B=poly[(i+1)%n];
    const da=(A[0]-px)*nx+(A[1]-py)*ny-d, db=(B[0]-px)*nx+(B[1]-py)*ny-d;
    if(da>=0) out.push(A);
    if((da>=0)!==(db>=0)){const t=da/(da-db);out.push([A[0]+(B[0]-A[0])*t,A[1]+(B[1]-A[1])*t]);}
  }
  return out;
}
function inset(poly,d){ // convex polygon inset by d
  const s=area(poly)>0?1:-1; let out=poly;
  for(let i=0,n=poly.length;i<n;i++){
    const p=poly[i],q=poly[(i+1)%n],ex=q[0]-p[0],ey=q[1]-p[1],L=Math.hypot(ex,ey); if(L<1e-9) continue;
    out=clipHalf(out,p[0],p[1],s*-ey/L,s*ex/L,d); if(out.length<3) return [];
  }
  return out;
}
function fillet(p,r){if(r<=0)return p;const o=[],n=p.length;
  for(let i=0;i<n;i++){const P=p[i],A=p[(i+n-1)%n],B=p[(i+1)%n],la=Math.hypot(A[0]-P[0],A[1]-P[1]),lb=Math.hypot(B[0]-P[0],B[1]-P[1]);if(la<1e-9||lb<1e-9){o.push(P);continue;}
    const u1=[(A[0]-P[0])/la,(A[1]-P[1])/la],u2=[(B[0]-P[0])/lb,(B[1]-P[1])/lb],th=Math.acos(clamp(u1[0]*u2[0]+u1[1]*u2[1],-1,1));
    if(th>3.1||th<1e-3){o.push(P);continue;}const tn=Math.tan(th/2),t=Math.min(r/tn,0.45*la,0.45*lb),rr=t*tn;
    let bx=u1[0]+u2[0],by=u1[1]+u2[1];const bl=Math.hypot(bx,by);bx/=bl;by/=bl;const h=rr/Math.sin(th/2),cx=P[0]+bx*h,cy=P[1]+by*h;
    const s0=[P[0]+u1[0]*t,P[1]+u1[1]*t],s1=[P[0]+u2[0]*t,P[1]+u2[1]*t];let a0=Math.atan2(s0[1]-cy,s0[0]-cx),a1=Math.atan2(s1[1]-cy,s1[0]-cx),da=a1-a0;
    while(da>Math.PI)da-=2*Math.PI;while(da<-Math.PI)da+=2*Math.PI;const N=Math.max(2,Math.ceil(Math.abs(da)/0.35));for(let k=0;k<=N;k++){const a=a0+da*k/N;o.push([cx+rr*Math.cos(a),cy+rr*Math.sin(a)]);}}
  return o;}
function regPoly(x,y,r,n,rot){const o=[];for(let i=0;i<n;i++){const a=rot+i*2*Math.PI/n;o.push([x+r*Math.cos(a),y+r*Math.sin(a)]);}return o;}
function star(x,y,ro,ri,n,rot){const o=[];for(let i=0;i<2*n;i++){const a=rot+i*Math.PI/n,r=i%2?ri:ro;o.push([x+r*Math.cos(a),y+r*Math.sin(a)]);}return o;}
function superEllipse(x,y,r,e,N){const o=[];for(let i=0;i<N;i++){const t=i/N*2*Math.PI,c=Math.cos(t),s=Math.sin(t);o.push([x+r*Math.sign(c)*Math.abs(c)**(2/e),y+r*Math.sign(s)*Math.abs(s)**(2/e)]);}return o;}
function obround(x,y,L,w,ang){const r=w/2,h=Math.max(L/2-r,0),o=[],c=Math.cos(ang),s=Math.sin(ang);
  for(let i=0;i<=10;i++){const a=-Math.PI/2+i*Math.PI/10;o.push([h+r*Math.cos(a),r*Math.sin(a)]);}
  for(let i=0;i<=10;i++){const a=Math.PI/2+i*Math.PI/10;o.push([-h+r*Math.cos(a),r*Math.sin(a)]);}
  return o.map(([u,v])=>[x+u*c-v*s,y+u*s+v*c]);}
function lens(x,y,L,W,ang){const R=(L*L/4+W*W/4)/W,d=R-W/2,ha=Math.asin(clamp(L/2/R,0,1)),o=[],c=Math.cos(ang),s=Math.sin(ang);
  for(let i=0;i<=8;i++){const a=-ha+2*ha*i/8;o.push([R*Math.sin(a),R*Math.cos(a)-d]);}
  for(let i=0;i<=8;i++){const a=ha-2*ha*i/8;o.push([R*Math.sin(a),-(R*Math.cos(a)-d)]);}
  return o.map(([u,v])=>[x+u*c-v*s,y+u*s+v*c]);}
function yShape(x,y,L,w){const o=[],ci=(w/2)/Math.sin(Math.PI/3);
  for(let i=0;i<3;i++){const a=Math.PI/2+i*2*Math.PI/3,nx=-Math.sin(a),ny=Math.cos(a),b=a+Math.PI/3;
    o.push([x+Math.cos(a)*L-nx*w/2,y+Math.sin(a)*L-ny*w/2],[x+Math.cos(a)*L+nx*w/2,y+Math.sin(a)*L+ny*w/2],[x+Math.cos(b)*ci,y+Math.sin(b)*ci]);}
  return o;}
function segDist(px,py,a,b){const bx=b[0]-a[0],by=b[1]-a[1],L2=bx*bx+by*by||1;let t=((px-a[0])*bx+(py-a[1])*by)/L2;t=clamp(t,0,1);return Math.hypot(px-a[0]-t*bx,py-a[1]-t*by);}
function inPoly(x,y,p){let c=false;for(let i=0,j=p.length-1;i<p.length;j=i++){const a=p[i],b=p[j];if(((a[1]>y)!==(b[1]>y))&&(x<(b[0]-a[0])*(y-a[1])/(b[1]-a[1])+a[0]))c=!c;}return c;}
function edgeDist(x,y,p){let d=1e9;for(let i=0,n=p.length;i<n;i++)d=Math.min(d,segDist(x,y,p[i],p[(i+1)%n]));return d;}
function inside(x,y){if(MASK)return maskAt(x,y)>0;if(!inPoly(x,y,S.outline))return false;for(const h of S.holes)if(inPoly(x,y,h.poly))return false;return true;}
function fitsPt(x,y,extra){if(MASK)return maskAt(x,y)>=S.margin+(extra||0);const m=S.margin+(extra||0);if(!inside(x,y)||edgeDist(x,y,S.outline)<m)return false;for(const h of S.holes)if(edgeDist(x,y,h.poly)<m)return false;return true;}
function bbox(p){let a=1e9,b=1e9,c=-1e9,d=-1e9;for(const q of p){a=Math.min(a,q[0]);b=Math.min(b,q[1]);c=Math.max(c,q[0]);d=Math.max(d,q[1]);}return[a,b,c,d];}
function mulberry(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}

// ---------- attractor field ----------
function fallOf(d){
  const u=clamp(d/S.R,0,1);
  switch(S.fall){
    case 'lin': return 1-u;
    case 'gauss': return u>=1?0:Math.exp(-4.5*u*u);
    case 'inv': return 1/(1+(d/(S.R*0.25))**2);
    case 'step': return Math.ceil((1-u)*4)/4;
    default: return 1-u*u*(3-2*u);
  }
}
// A line attractor is an open polyline {t:'line',pts:[{p,sm}]}; smooth points bend it into a curve through them.
function openCurve(C){
  const n=C.length;if(!C.some(c=>c.sm))return C.map(c=>c.p);const o=[];
  for(let i=0;i<n-1;i++){
    const P1=C[i],P2=C[i+1],P0=P1.sm&&i>0?C[i-1]:P1,P3=P2.sm&&i+2<n?C[i+2]:P2;
    const L=Math.hypot(P2.p[0]-P1.p[0],P2.p[1]-P1.p[1]),N=Math.max(2,Math.min(40,Math.ceil(L/6)));
    for(let k=0;k<N;k++){const t=k/N,t2=t*t,t3=t2*t;const f=(a,b,c,d)=>0.5*(2*b+(-a+c)*t+(2*a-5*b+4*c-d)*t2+(-a+3*b-3*c+d)*t3);
      o.push([f(P0.p[0],P1.p[0],P2.p[0],P3.p[0]),f(P0.p[1],P1.p[1],P2.p[1],P3.p[1])]);}
  }
  o.push(C[n-1].p);return o;
}
const LCACHE=new WeakMap();
function linePts(A){const key=JSON.stringify(A.pts),c=LCACHE.get(A);if(c&&c.key===key)return c.p;const p=openCurve(A.pts);LCACHE.set(A,{key,p});return p;}
function lineLen(A){const p=linePts(A);let L=0;for(let i=1;i<p.length;i++)L+=Math.hypot(p[i][0]-p[i-1][0],p[i][1]-p[i-1][1]);return L;}
function attInfo(A,x,y){
  if(A.t==='point'){const dx=x-A.a[0],dy=y-A.a[1],d=Math.hypot(dx,dy)||1e-9;return{d,nx:dx/d,ny:dy/d,tx:-dy/d,ty:dx/d};}
  const P=linePts(A);let b=null;
  for(let i=1;i<P.length;i++){const ax=P[i-1][0],ay=P[i-1][1],bx=P[i][0]-ax,by=P[i][1]-ay,L2=bx*bx+by*by||1e-12;
    const t=clamp(((x-ax)*bx+(y-ay)*by)/L2,0,1),dx=x-ax-t*bx,dy=y-ay-t*by,d2=dx*dx+dy*dy;if(!b||d2<b.d2)b={d2,dx,dy,bx,by,L:Math.sqrt(L2)||1};}
  const d=Math.sqrt(b.d2)||1e-9;return{d,nx:b.dx/d,ny:b.dy/d,tx:b.bx/b.L,ty:b.by/b.L};
}
function field(x,y){
  let f=0,best=-1,bi=null;
  for(const A of S.atts){const i=attInfo(A,x,y),v=fallOf(i.d);if(S.comb==='max')f=Math.max(f,v);else f+=v;if(v>best){best=v;bi=i;}}
  f=clamp(f,0,1); if(S.inv) f=1-f;
  return Object.assign({f},bi||{d:1e9,nx:1,ny:0,tx:1,ty:0});
}

// ---------- samplers ----------
function outlineBox(){const[a,b,c,d]=bbox(S.outline);return{x0:a,y0:b,x1:c,y1:d};}
function squareCenters(s){const B=outlineBox(),o=[];for(let y=B.y0+s/2;y<=B.y1;y+=s)for(let x=B.x0+s/2;x<=B.x1;x+=s)o.push([x,y]);return o;}
function hexCenters(s,rowStep){const B=outlineBox(),o=[],h=rowStep||s*Math.sqrt(3)/2;let r=0;for(let y=B.y0;y<=B.y1+h;y+=h,r++)for(let x=B.x0+(r%2?s/2:0);x<=B.x1+s;x+=s)o.push([x,y]);return o;}
function dart(radFn,pairFn,maxPair,tries,rng){
  const B=outlineBox(),cell=Math.max(maxPair,1),cols=Math.ceil((B.x1-B.x0)/cell)+3,grid=new Map(),pts=[];
  for(let t=0;t<tries;t++){
    const x=B.x0+rng()*(B.x1-B.x0),y=B.y0+rng()*(B.y1-B.y0);
    if(!inside(x,y)) continue;
    const r=radFn(x,y),gx=Math.floor((x-B.x0)/cell)+1,gy=Math.floor((y-B.y0)/cell)+1;let ok=true;
    for(let ix=gx-1;ix<=gx+1&&ok;ix++)for(let iy=gy-1;iy<=gy+1&&ok;iy++){const l=grid.get(ix+iy*cols);if(l)for(const q of l){if(Math.hypot(q.x-x,q.y-y)<pairFn(r,q.r)){ok=false;break;}}}
    if(!ok) continue;
    const p={x,y,r},key=gx+gy*cols;pts.push(p);(grid.get(key)||grid.set(key,[]).get(key)).push(p);
  }
  return{pts,grid,cell,cols,B};
}
function delaunay(P){
  const big=1e5,V=P.concat([[-big,-big],[big,-big],[0,big]]),n=P.length;
  const circ=(a,b,c)=>{const[ax,ay]=V[a],[bx,by]=V[b],[cx,cy]=V[c],d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))||1e-12;
    const ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d,uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d;
    return{a,b,c,x:ux,y:uy,r2:(ax-ux)**2+(ay-uy)**2};};
  let T=[circ(n,n+1,n+2)];
  for(let i=0;i<n;i++){
    const[px,py]=V[i],bad=[],keep=[];
    for(const t of T)((px-t.x)**2+(py-t.y)**2<t.r2?bad:keep).push(t);
    const ec=new Map();
    for(const t of bad)for(const[u,v]of[[t.a,t.b],[t.b,t.c],[t.c,t.a]]){const k=u<v?u+','+v:v+','+u;const e=ec.get(k);ec.set(k,e?null:[u,v]);}
    T=keep;for(const e of ec.values())if(e)T.push(circ(e[0],e[1],i));
  }
  return T.filter(t=>t.a<n&&t.b<n&&t.c<n).map(t=>[V[t.a],V[t.b],V[t.c]]);
}

// ---------- sample image for halftone ----------
const img=document.createElement('canvas');img.width=PW;img.height=PH;let imgData=null,userImage=null;
function defaultImage(){const W=img.width,H=img.height,g=img.getContext('2d');g.fillStyle='#fff';g.fillRect(0,0,W,H);g.filter=`blur(${Math.max(2,H/36)}px)`;g.fillStyle='#000';
  g.font=`900 ${Math.round(Math.min(H*0.42,W/4.2))}px Archivo, Arial Black, sans-serif`;g.textAlign='center';g.textBaseline='middle';g.fillText('GRILLE',W/2,H/2);g.filter='none';imgData=g.getImageData(0,0,W,H).data;}
function dark(x,y){if(!imgData)return 1;const W=img.width,H=img.height,i=(clamp(Math.round(y*H/PH),0,H-1)*W+clamp(Math.round(x*W/PW),0,W-1))*4;return 1-(imgData[i]*.299+imgData[i+1]*.587+imgData[i+2]*.114)/255;}

// ---------- patterns ----------
// each build returns {shapes:[...], dropped}. Shapes: poly {k:'poly',p,f}, circle {k:'circ',x,y,r,f}, slot line {k:'line',p,w,f}, facet {k:'facet',p,shade,f}, outline seg {k:'seg',p,f}
const PATTERNS=[
 {id:'holes',name:'Round perforation',group:'Grid + shape',drive:'Hole diameter, so open area grades from solid to porous.',make:'Keep hole diameter at or above sheet thickness for punching, and the bridge between holes at least the sheet thickness.',
  build(){const s=S.s,rmax=(s-S.b)/2,o=[];let dr=0;for(const[x,y]of hexCenters(s)){const{f}=field(x,y),r=rmax*f;if(r<=0.05)continue;if(2*r<S.m){dr++;continue;}o.push({k:'circ',x,y,r,f});}return{shapes:o,dropped:dr};}},
 {id:'honey',name:'Honeycomb',group:'Tiling · car grille',drive:'Wall thickness: thin walls (big cells) near the attractor, thick walls far away.',make:'Wall width is cell size minus opening; keep it at or above sheet thickness. Molded grilles need draft on the cell walls.',
  build(){const s=S.s,o=[];let dr=0;for(const[x,y]of hexCenters(s)){const{f}=field(x,y),wall=lerp(s*0.75,S.b,f),ri=(s-wall)/2;if(ri<=0.05)continue;if(2*ri<S.m){dr++;continue;}o.push({k:'poly',p:regPoly(x,y,ri*2/Math.sqrt(3),6,Math.PI/6),f});}return{shapes:o,dropped:dr};}},
 {id:'diamond',name:'Diamond mesh',group:'Tiling · car grille',drive:'Opening size and squash: openings grow and turn square near the attractor.',make:'Acute corners concentrate stress and burn on laser cuts; keep a corner radius. Check the bridge where diamonds squash.',
  build(){const s=S.s,kmax=1-S.b*Math.SQRT2/s,o=[];let dr=0;for(const[x,y]of hexCenters(s,s/2)){const{f}=field(x,y),k=kmax*(0.12+0.88*f),hy=s/2*k,hx=hy*lerp(0.55,1,f);if(hy<=0.05)continue;const p=[[x,y-hy],[x+hx,y],[x,y+hy],[x-hx,y]];if(inDia(p)<S.m){dr++;continue;}o.push({k:'poly',p,f});}return{shapes:o,dropped:dr};}},
 {id:'jewel',name:'Jewel studs (pyramids)',group:'3D texture · car grille',drive:'Pyramid height, and the apex leans toward the attractor so facets catch light differently.',make:'Emboss depth is limited by material stretch; for molding keep draft angles on facets and avoid undercuts.',
  build(){const s=S.s,o=[],L=[-0.45,-0.6,0.66],ln=Math.hypot(...L);for(const[x,y]of squareCenters(s)){const g=field(x,y),f=g.f,h=s*(0.08+0.5*f);
    const ap=[x-g.nx*f*s*0.28,y-g.ny*f*s*0.28],q=s/2-S.b/4,c=[[x-q,y-q],[x+q,y-q],[x+q,y+q],[x-q,y+q]];
    for(let i=0;i<4;i++){const A=c[i],B=c[(i+1)%4],v1=[B[0]-A[0],B[1]-A[1],0],v2=[ap[0]-A[0],ap[1]-A[1],h];let n=[v1[1]*v2[2]-v1[2]*v2[1],v1[2]*v2[0]-v1[0]*v2[2],v1[0]*v2[1]-v1[1]*v2[0]];if(n[2]<0)n=n.map(v=>-v);const nl=Math.hypot(...n)||1;
      const sh=clamp((n[0]*L[0]+n[1]*L[1]+n[2]*L[2])/nl/ln,0,1);o.push({k:'facet',p:[A,B,ap],shade:sh,f});}}return{shapes:o,dropped:0,grouped:4};}},
 {id:'slots',name:'Rotating slots (louvers)',group:'Linear',drive:'Slot angle (0 to 90°). With "align" on, slots follow the attractor direction and grow near it.',make:'Rounded slot ends cut cleanly. Slot length is capped so neighbours keep the minimum bridge at any angle.',
  build(){const s=S.s,Lm=Math.min(0.92*s,s-S.b),o=[];let dr=0;for(const[x,y]of squareCenters(s)){const g=field(x,y),f=g.f,w=Math.min(Math.max(S.m,s*0.26),Lm);let ang,L;
    if(S.align){ang=Math.atan2(g.ty,g.tx);L=Lm*(0.3+0.7*f);}else{ang=f*Math.PI/2;L=Lm;} if(L<S.m){dr++;continue;} o.push({k:'poly',p:obround(x,y,L,w,ang),f,noRound:true});}return{shapes:o,dropped:dr};}},
 {id:'voronoi',name:'Voronoi cells',group:'Cellular',drive:'Cell density (small cells near the attractor) and wall thickness.',make:'Short Voronoi edges create slivers; small cells are removed and corners get the corner radius. Cells cut by the outline are left solid.',
  build(rng){const s=S.s,sep=(x,y)=>s*lerp(1.5,0.55,field(x,y).f),D=dart(sep,(a,b)=>(a+b)/2,s*1.5,Math.round(area(S.outline)/(s*s)*40),rng),o=[];let dr=0;
    const B=D.B;for(const p of D.pts){let cell=[[B.x0-1,B.y0-1],[B.x1+1,B.y0-1],[B.x1+1,B.y1+1],[B.x0-1,B.y1+1]];
      const gx=Math.floor((p.x-B.x0)/D.cell)+1,gy=Math.floor((p.y-B.y0)/D.cell)+1;
      for(let ix=gx-2;ix<=gx+2;ix++)for(let iy=gy-2;iy<=gy+2;iy++){const l=D.grid.get(ix+iy*D.cols);if(l)for(const q of l){if(q===p)continue;const mx=(p.x+q.x)/2,my=(p.y+q.y)/2,nx=p.x-q.x,ny=p.y-q.y,L=Math.hypot(nx,ny);cell=clipHalf(cell,mx,my,nx/L,ny/L,0);}}
      const[cx,cy]=centroid(cell),f=field(cx,cy).f,h=inset(cell,S.b/2+(1-f)*s*0.12);if(h.length<3)continue;if(inDia(h)<S.m){dr++;continue;}o.push({k:'poly',p:h,f});}
    return{shapes:o,dropped:dr};}},
 {id:'delaunay',name:'Triangulated panels',group:'Cellular',drive:'Opening size inside each triangle: large near the attractor, small far away.',make:'Thin triangles give unusable openings; anything below the minimum hole size is removed.',
  build(rng){const s=S.s,sep=(x,y)=>s*lerp(2,0.85,field(x,y).f),D=dart(sep,(a,b)=>(a+b)/2,s*2,Math.round(area(S.outline)/(s*s)*30),rng),P=D.pts.map(p=>[p.x,p.y]);
    const per=perim(S.outline),n=S.outline.length;for(let i=0;i<n;i++){const A=S.outline[i],B=S.outline[(i+1)%n],L=Math.hypot(B[0]-A[0],B[1]-A[1]),k=Math.max(1,Math.round(L/(s*1.2)));for(let j=0;j<k;j++)P.push([A[0]+(B[0]-A[0])*j/k,A[1]+(B[1]-A[1])*j/k]);}
    for(const h of S.holes){const hp=h.poly,m=hp.length;for(let i=0;i<m;i++){const A=hp[i],B=hp[(i+1)%m],L=Math.hypot(B[0]-A[0],B[1]-A[1]),k=Math.max(1,Math.round(L/(s*1.2)));for(let j=0;j<k;j++)P.push([A[0]+(B[0]-A[0])*j/k,A[1]+(B[1]-A[1])*j/k]);}}
    const o=[];let dr=0;for(const t of delaunay(P)){const[cx,cy]=centroid(t);if(!inside(cx,cy))continue;const f=field(cx,cy).f,ri=inDia(t)/2,d=S.b/2+(1-(0.2+0.8*f))*Math.max(ri-S.b/2,0),h=inset(t,d);
      if(h.length<3)continue;if(inDia(h)<S.m){dr++;continue;}o.push({k:'poly',p:h,f});}return{shapes:o,dropped:dr};}},
 {id:'morph',name:'Shape morph (circle to square)',group:'Grid + shape',drive:'Blend from circle (far) to rounded square (near), plus size.',make:'Square shapes have tighter corner gaps than circles; the bridge is checked at the corners, not only between centres.',
  build(){const s=S.s,o=[];let dr=0;for(const[x,y]of squareCenters(s)){const{f}=field(x,y),r=(s-S.b)/2*(0.4+0.6*f);if(2*r<S.m){dr++;continue;}o.push({k:'poly',p:superEllipse(x,y,r,lerp(2,9,f),48),f,noRound:true});}return{shapes:o,dropped:dr};}},
 {id:'star',name:'Star tiling (girih-style)',group:'Tiling',drive:'Star sharpness: near-octagons far away, pointed eight-point stars near the attractor.',make:'Pointed tips leave thin straps; use a corner radius for laser and waterjet.',
  build(){const s=S.s,o=[];let dr=0;for(const[x,y]of squareCenters(s)){const{f}=field(x,y),ro=(s-S.b)/2,ri=ro*lerp(0.92,0.42,f),p=star(x,y,ro,ri,8,0);if(inDia(p)<S.m){dr++;continue;}o.push({k:'poly',p,f});}return{shapes:o,dropped:dr};}},
 {id:'truchet',name:'Truchet arcs (threshold tiles)',group:'Tiling',drive:'Whether a tile appears, its slot width, and (with "align") its orientation.',make:'Connected arcs can leave islands that fall out when cut. Use as engraving, or check every solid region stays attached.',
  build(rng){const s=S.s,o=[],arc=(cx,cy,a0)=>{const p=[];for(let i=0;i<=10;i++){const a=a0+i/10*Math.PI/2;p.push([cx+s/2*Math.cos(a),cy+s/2*Math.sin(a)]);}return p;};
    for(const[x,y]of squareCenters(s)){const g=field(x,y),flip=rng()<0.5;if(g.f<0.12)continue;const w=Math.max(S.m,lerp(S.m,s*0.24,g.f)),x0=x-s/2,y0=y-s/2;
      const A=S.align?(g.tx*g.ty>0):flip;
      if(A){o.push({k:'line',p:arc(x0,y0,0),w,f:g.f},{k:'line',p:arc(x0+s,y0+s,Math.PI),w,f:g.f});}else{o.push({k:'line',p:arc(x0+s,y0,Math.PI/2),w,f:g.f},{k:'line',p:arc(x0,y0+s,-Math.PI/2),w,f:g.f});}}
    return{shapes:o,dropped:0,grouped:2};}},
 {id:'contours',name:'Flow lines (contours)',group:'Line-based',drive:'Line spacing (tight near the attractor) and groove width.',make:'As grooves, tool radius sets the minimum spacing. As cut slots, add tabs so strips stay attached.',
  build(){const s=S.s,dm=Math.ceil(Math.hypot(PW,PH))+2,T=new Float32Array(dm+1);for(let d=1;d<=dm;d++){let f=fallOf(d);if(S.inv)f=1-f;T[d]=T[d-1]+1/(s*lerp(1.6,0.4,f));}
    const val=(x,y)=>{if(!S.atts.length)return y/s;let d=1e9;for(const A of S.atts)d=Math.min(d,attInfo(A,x,y).d);const i=Math.min(Math.floor(d),dm-1);return T[i]+(T[i+1]-T[i])*(d-i);};
    const B=outlineBox(),g=3,nx=Math.ceil((B.x1-B.x0)/g)+1,ny=Math.ceil((B.y1-B.y0)/g)+1,V=new Float32Array(nx*ny),o=[];
    for(let j=0;j<ny;j++)for(let i=0;i<nx;i++)V[j*nx+i]=val(B.x0+i*g,B.y0+j*g);
    for(let j=0;j<ny-1;j++)for(let i=0;i<nx-1;i++){const x=B.x0+i*g,y=B.y0+j*g,c=[V[j*nx+i],V[j*nx+i+1],V[(j+1)*nx+i+1],V[(j+1)*nx+i]],P=[[x,y],[x+g,y],[x+g,y+g],[x,y+g]];
      for(let L=Math.ceil(Math.min(...c));L<=Math.max(...c);L++){const pts=[];for(let e=0;e<4;e++){const a=c[e]-L,b=c[(e+1)%4]-L;if((a<0)!==(b<0)){const t=a/(a-b),A=P[e],Bp=P[(e+1)%4];pts.push([A[0]+(Bp[0]-A[0])*t,A[1]+(Bp[1]-A[1])*t]);}}
        for(let k=0;k+1<pts.length;k+=2){const m=[(pts[k][0]+pts[k+1][0])/2,(pts[k][1]+pts[k+1][1])/2],f=field(m[0],m[1]).f;o.push({k:'line',p:[pts[k],pts[k+1]],w:Math.max(S.m,0.6)*lerp(1,2.2,f),f});}}}
    return{shapes:o,dropped:0,grouped:-1};}},
 {id:'packing',name:'Circle packing',group:'Packing',drive:'Circle size: small, tightly packed circles near the attractor.',make:'Gaps between circles never drop below the minimum bridge; circles below the minimum hole are removed.',
  build(rng){const s=S.s,rad=(x,y)=>lerp(s*0.75,s*0.16,field(x,y).f),D=dart(rad,(a,b)=>a+b+S.b,s*1.5+S.b,Math.round(area(S.outline)/(s*s)*70),rng),o=[];let dr=0;
    for(const p of D.pts){if(2*p.r<S.m){dr++;continue;}o.push({k:'circ',x:p.x,y:p.y,r:p.r,f:field(p.x,p.y).f});}return{shapes:o,dropped:dr};}},
 {id:'halftone',name:'Halftone (image + field)',group:'Image-based',drive:'Dot size from a sample image, multiplied by the attractor field. Upload your own image in step 3.',make:'Dots below the minimum hole size are dropped rather than shrunk further; cap open area so the panel stays stiff.',
  build(){const s=S.s,rmax=(s-S.b)/2,o=[];let dr=0;for(const[x,y]of hexCenters(s)){const{f}=field(x,y),r=rmax*(0.15+0.85*f)*(0.12+0.88*dark(x,y));if(2*r<S.m){dr++;continue;}o.push({k:'circ',x,y,r,f});}return{shapes:o,dropped:dr};}},
 {id:'strut',name:'Strut lattice (swelling nodes)',group:'Tiling',drive:'Strut width: thin struts and big triangular openings near the attractor; far away the nodes swell into round lobes and the openings close up.',make:'The struts are the solid part; keep their thinnest width at or above the minimum bridge. Large corner rounding keeps the lobes smooth for laser and waterjet.',
  build(){const s=S.s,h=s*Math.sqrt(3)/2,B=outlineBox(),o=[];let dr=0;
    for(let r=0,y=B.y0-h;y<=B.y1+h;y+=h,r++)for(let x=B.x0-s+(r%2?s/2:0);x<=B.x1+s;x+=s)for(const up of[0,1]){
      const t=up?[[x,y],[x+s,y],[x+s/2,y+h]]:[[x+s,y],[x+s/2,y+h],[x+s*1.5,y+h]],c=centroid(t),f=field(c[0],c[1]).f;
      const w=lerp(s*0.42,S.b,f),p=inset(t,w/2);if(p.length<3){continue;}if(inDia(p)<S.m){dr++;continue;}
      o.push({k:'poly',p:fillet(p,lerp(s*0.2,s*0.04,f)),f,noRound:true});}
    return{shapes:o,dropped:dr};}},
 {id:'ytiles',name:'Y tiles',group:'Tiling',drive:'Arm length and width: Y shapes grow and thicken near the attractor.',make:'Inner corners of the Y are sharp; the corner radius softens them. Arm tips keep the minimum bridge to the next row.',
  build(){const s=S.s,h=s*Math.sqrt(3)/2,o=[];let dr=0;
    for(const[x,y]of hexCenters(s,h)){const f=field(x,y).f;if(f<=0.02)continue;const L=(s/Math.sqrt(3)-S.b)*(0.35+0.65*f),w=Math.max(S.m,lerp(s*0.08,s*0.2,f));
      if(L<S.m){dr++;continue;}o.push({k:'poly',p:yShape(x,y,L,w),f});}
    return{shapes:o,dropped:dr};}},
 {id:'nesthex',name:'Nested hexagons',group:'Tiling',drive:'Ring width: hexagon rings open up near the attractor (a second, inner ring appears) and thin to hairlines far away.',make:'Each ring is cut as six segments with a bridge at every corner, so the centre stays attached. Use as grooves if you want closed rings.',
  build(){const s=S.s,o=[];let dr=0;for(const[x,y]of hexCenters(s)){const f=field(x,y).f,Ro=(s-S.b)/Math.sqrt(3),w=lerp(0,Ro*0.26,f);if(w<=0.05)continue;if(w<S.m){dr++;continue;}
      const ring=(Ro,w)=>{const Ri=Ro-w*2/Math.sqrt(3),gap=S.b/2;for(let i=0;i<6;i++){const a0=Math.PI/6+i*Math.PI/3,a1=a0+Math.PI/3,P=(r,a)=>[x+r*Math.cos(a),y+r*Math.sin(a)];
        const o0=P(Ro,a0),o1=P(Ro,a1),i0=P(Ri,a0),i1=P(Ri,a1),sh=(p,q,d)=>{const L=Math.hypot(q[0]-p[0],q[1]-p[1]);return[p[0]+(q[0]-p[0])/L*d,p[1]+(q[1]-p[1])/L*d];};
        o.push({k:'poly',p:[sh(o0,o1,gap),sh(o1,o0,gap),sh(i1,i0,gap),sh(i0,i1,gap)],f});}return Ri;};
      const Ri=ring(Ro,w),R2=Ri-Math.max(S.b,w*0.9)*2/Math.sqrt(3),w2=w*0.8;if(w2>=S.m&&R2-w2*2/Math.sqrt(3)>S.b)ring(R2,w2);}
    return{shapes:o,dropped:dr,grouped:6};}},
 {id:'sunflower',name:'Sunflower (Fibonacci)',group:'Spiral',drive:'Dot size along a golden-angle spiral centred on the outline: dots grow near the attractor.',make:'Spacing is even across the spiral, so the bridge only depends on the largest dot; dots below the minimum hole are removed.',
  build(){const c=S.s*0.62,ga=Math.PI*(3-Math.sqrt(5)),[cx,cy]=centroid(S.outline),B=outlineBox(),Rmax=Math.hypot(B.x1-B.x0,B.y1-B.y0)/2,n=Math.ceil((Rmax/c)**2),rmax=(c*1.75-S.b)/2,o=[];let dr=0;
    for(let k=1;k<=n;k++){const r=c*Math.sqrt(k),a=k*ga,x=cx+r*Math.cos(a),y=cy+r*Math.sin(a);if(!inside(x,y))continue;const f=field(x,y).f,rr=rmax*f;if(rr<=0.05)continue;if(2*rr<S.m){dr++;continue;}o.push({k:'circ',x,y,r:rr,f});}
    return{shapes:o,dropped:dr};}},
 {id:'herring',name:'Herringbone slots',group:'Linear',drive:'Slot length and width: rows lean alternately left and right, and slots grow near the attractor.',make:'Rounded slot ends cut cleanly. Length is capped so slots in neighbouring rows keep the minimum bridge.',
  build(){const s=S.s,o=[];let dr=0,row=0;const B=outlineBox();for(let y=B.y0+s/4;y<=B.y1;y+=s/2,row++)for(let x=B.x0+s/2;x<=B.x1;x+=s/1.6){const f=field(x,y).f,ang=(row%2?1:-1)*Math.PI/4,L=lerp(s*0.25,s*0.62,f),w=Math.max(S.m,lerp(s*0.12,s*0.2,f));if(f<=0.02)continue;if(L<S.m){dr++;continue;}o.push({k:'poly',p:obround(x,y,L,w,ang),f,noRound:true});}
    return{shapes:o,dropped:dr};}},
 {id:'pinwheel',name:'Pinwheel lens slits',group:'Linear',drive:'Twist and size: lens slits on a triangle grid turn into pinwheels and grow near the attractor.',make:'Lens tips are sharp; the corner radius rounds them. Slits are capped so tips keep the minimum bridge when twisted.',
  build(){const s=S.s,h=s*Math.sqrt(3)/2,o=[];let dr=0;for(const[x,y]of hexCenters(s,h))for(const a of[0,Math.PI/3,2*Math.PI/3]){
      const mx=x+Math.cos(a)*s/2,my=y+Math.sin(a)*s/2,f=field(mx,my).f;if(f<=0.02)continue;const L=lerp(s*0.3,s*0.62,f),W=Math.max(S.m,lerp(s*0.06,s*0.16,f));if(L<S.m){dr++;continue;}
      o.push({k:'poly',p:lens(mx,my,L,W,a+Math.PI/2+f*Math.PI/4),f});}
    return{shapes:o,dropped:dr};}},
 {id:'xdiamond',name:'Cross-slot diamonds',group:'Linear',drive:'Slot length: slots at ±45° grow near the attractor until they meet as diamond outlines.',make:'Slot ends are rounded. The cap on length keeps a bridge where four slots meet at a diamond corner.',
  build(){const s=S.s*0.75,o=[];let dr=0;const B=outlineBox();let j=0;for(let y=B.y0+s/2;y<=B.y1;y+=s,j++){let i=0;for(let x=B.x0+s/2;x<=B.x1;x+=s,i++){const f=field(x,y).f;if(f<=0.02)continue;
      const L=lerp(s*0.3,s*Math.SQRT2-S.b*1.6-Math.max(S.m,s*0.14),f),w=Math.max(S.m,s*0.14);if(L<S.m){dr++;continue;}o.push({k:'poly',p:obround(x,y,L+w,w,((i+j)%2?1:-1)*Math.PI/4),f,noRound:true});}}
    return{shapes:o,dropped:dr};}},
 {id:'rd',name:'Reaction-diffusion',group:'Simulation',drive:'Feed and kill rates: spots far away turn into stripes and mazes near the attractor. Runs live.',make:'Best for 3D printing, CNC relief or engraving. Exports trace the pattern outline; features smaller than your tool or nozzle need filtering.',
  raster:true, build(){return{shapes:rdOutline(),dropped:0,grouped:-1};}}
];
const PMAP=Object.fromEntries(PATTERNS.map(p=>[p.id,p]));

// ---------- reaction-diffusion ----------
const RD={nx:0,ny:0,g:0,U:null,V:null,F:null,K:null,dirty:true,key:''};
function rdInit(){const g=Math.max(1,S.s/14);RD.g=g;RD.nx=Math.ceil(PW/g);RD.ny=Math.ceil(PH/g);const N=RD.nx*RD.ny;RD.U=new Float32Array(N).fill(1);RD.V=new Float32Array(N);RD.F=new Float32Array(N);RD.K=new Float32Array(N);RD.M=new Uint8Array(N);RD.mk='';
  const r=mulberry(S.seed);for(let n=0;n<70;n++){const cx=Math.floor(r()*RD.nx),cy=Math.floor(r()*RD.ny);for(let j=-2;j<=2;j++)for(let i=-2;i<=2;i++){const x=cx+i,y=cy+j;if(x>=0&&y>=0&&x<RD.nx&&y<RD.ny){RD.U[y*RD.nx+x]=0.5;RD.V[y*RD.nx+x]=0.25;}}}RD.dirty=true;}
function rdParams(){for(let j=0;j<RD.ny;j++)for(let i=0;i<RD.nx;i++){const x=(i+.5)*RD.g,y=(j+.5)*RD.g,k=j*RD.nx+i,f=field(x,y).f;RD.F[k]=lerp(0.0367,0.029,f);RD.K[k]=lerp(0.0649,0.057,f);if(RD.mk!==S.outlineVer+'/'+S.margin)RD.M[k]=fitsPt(x,y,0)?1:0;}RD.mk=S.outlineVer+'/'+S.margin;RD.dirty=false;}
function rdStep(n){const{nx,ny,U,V,F,K,M}=RD;const U2=new Float32Array(U.length),V2=new Float32Array(V.length);
  for(let it=0;it<n;it++){for(let j=0;j<ny;j++)for(let i=0;i<nx;i++){const k=j*nx+i;if(!M[k]){U2[k]=1;V2[k]=0;continue;}let l=i>0?k-1:k,r=i<nx-1?k+1:k,u=j>0?k-nx:k,d=j<ny-1?k+nx:k;if(!M[l])l=k;if(!M[r])r=k;if(!M[u])u=k;if(!M[d])d=k;
      const lu=U[l]+U[r]+U[u]+U[d]-4*U[k],lv=V[l]+V[r]+V[u]+V[d]-4*V[k],uvv=U[k]*V[k]*V[k];U2[k]=U[k]+(0.2*lu-uvv+F[k]*(1-U[k]));V2[k]=V[k]+(0.1*lv+uvv-(F[k]+K[k])*V[k]);}
    U.set(U2);V.set(V2);}}
function rdOutline(){const{nx,ny,V,g}=RD,o=[],th=0.22;if(!V)return o;for(let j=0;j<ny-1;j++)for(let i=0;i<nx-1;i++){const c=[V[j*nx+i],V[j*nx+i+1],V[(j+1)*nx+i+1],V[(j+1)*nx+i]],x=(i+.5)*g,y=(j+.5)*g,P=[[x,y],[x+g,y],[x+g,y+g],[x,y+g]],pts=[];
  for(let e=0;e<4;e++){const a=c[e]-th,b=c[(e+1)%4]-th;if((a<0)!==(b<0)){const t=a/(a-b),A=P[e],B=P[(e+1)%4];pts.push([A[0]+(B[0]-A[0])*t,A[1]+(B[1]-A[1])*t]);}}
  for(let k=0;k+1<pts.length;k+=2)o.push({k:'seg',p:[pts[k],pts[k+1]],f:field(pts[k][0],pts[k][1]).f});}return o;}

// ---------- build + filter ----------
let built={shapes:[],dropped:0};
function shapeFits(sh){
  if(sh.k==='circ') return fitsPt(sh.x,sh.y,sh.r);
  if(sh.k==='seg') return true;
  const ex=sh.k==='line'?sh.w/2:0;for(const q of sh.p)if(!fitsPt(q[0],q[1],ex))return false;
  if(sh.k==='poly'){const c=centroid(sh.p);if(!inside(c[0],c[1]))return false;}
  return true;
}
function rebuild(){
  const P=PMAP[S.pattern];if(P.raster){if(!RD.U||RD.key!==S.s+'/'+S.seed){RD.key=S.s+'/'+S.seed;rdInit();}RD.dirty=true;built={shapes:[],dropped:0,raster:true};return;}
  const r=P.build(mulberry(S.seed));let shapes=r.shapes;
  if(r.grouped>1){const keep=[];for(let i=0;i<shapes.length;i+=r.grouped){const grp=shapes.slice(i,i+r.grouped);if(grp.every(shapeFits))keep.push(...grp);}shapes=keep;}
  else shapes=shapes.filter(shapeFits);
  if(S.fillet>0)shapes=shapes.map(sh=>sh.k==='poly'&&!sh.noRound?Object.assign({},sh,{p:fillet(sh.p,S.fillet)}):sh);
  built={shapes,dropped:r.dropped};
}

// ---------- colors ----------
// blue -> yellow -> orange -> red
const RAMP=[[0,[37,99,235]],[0.4,[250,204,21]],[0.7,[249,115,22]],[1,[220,38,38]]];
function ramp(f){f=clamp(f,0,1);for(let i=1;i<RAMP.length;i++){const[a,ca]=RAMP[i-1],[b,cb]=RAMP[i];if(f<=b){const t=(f-a)/(b-a);return ca.map((v,j)=>Math.round(lerp(v,cb[j],t)));}}return RAMP[RAMP.length-1][1].slice();}
const rgb=a=>`rgb(${a[0]},${a[1]},${a[2]})`;
const hex=a=>'#'+a.map(v=>v.toString(16).padStart(2,'0')).join('');
function facetColor(sh,useColor){const base=useColor?ramp(sh.f):[150,158,166];const k=0.35+0.85*sh.shade;return base.map(v=>Math.round(clamp(v*k,0,255)));}
function tracePoly(g,p,k){g.moveTo(p[0][0]*k,p[0][1]*k);for(let i=1;i<p.length;i++)g.lineTo(p[i][0]*k,p[i][1]*k);g.closePath();}
function renderScene(g,k,opts){
  const sheet=opts.sheet,hole=opts.hole;
  g.fillStyle=opts.metal;g.fillRect(0,0,PW*k,PH*k);
  // field: soft halo around the sheet plus a light tint inside, sampled every 8 mm and smoothed
  let fc=null;if(opts.field){const st=8,nx=PW/st+1,ny=Math.ceil(PH/st)+1,c=parseColor(opts.fieldColor),mk=()=>{const cc=document.createElement('canvas');cc.width=nx;cc.height=ny;return cc;};
    fc=mk();const fh=mk(),a=fc.getContext('2d').createImageData(nx,ny),h=fh.getContext('2d').createImageData(nx,ny);
    for(let j=0;j<ny;j++)for(let i=0;i<nx;i++){const f=clamp(field(i*st,j*st).f,0,1),e=clamp(Math.min(i*st,PW-i*st,j*st,PH-j*st)/60,0,1),o=(j*nx+i)*4;
      for(const d of[a,h]){d.data[o]=c[0];d.data[o+1]=c[1];d.data[o+2]=c[2];}a.data[o+3]=Math.round(f*255);h.data[o+3]=Math.round(f*e*e*255);}
    fc.getContext('2d').putImageData(a,0,0);fh.getContext('2d').putImageData(h,0,0);
    g.save();g.imageSmoothingEnabled=true;g.globalAlpha=0.16;g.drawImage(fh,-st/2*k,-st/2*k,nx*st*k,ny*st*k);g.restore();}
  g.beginPath();tracePoly(g,S.outline,k);g.fillStyle=sheet;g.fill();
  if(fc){const st=8;g.save();g.beginPath();tracePoly(g,S.outline,k);g.clip();g.imageSmoothingEnabled=true;g.globalAlpha=0.22;g.drawImage(fc,-st/2*k,-st/2*k,fc.width*st*k,fc.height*st*k);g.restore();}
  if(built.raster&&RD.V){const{nx,ny,V,M}=RD,oc=document.createElement('canvas');oc.width=nx;oc.height=ny;const oc2=oc.getContext('2d'),id=oc2.createImageData(nx,ny),hc=parseColor(hole);
    for(let i=0;i<nx*ny;i++){const on=M[i]&&V[i]>0.22;const c=on?(S.color?ramp(field(((i%nx)+.5)*RD.g,(Math.floor(i/nx)+.5)*RD.g).f):hc):null;id.data[i*4]=c?c[0]:0;id.data[i*4+1]=c?c[1]:0;id.data[i*4+2]=c?c[2]:0;id.data[i*4+3]=c?255:0;}
    oc2.putImageData(id,0,0);g.imageSmoothingEnabled=true;g.drawImage(oc,0,0,nx*RD.g*k,ny*RD.g*k);}
  for(const sh of built.shapes){
    const col=S.color?rgb(ramp(sh.f)):hole;
    if(sh.k==='circ'){g.beginPath();g.arc(sh.x*k,sh.y*k,sh.r*k,0,Math.PI*2);g.fillStyle=col;g.fill();}
    else if(sh.k==='poly'){g.beginPath();tracePoly(g,sh.p,k);g.fillStyle=col;g.fill();}
    else if(sh.k==='facet'){g.beginPath();tracePoly(g,sh.p,k);g.fillStyle=rgb(facetColor(sh,S.color));g.fill();g.strokeStyle='rgba(0,0,0,.25)';g.lineWidth=Math.max(0.5,0.15*k);g.stroke();}
    else if(sh.k==='line'){g.beginPath();g.moveTo(sh.p[0][0]*k,sh.p[0][1]*k);for(let i=1;i<sh.p.length;i++)g.lineTo(sh.p[i][0]*k,sh.p[i][1]*k);g.strokeStyle=col;g.lineWidth=sh.w*k;g.lineCap='round';g.lineJoin='round';g.stroke();}
  }
  for(const h of S.holes){g.beginPath();tracePoly(g,h.poly,k);g.fillStyle=opts.metal;g.fill();}
  g.beginPath();tracePoly(g,S.outline,k);for(const h of S.holes)tracePoly(g,h.poly,k);g.strokeStyle=opts.outlineColor;g.lineWidth=Math.max(1,0.6*k);g.stroke();
}
function parseColor(c){const d=document.createElement('canvas').getContext('2d');d.fillStyle=c;const v=d.fillStyle;if(v[0]==='#')return[1,3,5].map(i=>parseInt(v.slice(i,i+2),16));const m=v.match(/\d+/g);return m?m.slice(0,3).map(Number):[0,0,0];}// ---------- export ----------
// ---------- footprint mask (3D) ----------
// MASK: distance in mm from each cell to the edge of the model footprint (0 outside), at MASK.res mm per cell.
let MASK=null;
function maskAt(x,y){const M=MASK,i=Math.floor(x/M.res),j=Math.floor(y/M.res);if(i<0||j<0||i>=M.nx||j>=M.ny)return 0;return M.d[j*M.nx+i];}
function setMask(m){MASK=m;}
function setSheet(w,h){PW=w;PH=h;S.ctrl=[[0,0],[w,0],[w,h],[0,h]].map(p=>({p,sm:false}));buildOutline();
  img.width=Math.max(1,Math.round(w));img.height=Math.max(1,Math.round(h));if(userImage)drawImage(userImage);else defaultImage();}
function drawImage(im){userImage=im;const g=img.getContext('2d');g.fillStyle='#fff';g.fillRect(0,0,img.width,img.height);const sc=Math.max(img.width/im.width,img.height/im.height);
  g.drawImage(im,(img.width-im.width*sc)/2,(img.height-im.height*sc)/2,im.width*sc,im.height*sc);imgData=g.getImageData(0,0,img.width,img.height).data;}
return {S,PATTERNS,PMAP,field,rebuild,built:()=>built,renderScene,setSheet,setMask,drawImage,openCurve,fillet,clamp,lerp,ramp,mulberry,
  get PW(){return PW;},get PH(){return PH;}};
})();
