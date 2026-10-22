# Attractor Patterns 3D

A browser playground that wraps attractor-driven perforation and texture patterns onto 3D models, then cuts, extrudes or recesses them and exports the result.

**Live page:** https://siatohi80.github.io/attractor-patterns-3d-site/

For flat sheets, use the 2D playground: https://siatohi80.github.io/attractor-patterns-site/

## How to use it

1. **Model:** open a STEP, IGES, BREP or Rhino 3DM file (surfaces, polysurfaces or solids), or an STL, OBJ, PLY or GLB mesh. You can also start from one of the samples.
2. **Faces:** click a face to put the pattern on it. Shift-click adds or removes faces, as long as the selection stays connected.
3. **Attractors:** place points and lines on the model. Line points can be made smooth to form a curve.
4. **Pattern:** choose a pattern family and set cell size, bridge, minimum hole and corner radius.
5. **Apply:** cut out, extrude or recess the openings to a set depth, then export as STL, OBJ, GLB or 3DM.

## Good to know

- Everything runs in your browser. Files are not uploaded anywhere.
- The pattern is projected onto the selected faces like a slide projector. Parts steeper than about 70° to the projection direction are left alone.
- Cutting a closed solid goes right through it along the projection direction.
- Exports are meshes, not NURBS surfaces.

This repo holds only the published page. It is updated from a separate development repo.
