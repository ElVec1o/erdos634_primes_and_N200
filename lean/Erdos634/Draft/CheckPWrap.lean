import Erdos634.Refl.CheckP

/-! # Refl.CheckP: reflective checker for 4-vertex (parallelogram) targets

`Refl.CheckP` extends `Refl.CheckR` to handle 4-vertex (parallelogram) target polygons.
It is the Lean-side infrastructure for parallelogram certificate files:
any NO_TILING result on a parallelogram target is verified by `InstP.checkAll` (exhaustive
search) or `InstP.checkAllR` (chunked/resumable variant).

The checker is intended to be sound in the same sense as `Refl.Check`: if `I.checkAll fuel tree = true`
then no `CongruentDissection` of the target parallelogram by the given tile exists.
The soundness proof for the parallelogram case, which mirrors `Refl.Sound`, is not formalized; it
needs the parallelogram-placement geometry, analogous to the triangular `SoundStage*` chain.

This wrapper compiles with no `sorry` and standard axioms.
-/

namespace Erdos634.Draft.CheckPWrap

-- Non-vacuity: the Quad structure is inhabited.
example : Erdos634.Refl.CheckP.Quad := ⟨⟨1,0,1⟩, ⟨1,1,1⟩, ⟨0,1,1⟩, ⟨0,0,1⟩⟩

-- The InstP structure is inhabited (trivial instance).
example : Erdos634.Refl.CheckP.InstP :=
  ⟨1, ⟨⟨1,0,1⟩, ⟨1,1,1⟩, ⟨0,1,1⟩, ⟨0,0,1⟩⟩, (1, 1, 1), []⟩

end Erdos634.Draft.CheckPWrap
