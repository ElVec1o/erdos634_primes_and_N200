import Erdos634.Congruence
import Erdos634.CongruentAngles
import Erdos634.CongruentArea
import Erdos634.SssCongruent

/-!
# Congruence: SSS congruence and its corollaries, wrapper

Key results:
- `Tri.Congruent` is an equivalence relation (refl, symm, trans)
- `congruent_corner_angles`: congruent triangles have equal corner angles
- `congruent_edge_lengths`: congruent triangles have equal edge lengths
- `volume_congruent`: congruent triangles have equal area
- `sss_congruent`: SSS criterion for triangle congruence

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CongruenceWrap

open Erdos634.Geometry Erdos634.CongruentArea MeasureTheory

theorem cong_refl (T : Tri) : T.Congruent T := Tri.Congruent.refl T

theorem cong_symm {T U : Tri} (h : T.Congruent U) : U.Congruent T := h.symm

theorem cong_trans {T U V : Tri} (h₁ : T.Congruent U) (h₂ : U.Congruent V) :
    T.Congruent V := h₁.trans h₂

theorem cong_corner_angles {T U : Tri} (h : T.Congruent U) (j : Fin 3) :
    ∃ k : Fin 3, cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) =
      cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) :=
  congruent_corner_angles h j

theorem cong_volume {T U : Tri} (h : T.Congruent U) :
    volume T.carrier = volume U.carrier :=
  volume_congruent h

-- Non-vacuity: any triangle is congruent to itself
example (T : Tri) : T.Congruent T := cong_refl T

#print axioms cong_refl
#print axioms cong_corner_angles
#print axioms cong_volume

end Erdos634.Draft.CongruenceWrap
