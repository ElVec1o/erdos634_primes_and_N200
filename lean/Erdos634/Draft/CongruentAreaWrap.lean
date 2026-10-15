import Erdos634.CongruentArea

/-!
# CongruentArea: area preservation under congruence, wrapper

Key results:
- `volume_congruent`: congruent triangles have equal area
- `congruentDissection_volume_target`: area of target = N × area of model (prop:dissection)
- `measurePreserving_isometryEquiv`: isometries preserve Lebesgue measure

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CongruentAreaWrap

open Erdos634.CongruentArea Erdos634.Geometry MeasureTheory
open scoped ENNReal

variable {N : ℕ}

theorem ca_volume_congruent {T U : Tri} (h : T.Congruent U) :
    volume T.carrier = volume U.carrier :=
  volume_congruent h

theorem ca_congruentDissection_volume_target (D : CongruentDissection N) :
    volume D.target.carrier = (N : ℝ≥0∞) * volume D.model.carrier :=
  congruentDissection_volume_target D

theorem ca_measurePreserving_isometryEquiv (f : Plane ≃ᵢ Plane) :
    MeasurePreserving f volume volume :=
  measurePreserving_isometryEquiv f

-- Non-vacuity: refl congruence gives equal area
example (T : Tri) : volume T.carrier = volume T.carrier :=
  ca_volume_congruent (Tri.Congruent.refl T)

#print axioms ca_congruentDissection_volume_target

end Erdos634.Draft.CongruentAreaWrap
