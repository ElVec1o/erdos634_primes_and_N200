import Erdos634.NormalPosition

namespace Erdos634.Draft.NormalPositionWrap
open Erdos634.Geometry Erdos634.NormalPosition

theorem wrap_exists_normal_position_congruent {N : ℕ} (D : CongruentDissection N) {U : Tri}
    (h : D.target.Congruent U) :
    ∃ (g : Plane ≃ᵢ Plane) (D' : CongruentDissection N),
      D'.target = U ∧ D'.model = D.model ∧
      ∀ i m, (D'.tile i).pts m = g ((D.tile i).pts m) :=
  exists_normal_position_congruent D h

example : True := trivial
#print axioms wrap_exists_normal_position_congruent

end Erdos634.Draft.NormalPositionWrap
