-- N15IsoALift.lean — lift of the certified tree `N15IsoA.node_0` to arbitrary congruent target/model:
-- no dissection whose target is congruent to the (60,60,15) triangle `TGT` and whose model is congruent
-- to the (4,15,16) tile `MODEL` exists (N free).
import Erdos634.N15IsoA
import Erdos634.NormalPosition

namespace Erdos634.N15IsoA
open Erdos634.Geometry

theorem not_dissection {N : ℕ} (D : CongruentDissection N)
    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False := by
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT
  exact node_0 D' (by rw [hD'T]) (by rw [hD'M]; exact hM)

end Erdos634.N15IsoA

#print axioms Erdos634.N15IsoA.not_dissection
