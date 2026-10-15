/-
Draft/N15Final.lean -- N = 15 without further hypotheses: `not_tile_15 : CongruentDissection 15 → False`.
  chain_fifteen7 (A2 : GapA2) : the Chain15 dispatch with GapA (via GapA2 + lemmaH15_holds), GapE60 (FluxCRow5N15),
  GapE120 (GapE120Dis, reflective certificate), GapF1 (f1_free_Ma1 + F1c4aSide.gapF1_c4a_holds), GapR8 (R8N15*), all discharged;
  the single leaf GapA2 is supplied by GA2WZ.gapA2_full.
  Composite N = 15.  No sorry, no native_decide.
-/
import Erdos634.Draft.GapE120Dis
import Erdos634.Draft.GA2WZ

namespace Erdos634.Draft.N15Final
open Erdos634.Geometry

/-- **N = 15: no residual hypothesis.** -/
theorem not_tile_15 (D : CongruentDissection 15) : False :=
  Erdos634.Geometry.GapE120Dis.chain_fifteen7 Erdos634.GA2WZ.gapA2_full D

theorem not_tile_15' : ¬ Nonempty (CongruentDissection 15) := fun ⟨D⟩ => not_tile_15 D

end Erdos634.Draft.N15Final

#print axioms Erdos634.Draft.N15Final.not_tile_15
