-- `GapIsoSporadic33` holds with no hypothesis: the reduction `SIXIso33.iso33_scaled` (tile (5,3,7), target (21,21,33)) plus the certified
-- refutation tree (`Refl.SIXBridgeI33.not_dissection_sides`, 11252 nodes, kernel `decide`), and `chain_33_final'`.
import Erdos634.Draft.SIXIso33
import Erdos634.Draft.SIXBridgeI33
import Erdos634.Draft.CompositeFinal12

namespace Erdos634.Draft.SIXF33

open Erdos634.Geometry Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeFinal12

theorem iso33 : GapIsoSporadic33 := by
  intro D α a b c hα hm hiso
  obtain ⟨D', ⟨σ, h0, h1, h2⟩, ⟨τ, m0, m1, m2⟩⟩ := SIXIso33.iso33_scaled D α a b c hα hm hiso
  exact Refl.SIXBridgeI33.not_dissection_sides D' σ τ h0 h1 h2 m0 m1 m2

/-- `33` is not a tile count: hypothesis-free. -/
theorem chain_33_final' (D : CongruentDissection 33) : False :=
  chain_33_final iso33 D

end Erdos634.Draft.SIXF33

#print axioms Erdos634.Draft.SIXF33.iso33
#print axioms Erdos634.Draft.SIXF33.chain_33_final'
