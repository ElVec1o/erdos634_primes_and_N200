/- Split of AllN2Check5 (one file exceeded 10 min). AllN2Check5: N=159. No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

theorem C'_159 : C' 159 := by decide +kernel
theorem not_tile'_159 (D : CongruentDissection 159) : False := not_tile_of_conditions' 159 C'_159 D

end Erdos634.Draft.AllN2

#print axioms Erdos634.Draft.AllN2.not_tile'_159
