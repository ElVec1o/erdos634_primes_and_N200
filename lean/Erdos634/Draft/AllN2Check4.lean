/- Part of a split of the AllN2 checks into smaller modules (AllN2Check4). No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

theorem C'_87 : C' 87 := by decide +kernel
theorem not_tile'_87 (D : CongruentDissection 87) : False := not_tile_of_conditions' 87 C'_87 D
theorem C'_93 : C' 93 := by decide +kernel
theorem not_tile'_93 (D : CongruentDissection 93) : False := not_tile_of_conditions' 93 C'_93 D
theorem C'_111 : C' 111 := by decide +kernel
theorem not_tile'_111 (D : CongruentDissection 111) : False := not_tile_of_conditions' 111 C'_111 D
theorem C'_123 : C' 123 := by decide +kernel
theorem not_tile'_123 (D : CongruentDissection 123) : False := not_tile_of_conditions' 123 C'_123 D
theorem C'_129 : C' 129 := by decide +kernel
theorem not_tile'_129 (D : CongruentDissection 129) : False := not_tile_of_conditions' 129 C'_129 D
theorem C'_141 : C' 141 := by decide +kernel
theorem not_tile'_141 (D : CongruentDissection 141) : False := not_tile_of_conditions' 141 C'_141 D

end Erdos634.Draft.AllN2

#print axioms Erdos634.Draft.AllN2.not_tile'_87
