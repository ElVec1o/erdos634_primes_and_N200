import Erdos634.ChordFinsetInvariant
namespace Erdos634.Draft.ChordFinsetInvariantWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_excl_new_self {P s : Plane} : Wbtw ℝ P s s :=
  excl_new_self

theorem wrap_excl_carries_forward {P p r s Sk : Plane}
    (hold : Wbtw ℝ P Sk p) (hle : Wbtw ℝ P p r) (hrs : Wbtw ℝ P r s) :
    Wbtw ℝ P Sk s :=
  excl_carries_forward hold hle hrs

example : True := trivial
#print axioms excl_carries_forward
end Erdos634.Draft.ChordFinsetInvariantWrap
