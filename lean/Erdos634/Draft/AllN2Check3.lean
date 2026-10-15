/- Part of a split of the AllN2 checks into smaller modules (AllN2Check3). No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry


example : leafVec' 159 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 165 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 177 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 183 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 195 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 201 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 213 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 219 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 235 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 237 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 249 = [true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
example : leafVec' 255 = [true, true, true, true, true, true, false, true, true, true, true, true] := by decide +kernel
example : leafVec' 285 = [true, true, true, true, true, true, false, true, true, true, true, true] := by decide +kernel
example : leafVec' 385 = [true, true, true, true, true, true, false, false, true, true, true, true] := by decide +kernel
example : leafVec' 455 = [true, true, true, true, true, true, false, true, true, true, true, true] := by decide +kernel

end Erdos634.Draft.AllN2


