/-
Draft/PI3HArithWindow.lean -- the WINDOW of the pi/3 strip/level/T2 analysis, by kernel `decide`.

`window_eq`  : the odd squarefree N <= 10^4 having an x-type pair uncovered by Theorem T (l_kappa <= 2N) are exactly the 52 numbers
               of `windowList`.  10 chunks of 1000, one `decide +kernel` each.
`window_pre` : for each of the 52 N, every uncovered x-type pair satisfies the standing conditions C1-C8 (`xPre`), in particular
               g = 6, Delta > x, Delta_c > x, Delta_c - Delta = x, Delta + Delta_c odd, N < l_kappa <= 2N, C8.
`window_pairs_card` : the 52 N carry exactly 52 such pairs (one each).
Controls: N = 1440 (even; D square for (120,36)) is not in the window; N = 87 not in the window (Theorem T-covered).  No sorry, no native_decide.
-/
import Erdos634.Draft.PI3HArithDefs

namespace Erdos634.Draft.PI3H

/-- the 52 N. -/
def windowList : List ℕ :=
  [255, 285, 483, 609, 1155, 1221, 1353, 1419, 1599, 1677,
    1833, 2067, 2145, 2703, 2805, 3009, 3111, 3315, 3363, 3417,
    3477, 3621, 3705, 3819, 4047, 4161, 4389, 4503, 4899, 5037,
    5313, 5451, 5727, 5865, 6141, 6279, 6555, 6693, 7743, 7917,
    8265, 8439, 8787, 8835, 8961, 9021, 9309, 9393, 9483, 9579,
    9831, 9951]

theorem window_chunk0 : ((List.range' 0 1000).filter inWindow) = [255, 285, 483, 609] := by decide +kernel
theorem window_chunk1 : ((List.range' 1000 1000).filter inWindow) = [1155, 1221, 1353, 1419, 1599, 1677, 1833] := by decide +kernel
theorem window_chunk2 : ((List.range' 2000 1000).filter inWindow) = [2067, 2145, 2703, 2805] := by decide +kernel
theorem window_chunk3 : ((List.range' 3000 1000).filter inWindow) = [3009, 3111, 3315, 3363, 3417, 3477, 3621, 3705, 3819] := by decide +kernel
theorem window_chunk4 : ((List.range' 4000 1000).filter inWindow) = [4047, 4161, 4389, 4503, 4899] := by decide +kernel
theorem window_chunk5 : ((List.range' 5000 1000).filter inWindow) = [5037, 5313, 5451, 5727, 5865] := by decide +kernel
theorem window_chunk6 : ((List.range' 6000 1000).filter inWindow) = [6141, 6279, 6555, 6693] := by decide +kernel
theorem window_chunk7 : ((List.range' 7000 1000).filter inWindow) = [7743, 7917] := by decide +kernel
theorem window_chunk8 : ((List.range' 8000 1000).filter inWindow) = [8265, 8439, 8787, 8835, 8961] := by decide +kernel
theorem window_chunk9 : ((List.range' 9000 1001).filter inWindow) = [9021, 9309, 9393, 9483, 9579, 9831, 9951] := by decide +kernel

theorem range_split : List.range 10001 = List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1001 := by decide +kernel

/-- **The window.** -/
theorem window_eq : (List.range 10001).filter inWindow = windowList := by
  rw [range_split]
  simp only [List.filter_append]
  rw [window_chunk0, window_chunk1, window_chunk2, window_chunk3, window_chunk4, window_chunk5, window_chunk6, window_chunk7, window_chunk8, window_chunk9] 
  decide +kernel

theorem window_card : ((List.range 10001).filter inWindow).length = 52 := by rw [window_eq]; decide +kernel

/-- the standing arithmetic conditions C1-C8 for every uncovered x-type pair of the window. -/
theorem window_pre : windowList.all (fun N => (xList N).all fun x => xPre N x) = true := by decide +kernel

/-- each window N carries exactly one uncovered x-type pair. -/
theorem window_pairs_card : windowList.all (fun N => (xList N).length == 1) = true := by decide +kernel

/-- Controls. -/
theorem ctl_1440_not_window : inWindow 1440 = false := by decide +kernel
theorem ctl_87_not_window : inWindow 87 = false := by decide +kernel
/-- N = 1440, pair (120, 36): D = 36^2 is a square, so the pair is outside the class (`xUnc` fails). -/
theorem ctl_1440_square : isSq ((120 + 36) * (120 + 36) - 16 * 1440) = true ∧ xUnc 1440 12 = false := by
  constructor <;> decide +kernel

end Erdos634.Draft.PI3H

#print axioms Erdos634.Draft.PI3H.window_eq
#print axioms Erdos634.Draft.PI3H.window_card
#print axioms Erdos634.Draft.PI3H.window_pre
#print axioms Erdos634.Draft.PI3H.window_pairs_card
#print axioms Erdos634.Draft.PI3H.ctl_1440_square
