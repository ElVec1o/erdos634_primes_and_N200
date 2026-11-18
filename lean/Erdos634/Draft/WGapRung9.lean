/-
Draft/WGapRung9.lean -- 16 November 2026 (work item LEAN_WGAP_2026-11-15, session 17).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  Leaf module.
Controls for the UNCONDITIONAL `WGapRung.no_tiling_W_gap` (WGapStation4): (a) its full hypothesis list is satisfiable far beyond rung 5 (`M (f-e) - e` = 8, 20, 21, 100), and the theorem applies there;
(b) the hypothesis list FAILS at the three Lean-kernel `WTilable` instances of WGapRung6b and at every witnessed tiling of the WGapRung6 list (including `W_4(2,3)`, `W_3(2,5)`, `W_4(3,5)`);
(c) agreement with `no_tiling_W_rung5` / `no_tiling_W_rung4` on common instances.
-/
import Erdos634.Draft.WGapStation4
import Erdos634.Draft.WGapRung8

namespace Erdos634.Draft.WGapRung

open Erdos634.Draft.CollarG

/-- the full hypothesis list of `no_tiling_W_gap` -/
def GapHyp (e f M : ℕ) : Prop :=
  Nat.Coprime e f ∧ 2 ≤ e ∧ e < f ∧ f ≤ M * e ∧ M * (f - e) < f

theorem gap_applied (e f M : ℕ) (h : GapHyp e f M) : ¬ WTilable e f M :=
  no_tiling_W_gap e f M h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

-- (a) satisfiable beyond rung 5 (M (f-e) - e = 8, 20, 21, 100): rung 5 does not apply
example : GapHyp 10 19 2 ∧ ¬ RungHyp 5 10 19 2 := by unfold GapHyp RungHyp; decide
example : GapHyp 22 43 2 ∧ ¬ RungHyp 5 22 43 2 := by unfold GapHyp RungHyp; decide    -- N = 12856
example : GapHyp 23 45 2 ∧ ¬ RungHyp 5 23 45 2 := by unfold GapHyp RungHyp; decide    -- N = 14084
example : GapHyp 102 203 2 ∧ ¬ RungHyp 5 102 203 2 := by unfold GapHyp RungHyp; decide -- N = 288056
theorem no_W_10_19_2 : ¬ WTilable 10 19 2 := gap_applied 10 19 2 (by unfold GapHyp; decide)
theorem no_W_22_43_2 : ¬ WTilable 22 43 2 := gap_applied 22 43 2 (by unfold GapHyp; decide)
theorem no_W_23_45_2 : ¬ WTilable 23 45 2 := gap_applied 23 45 2 (by unfold GapHyp; decide)
theorem no_W_102_203_2 : ¬ WTilable 102 203 2 := gap_applied 102 203 2 (by unfold GapHyp; decide)

-- (c) agreement with the rung theorems on common instances
theorem agree_gap_rung5 : (¬ WTilable 9 16 2) ∧ (¬ WTilable 9 16 2) ∧ (¬ WTilable 9 13 3) ∧ (¬ WTilable 9 13 3) :=
  ⟨no_tiling_W_rung5 9 16 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
   gap_applied 9 16 2 (by unfold GapHyp; decide),
   no_tiling_W_rung4 9 13 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
   gap_applied 9 13 3 (by unfold GapHyp; decide)⟩

-- (b) the hypothesis list fails at the three Lean-kernel WTilable instances of WGapRung6b
example : ¬ GapHyp 2 3 3 := by unfold GapHyp; decide
example : ¬ GapHyp 6 11 11 := by unfold GapHyp; decide
example : ¬ GapHyp 6 11 17 := by unfold GapHyp; decide
-- and at every witnessed tiling of the WGapRung6 list
example : ¬ GapHyp 2 3 4 := by unfold GapHyp; decide 
example : ¬ GapHyp 10 21 4 := by unfold GapHyp; decide  -- tile count 12512
example : ¬ GapHyp 11 20 5 := by unfold GapHyp; decide  -- tile count 16975
example : ¬ GapHyp 13 20 6 := by unfold GapHyp; decide  -- tile count 22716
example : ¬ GapHyp 17 30 5 := by unfold GapHyp; decide  -- tile count 37775
example : ¬ GapHyp 19 40 3 := by unfold GapHyp; decide  -- tile count 25551
example : ¬ GapHyp 2 11 6 := by unfold GapHyp; decide  -- tile count 8568
example : ¬ GapHyp 2 15 8 := by unfold GapHyp; decide  -- tile count 28544
example : ¬ GapHyp 2 5 3 := by unfold GapHyp; decide  -- tile count 414
example : ¬ GapHyp 3 10 4 := by unfold GapHyp; decide  -- tile count 3056
example : ¬ GapHyp 3 16 6 := by unfold GapHyp; decide  -- tile count 18108
example : ¬ GapHyp 3 5 4 := by unfold GapHyp; decide  -- tile count 656
example : ¬ GapHyp 3 7 3 := by unfold GapHyp; decide  -- tile count 801
example : ¬ GapHyp 3 7 4 := by unfold GapHyp; decide  -- tile count 1424
example : ¬ GapHyp 3 8 3 := by unfold GapHyp; decide  -- tile count 1071
example : ¬ GapHyp 4 17 5 := by unfold GapHyp; decide  -- tile count 14050
example : ¬ GapHyp 4 7 4 := by unfold GapHyp; decide  -- tile count 1312
example : ¬ GapHyp 4 9 3 := by unfold GapHyp; decide  -- tile count 1314
example : ¬ GapHyp 5 11 3 := by unfold GapHyp; decide  -- tile count 1953
example : ¬ GapHyp 5 12 3 := by unfold GapHyp; decide  -- tile count 2367
example : ¬ GapHyp 5 17 4 := by unfold GapHyp; decide  -- tile count 8848
example : ¬ GapHyp 5 7 5 := by unfold GapHyp; decide  -- tile count 1825
example : ¬ GapHyp 5 8 4 := by unfold GapHyp; decide  -- tile count 1648
example : ¬ GapHyp 5 8 6 := by unfold GapHyp; decide  -- tile count 3708
example : ¬ GapHyp 5 9 4 := by unfold GapHyp; decide  -- tile count 2192
example : ¬ GapHyp 6 11 4 := by unfold GapHyp; decide  -- tile count 3296
example : ¬ GapHyp 6 19 4 := by unfold GapHyp; decide  -- tile count 10976
example : ¬ GapHyp 7 10 5 := by unfold GapHyp; decide  -- tile count 3775
example : ¬ GapHyp 7 11 4 := by unfold GapHyp; decide  -- tile count 3088
example : ¬ GapHyp 7 12 4 := by unfold GapHyp; decide  -- tile count 3824
example : ¬ GapHyp 7 13 13 := by unfold GapHyp; decide  -- tile count 48841
example : ¬ GapHyp 7 17 3 := by unfold GapHyp; decide  -- tile count 4761
example : ¬ GapHyp 7 9 6 := by unfold GapHyp; decide  -- tile count 4068
example : ¬ GapHyp 8 11 5 := by unfold GapHyp; decide  -- tile count 4450
example : ¬ GapHyp 8 13 4 := by unfold GapHyp; decide  -- tile count 4384
example : ¬ GapHyp 8 21 3 := by unfold GapHyp; decide  -- tile count 7362
example : ¬ GapHyp 9 11 7 := by unfold GapHyp; decide  -- tile count 7889
example : ¬ GapHyp 9 16 5 := by unfold GapHyp; decide  -- tile count 10775

#print axioms gap_applied
#print axioms no_W_10_19_2
#print axioms no_W_22_43_2
#print axioms no_W_23_45_2
#print axioms no_W_102_203_2
#print axioms agree_gap_rung5

end Erdos634.Draft.WGapRung
