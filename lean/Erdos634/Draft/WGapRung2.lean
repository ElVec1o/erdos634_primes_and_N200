/-
Draft/WGapRung2.lean -- 16 November 2026 (work item LEAN_WRUNG2_2026-11-16).  UNAUDITED beyond internal checks.  Not imported by any aggregate.
Controls for `WGapRung.no_tiling_W_rung2`: (a) satisfiable instances; (b) the arithmetic hypotheses FAIL at every witnessed tiling
(data/witnesses/*_W_* plus W_4(2,3)), so the theorem is not vacuous against a real tiling; (c) agreement with `SplusThick.wTilable_not_of_small_M`.
-/
import Erdos634.Draft.WGapRung1
import Erdos634.Draft.SplusThickFinal

namespace Erdos634.Draft.WGapRung

/-- the full hypothesis list of `no_tiling_W_rung2` -/
def Rung2Hyp (e f M : ℕ) : Prop :=
  Nat.Coprime e f ∧ 2 ≤ e ∧ e < f ∧ f ≤ M * e ∧ M * (f - e) < f ∧ M * (f - e) ≤ e + 2

-- (a) satisfiable: the hypotheses hold and the conclusion is obtained
example : Rung2Hyp 8 13 2 := by unfold Rung2Hyp; decide
example : Rung2Hyp 7 10 3 := by unfold Rung2Hyp; decide
example : Rung2Hyp 4 7 2 := by unfold Rung2Hyp; decide
theorem no_W_2_8_13 : ¬ Erdos634.Draft.CollarG.WTilable 8 13 2 :=
  no_tiling_W_rung2 8 13 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_3_7_10 : ¬ Erdos634.Draft.CollarG.WTilable 7 10 3 :=
  no_tiling_W_rung2 7 10 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_2_4_7 : ¬ Erdos634.Draft.CollarG.WTilable 4 7 2 :=
  no_tiling_W_rung2 4 7 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- (c) agreement with the existing theorem (M (f-e) <= e+1) on a common instance (5,8,2): both prove the same proposition
theorem agree_5_8_2 : (¬ Erdos634.Draft.CollarG.WTilable 5 8 2) ∧ (¬ Erdos634.Draft.CollarG.WTilable 5 8 2) :=
  ⟨no_tiling_W_rung2 5 8 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
   Erdos634.Draft.SplusThick.wTilable_not_of_small_M (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

-- (b) the hypotheses fail at every witnessed tiling of W_M(e,f)
example : ¬ Rung2Hyp 2 3 4 := by unfold Rung2Hyp; decide
example : ¬ Rung2Hyp 10 21 4 := by unfold Rung2Hyp; decide  -- tile count 12512
example : ¬ Rung2Hyp 11 20 5 := by unfold Rung2Hyp; decide  -- tile count 16975
example : ¬ Rung2Hyp 13 20 6 := by unfold Rung2Hyp; decide  -- tile count 22716
example : ¬ Rung2Hyp 17 30 5 := by unfold Rung2Hyp; decide  -- tile count 37775
example : ¬ Rung2Hyp 19 40 3 := by unfold Rung2Hyp; decide  -- tile count 25551
example : ¬ Rung2Hyp 2 11 6 := by unfold Rung2Hyp; decide  -- tile count 8568
example : ¬ Rung2Hyp 2 15 8 := by unfold Rung2Hyp; decide  -- tile count 28544
example : ¬ Rung2Hyp 2 5 3 := by unfold Rung2Hyp; decide  -- tile count 414
example : ¬ Rung2Hyp 3 10 4 := by unfold Rung2Hyp; decide  -- tile count 3056
example : ¬ Rung2Hyp 3 16 6 := by unfold Rung2Hyp; decide  -- tile count 18108
example : ¬ Rung2Hyp 3 5 4 := by unfold Rung2Hyp; decide  -- tile count 656
example : ¬ Rung2Hyp 3 7 3 := by unfold Rung2Hyp; decide  -- tile count 801
example : ¬ Rung2Hyp 3 7 4 := by unfold Rung2Hyp; decide  -- tile count 1424
example : ¬ Rung2Hyp 3 8 3 := by unfold Rung2Hyp; decide  -- tile count 1071
example : ¬ Rung2Hyp 4 17 5 := by unfold Rung2Hyp; decide  -- tile count 14050
example : ¬ Rung2Hyp 4 7 4 := by unfold Rung2Hyp; decide  -- tile count 1312
example : ¬ Rung2Hyp 4 9 3 := by unfold Rung2Hyp; decide  -- tile count 1314
example : ¬ Rung2Hyp 5 11 3 := by unfold Rung2Hyp; decide  -- tile count 1953
example : ¬ Rung2Hyp 5 12 3 := by unfold Rung2Hyp; decide  -- tile count 2367
example : ¬ Rung2Hyp 5 17 4 := by unfold Rung2Hyp; decide  -- tile count 8848
example : ¬ Rung2Hyp 5 7 5 := by unfold Rung2Hyp; decide  -- tile count 1825
example : ¬ Rung2Hyp 5 8 4 := by unfold Rung2Hyp; decide  -- tile count 1648
example : ¬ Rung2Hyp 5 8 6 := by unfold Rung2Hyp; decide  -- tile count 3708
example : ¬ Rung2Hyp 5 9 4 := by unfold Rung2Hyp; decide  -- tile count 2192
example : ¬ Rung2Hyp 6 11 4 := by unfold Rung2Hyp; decide  -- tile count 3296
example : ¬ Rung2Hyp 6 19 4 := by unfold Rung2Hyp; decide  -- tile count 10976
example : ¬ Rung2Hyp 7 10 5 := by unfold Rung2Hyp; decide  -- tile count 3775
example : ¬ Rung2Hyp 7 11 4 := by unfold Rung2Hyp; decide  -- tile count 3088
example : ¬ Rung2Hyp 7 12 4 := by unfold Rung2Hyp; decide  -- tile count 3824
example : ¬ Rung2Hyp 7 13 13 := by unfold Rung2Hyp; decide  -- tile count 48841
example : ¬ Rung2Hyp 7 17 3 := by unfold Rung2Hyp; decide  -- tile count 4761
example : ¬ Rung2Hyp 7 9 6 := by unfold Rung2Hyp; decide  -- tile count 4068
example : ¬ Rung2Hyp 8 11 5 := by unfold Rung2Hyp; decide  -- tile count 4450
example : ¬ Rung2Hyp 8 13 4 := by unfold Rung2Hyp; decide  -- tile count 4384
example : ¬ Rung2Hyp 8 21 3 := by unfold Rung2Hyp; decide  -- tile count 7362
example : ¬ Rung2Hyp 9 11 7 := by unfold Rung2Hyp; decide  -- tile count 7889
example : ¬ Rung2Hyp 9 16 5 := by unfold Rung2Hyp; decide  -- tile count 10775

#print axioms no_W_2_8_13
#print axioms no_W_3_7_10
#print axioms no_W_2_4_7
#print axioms agree_5_8_2

end Erdos634.Draft.WGapRung
