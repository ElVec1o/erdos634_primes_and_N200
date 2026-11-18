/-
Draft/WGapRung4.lean -- 16 November 2026 (work item LEAN_WGAP_2026-11-15, session 12).  UNAUDITED beyond internal checks.  Not imported by any aggregate.
Controls for `WGapRung.no_tiling_W_rung3`: (a) satisfiable instances with `M (f-e) = e + 3`; (b) the arithmetic hypotheses FAIL at every witnessed tiling
(data/witnesses/*_W_* plus W_4(2,3), W_3(2,5), W_4(3,5)); (c) agreement with `no_tiling_W_rung2` on a common instance.
-/
import Erdos634.Draft.WGapRung3
import Erdos634.Draft.WGapRung2

namespace Erdos634.Draft.WGapRung

/-- the full hypothesis list of `no_tiling_W_rung3` -/
def Rung3Hyp (e f M : ℕ) : Prop :=
  Nat.Coprime e f ∧ 2 ≤ e ∧ e < f ∧ f ≤ M * e ∧ M * (f - e) < f ∧ M * (f - e) ≤ e + 3

-- (a) satisfiable, with M (f - e) = e + 3 exactly (so rung 2 does not apply)
example : Rung3Hyp 5 9 2 := by unfold Rung3Hyp; decide
example : Rung3Hyp 7 12 2 := by unfold Rung3Hyp; decide
example : Rung3Hyp 9 13 3 := by unfold Rung3Hyp; decide
example : ¬ (2 * (9 - 5) ≤ 5 + 2) := by decide
example : ¬ (2 * (12 - 7) ≤ 7 + 2) := by decide
example : ¬ (3 * (13 - 9) ≤ 9 + 2) := by decide
theorem no_W_5_9_2 : ¬ Erdos634.Draft.CollarG.WTilable 5 9 2 :=
  no_tiling_W_rung3 5 9 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_7_12_2 : ¬ Erdos634.Draft.CollarG.WTilable 7 12 2 :=
  no_tiling_W_rung3 7 12 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_9_13_3 : ¬ Erdos634.Draft.CollarG.WTilable 9 13 3 :=
  no_tiling_W_rung3 9 13 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- (c) agreement with `no_tiling_W_rung2` on a common instance (8,13,2): both prove the same proposition
theorem agree_rung2_rung3 : (¬ Erdos634.Draft.CollarG.WTilable 8 13 2) ∧ (¬ Erdos634.Draft.CollarG.WTilable 8 13 2) :=
  ⟨no_tiling_W_rung2 8 13 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
   no_tiling_W_rung3 8 13 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

-- (b) the hypotheses fail at every witnessed tiling of W_M(e,f)
example : ¬ Rung3Hyp 2 3 4 := by unfold Rung3Hyp; decide
example : ¬ Rung3Hyp 10 21 4 := by unfold Rung3Hyp; decide  -- tile count 12512
example : ¬ Rung3Hyp 11 20 5 := by unfold Rung3Hyp; decide  -- tile count 16975
example : ¬ Rung3Hyp 13 20 6 := by unfold Rung3Hyp; decide  -- tile count 22716
example : ¬ Rung3Hyp 17 30 5 := by unfold Rung3Hyp; decide  -- tile count 37775
example : ¬ Rung3Hyp 19 40 3 := by unfold Rung3Hyp; decide  -- tile count 25551
example : ¬ Rung3Hyp 2 11 6 := by unfold Rung3Hyp; decide  -- tile count 8568
example : ¬ Rung3Hyp 2 15 8 := by unfold Rung3Hyp; decide  -- tile count 28544
example : ¬ Rung3Hyp 2 5 3 := by unfold Rung3Hyp; decide  -- tile count 414
example : ¬ Rung3Hyp 3 10 4 := by unfold Rung3Hyp; decide  -- tile count 3056
example : ¬ Rung3Hyp 3 16 6 := by unfold Rung3Hyp; decide  -- tile count 18108
example : ¬ Rung3Hyp 3 5 4 := by unfold Rung3Hyp; decide  -- tile count 656
example : ¬ Rung3Hyp 3 7 3 := by unfold Rung3Hyp; decide  -- tile count 801
example : ¬ Rung3Hyp 3 7 4 := by unfold Rung3Hyp; decide  -- tile count 1424
example : ¬ Rung3Hyp 3 8 3 := by unfold Rung3Hyp; decide  -- tile count 1071
example : ¬ Rung3Hyp 4 17 5 := by unfold Rung3Hyp; decide  -- tile count 14050
example : ¬ Rung3Hyp 4 7 4 := by unfold Rung3Hyp; decide  -- tile count 1312
example : ¬ Rung3Hyp 4 9 3 := by unfold Rung3Hyp; decide  -- tile count 1314
example : ¬ Rung3Hyp 5 11 3 := by unfold Rung3Hyp; decide  -- tile count 1953
example : ¬ Rung3Hyp 5 12 3 := by unfold Rung3Hyp; decide  -- tile count 2367
example : ¬ Rung3Hyp 5 17 4 := by unfold Rung3Hyp; decide  -- tile count 8848
example : ¬ Rung3Hyp 5 7 5 := by unfold Rung3Hyp; decide  -- tile count 1825
example : ¬ Rung3Hyp 5 8 4 := by unfold Rung3Hyp; decide  -- tile count 1648
example : ¬ Rung3Hyp 5 8 6 := by unfold Rung3Hyp; decide  -- tile count 3708
example : ¬ Rung3Hyp 5 9 4 := by unfold Rung3Hyp; decide  -- tile count 2192
example : ¬ Rung3Hyp 6 11 4 := by unfold Rung3Hyp; decide  -- tile count 3296
example : ¬ Rung3Hyp 6 19 4 := by unfold Rung3Hyp; decide  -- tile count 10976
example : ¬ Rung3Hyp 7 10 5 := by unfold Rung3Hyp; decide  -- tile count 3775
example : ¬ Rung3Hyp 7 11 4 := by unfold Rung3Hyp; decide  -- tile count 3088
example : ¬ Rung3Hyp 7 12 4 := by unfold Rung3Hyp; decide  -- tile count 3824
example : ¬ Rung3Hyp 7 13 13 := by unfold Rung3Hyp; decide  -- tile count 48841
example : ¬ Rung3Hyp 7 17 3 := by unfold Rung3Hyp; decide  -- tile count 4761
example : ¬ Rung3Hyp 7 9 6 := by unfold Rung3Hyp; decide  -- tile count 4068
example : ¬ Rung3Hyp 8 11 5 := by unfold Rung3Hyp; decide  -- tile count 4450
example : ¬ Rung3Hyp 8 13 4 := by unfold Rung3Hyp; decide  -- tile count 4384
example : ¬ Rung3Hyp 8 21 3 := by unfold Rung3Hyp; decide  -- tile count 7362
example : ¬ Rung3Hyp 9 11 7 := by unfold Rung3Hyp; decide  -- tile count 7889
example : ¬ Rung3Hyp 9 16 5 := by unfold Rung3Hyp; decide  -- tile count 10775

#print axioms no_W_5_9_2
#print axioms no_W_7_12_2
#print axioms no_W_9_13_3
#print axioms agree_rung2_rung3

end Erdos634.Draft.WGapRung
