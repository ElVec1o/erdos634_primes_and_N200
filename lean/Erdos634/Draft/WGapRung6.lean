/-
Draft/WGapRung6.lean -- 16 November 2026 (work item LEAN_WGAP_2026-11-15, session 14).  UNAUDITED beyond internal checks.  Not imported by any aggregate.
Controls for `WGapRung.no_tiling_W_rung4`: (a) satisfiable instances with `M (f-e) = e + 4` (so rung 3 does not apply), among them `(6,11,2)` (N = 824, an open value below 1000);
(b) the arithmetic hypotheses FAIL at every witnessed tiling (data/witnesses/*_W_* plus W_4(2,3), W_3(2,5), W_4(3,5)); (c) agreement with `no_tiling_W_rung3` on a common instance.
-/
import Erdos634.Draft.WGapRung5
import Erdos634.Draft.WGapRung4

namespace Erdos634.Draft.WGapRung

/-- the full hypothesis list of `no_tiling_W_rung4` -/
def Rung4Hyp (e f M : ℕ) : Prop :=
  Nat.Coprime e f ∧ 2 ≤ e ∧ e < f ∧ f ≤ M * e ∧ M * (f - e) < f ∧ M * (f - e) ≤ e + 4

-- (a) satisfiable, with M (f - e) = e + 4 exactly (so rung 3 does not apply)
example : Rung4Hyp 6 11 2 := by unfold Rung4Hyp; decide   -- N = 824
example : Rung4Hyp 11 16 3 := by unfold Rung4Hyp; decide  -- N = 3519
example : Rung4Hyp 10 17 2 := by unfold Rung4Hyp; decide  -- N = 1912
example : ¬ (2 * (11 - 6) ≤ 6 + 3) := by decide
example : ¬ (3 * (16 - 11) ≤ 11 + 3) := by decide
example : ¬ (2 * (17 - 10) ≤ 10 + 3) := by decide
theorem no_W_6_11_2 : ¬ Erdos634.Draft.CollarG.WTilable 6 11 2 :=
  no_tiling_W_rung4 6 11 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_11_16_3 : ¬ Erdos634.Draft.CollarG.WTilable 11 16 3 :=
  no_tiling_W_rung4 11 16 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_10_17_2 : ¬ Erdos634.Draft.CollarG.WTilable 10 17 2 :=
  no_tiling_W_rung4 10 17 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- (c) agreement with `no_tiling_W_rung3` on a common instance (9,13,3): M (f-e) = 12 = e + 3
theorem agree_rung3_rung4 : (¬ Erdos634.Draft.CollarG.WTilable 9 13 3) ∧ (¬ Erdos634.Draft.CollarG.WTilable 9 13 3) :=
  ⟨no_tiling_W_rung3 9 13 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
   no_tiling_W_rung4 9 13 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

-- (b) the hypotheses fail at every witnessed tiling of W_M(e,f)
example : ¬ Rung4Hyp 2 3 4 := by unfold Rung4Hyp; decide
example : ¬ Rung4Hyp 10 21 4 := by unfold Rung4Hyp; decide  -- tile count 12512
example : ¬ Rung4Hyp 11 20 5 := by unfold Rung4Hyp; decide  -- tile count 16975
example : ¬ Rung4Hyp 13 20 6 := by unfold Rung4Hyp; decide  -- tile count 22716
example : ¬ Rung4Hyp 17 30 5 := by unfold Rung4Hyp; decide  -- tile count 37775
example : ¬ Rung4Hyp 19 40 3 := by unfold Rung4Hyp; decide  -- tile count 25551
example : ¬ Rung4Hyp 2 11 6 := by unfold Rung4Hyp; decide  -- tile count 8568
example : ¬ Rung4Hyp 2 15 8 := by unfold Rung4Hyp; decide  -- tile count 28544
example : ¬ Rung4Hyp 2 5 3 := by unfold Rung4Hyp; decide  -- tile count 414
example : ¬ Rung4Hyp 3 10 4 := by unfold Rung4Hyp; decide  -- tile count 3056
example : ¬ Rung4Hyp 3 16 6 := by unfold Rung4Hyp; decide  -- tile count 18108
example : ¬ Rung4Hyp 3 5 4 := by unfold Rung4Hyp; decide  -- tile count 656
example : ¬ Rung4Hyp 3 7 3 := by unfold Rung4Hyp; decide  -- tile count 801
example : ¬ Rung4Hyp 3 7 4 := by unfold Rung4Hyp; decide  -- tile count 1424
example : ¬ Rung4Hyp 3 8 3 := by unfold Rung4Hyp; decide  -- tile count 1071
example : ¬ Rung4Hyp 4 17 5 := by unfold Rung4Hyp; decide  -- tile count 14050
example : ¬ Rung4Hyp 4 7 4 := by unfold Rung4Hyp; decide  -- tile count 1312
example : ¬ Rung4Hyp 4 9 3 := by unfold Rung4Hyp; decide  -- tile count 1314
example : ¬ Rung4Hyp 5 11 3 := by unfold Rung4Hyp; decide  -- tile count 1953
example : ¬ Rung4Hyp 5 12 3 := by unfold Rung4Hyp; decide  -- tile count 2367
example : ¬ Rung4Hyp 5 17 4 := by unfold Rung4Hyp; decide  -- tile count 8848
example : ¬ Rung4Hyp 5 7 5 := by unfold Rung4Hyp; decide  -- tile count 1825
example : ¬ Rung4Hyp 5 8 4 := by unfold Rung4Hyp; decide  -- tile count 1648
example : ¬ Rung4Hyp 5 8 6 := by unfold Rung4Hyp; decide  -- tile count 3708
example : ¬ Rung4Hyp 5 9 4 := by unfold Rung4Hyp; decide  -- tile count 2192
example : ¬ Rung4Hyp 6 11 4 := by unfold Rung4Hyp; decide  -- tile count 3296
example : ¬ Rung4Hyp 6 19 4 := by unfold Rung4Hyp; decide  -- tile count 10976
example : ¬ Rung4Hyp 7 10 5 := by unfold Rung4Hyp; decide  -- tile count 3775
example : ¬ Rung4Hyp 7 11 4 := by unfold Rung4Hyp; decide  -- tile count 3088
example : ¬ Rung4Hyp 7 12 4 := by unfold Rung4Hyp; decide  -- tile count 3824
example : ¬ Rung4Hyp 7 13 13 := by unfold Rung4Hyp; decide  -- tile count 48841
example : ¬ Rung4Hyp 7 17 3 := by unfold Rung4Hyp; decide  -- tile count 4761
example : ¬ Rung4Hyp 7 9 6 := by unfold Rung4Hyp; decide  -- tile count 4068
example : ¬ Rung4Hyp 8 11 5 := by unfold Rung4Hyp; decide  -- tile count 4450
example : ¬ Rung4Hyp 8 13 4 := by unfold Rung4Hyp; decide  -- tile count 4384
example : ¬ Rung4Hyp 8 21 3 := by unfold Rung4Hyp; decide  -- tile count 7362
example : ¬ Rung4Hyp 9 11 7 := by unfold Rung4Hyp; decide  -- tile count 7889
example : ¬ Rung4Hyp 9 16 5 := by unfold Rung4Hyp; decide  -- tile count 10775

#print axioms no_W_6_11_2
#print axioms no_W_11_16_3
#print axioms no_W_10_17_2
#print axioms agree_rung3_rung4

end Erdos634.Draft.WGapRung
