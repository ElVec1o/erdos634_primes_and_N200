/-
Draft/WGapRung8.lean -- 16 November 2026 (work item LEAN_WGAP_2026-11-15, session 17).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  Leaf module.
Controls for `WGapRung.no_tiling_W_rung5` (copied in structure from WGapRung6 / WGapRung6b): (a) satisfiable instances with `M (f-e) = e + 5` exactly (so rung 4 does not apply), (9,16,2) (N = 1724), (13,19,3), (13,22,2);
(b) the rung-5 hypothesis list FAILS at the three Lean-kernel `WTilable` instances of WGapRung6b and at every witnessed tiling of the WGapRung6 list (including `W_4(2,3)`, `W_3(2,5)`, `W_4(3,5)`);
(c) agreement with `no_tiling_W_rung4` on a common instance (9,13,3).
-/
import Erdos634.Draft.WGapRung7
import Erdos634.Draft.WGapRung6b

namespace Erdos634.Draft.WGapRung

open Erdos634.Draft.CollarG

-- (a) satisfiable, with M (f - e) = e + 5 exactly (so rung 4 does not apply)
example : RungHyp 5 9 16 2 := by unfold RungHyp; decide    -- N = 1724
example : RungHyp 5 13 19 3 := by unfold RungHyp; decide
example : RungHyp 5 13 22 2 := by unfold RungHyp; decide
example : ¬ RungHyp 4 9 16 2 := by unfold RungHyp; decide
example : ¬ RungHyp 4 13 19 3 := by unfold RungHyp; decide
example : ¬ RungHyp 4 13 22 2 := by unfold RungHyp; decide
theorem no_W_9_16_2 : ¬ WTilable 9 16 2 :=
  no_tiling_W_rung5 9 16 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_13_19_3 : ¬ WTilable 13 19 3 :=
  no_tiling_W_rung5 13 19 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem no_W_13_22_2 : ¬ WTilable 13 22 2 :=
  no_tiling_W_rung5 13 22 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- (c) agreement with `no_tiling_W_rung4` on a common instance (9,13,3): M (f-e) = 12 = e + 3
theorem agree_rung4_rung5 : (¬ WTilable 9 13 3) ∧ (¬ WTilable 9 13 3) :=
  ⟨no_tiling_W_rung4 9 13 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
   no_tiling_W_rung5 9 13 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- the rung-5 theorem applied through its hypothesis list -/
theorem rung5_applied (e f M : ℕ) (h : RungHyp 5 e f M) : ¬ WTilable e f M :=
  no_tiling_W_rung5 e f M h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

-- (b) the rung-5 hypothesis list fails at the three Lean-kernel WTilable instances of WGapRung6b
example : ¬ RungHyp 5 2 3 3 := by unfold RungHyp; decide
example : ¬ RungHyp 5 6 11 11 := by unfold RungHyp; decide
example : ¬ RungHyp 5 6 11 17 := by unfold RungHyp; decide
-- and at every witnessed tiling of the WGapRung6 list
example : ¬ RungHyp 5 2 3 4 := by unfold RungHyp; decide 
example : ¬ RungHyp 5 10 21 4 := by unfold RungHyp; decide  -- tile count 12512
example : ¬ RungHyp 5 11 20 5 := by unfold RungHyp; decide  -- tile count 16975
example : ¬ RungHyp 5 13 20 6 := by unfold RungHyp; decide  -- tile count 22716
example : ¬ RungHyp 5 17 30 5 := by unfold RungHyp; decide  -- tile count 37775
example : ¬ RungHyp 5 19 40 3 := by unfold RungHyp; decide  -- tile count 25551
example : ¬ RungHyp 5 2 11 6 := by unfold RungHyp; decide  -- tile count 8568
example : ¬ RungHyp 5 2 15 8 := by unfold RungHyp; decide  -- tile count 28544
example : ¬ RungHyp 5 2 5 3 := by unfold RungHyp; decide  -- tile count 414
example : ¬ RungHyp 5 3 10 4 := by unfold RungHyp; decide  -- tile count 3056
example : ¬ RungHyp 5 3 16 6 := by unfold RungHyp; decide  -- tile count 18108
example : ¬ RungHyp 5 3 5 4 := by unfold RungHyp; decide  -- tile count 656
example : ¬ RungHyp 5 3 7 3 := by unfold RungHyp; decide  -- tile count 801
example : ¬ RungHyp 5 3 7 4 := by unfold RungHyp; decide  -- tile count 1424
example : ¬ RungHyp 5 3 8 3 := by unfold RungHyp; decide  -- tile count 1071
example : ¬ RungHyp 5 4 17 5 := by unfold RungHyp; decide  -- tile count 14050
example : ¬ RungHyp 5 4 7 4 := by unfold RungHyp; decide  -- tile count 1312
example : ¬ RungHyp 5 4 9 3 := by unfold RungHyp; decide  -- tile count 1314
example : ¬ RungHyp 5 5 11 3 := by unfold RungHyp; decide  -- tile count 1953
example : ¬ RungHyp 5 5 12 3 := by unfold RungHyp; decide  -- tile count 2367
example : ¬ RungHyp 5 5 17 4 := by unfold RungHyp; decide  -- tile count 8848
example : ¬ RungHyp 5 5 7 5 := by unfold RungHyp; decide  -- tile count 1825
example : ¬ RungHyp 5 5 8 4 := by unfold RungHyp; decide  -- tile count 1648
example : ¬ RungHyp 5 5 8 6 := by unfold RungHyp; decide  -- tile count 3708
example : ¬ RungHyp 5 5 9 4 := by unfold RungHyp; decide  -- tile count 2192
example : ¬ RungHyp 5 6 11 4 := by unfold RungHyp; decide  -- tile count 3296
example : ¬ RungHyp 5 6 19 4 := by unfold RungHyp; decide  -- tile count 10976
example : ¬ RungHyp 5 7 10 5 := by unfold RungHyp; decide  -- tile count 3775
example : ¬ RungHyp 5 7 11 4 := by unfold RungHyp; decide  -- tile count 3088
example : ¬ RungHyp 5 7 12 4 := by unfold RungHyp; decide  -- tile count 3824
example : ¬ RungHyp 5 7 13 13 := by unfold RungHyp; decide  -- tile count 48841
example : ¬ RungHyp 5 7 17 3 := by unfold RungHyp; decide  -- tile count 4761
example : ¬ RungHyp 5 7 9 6 := by unfold RungHyp; decide  -- tile count 4068
example : ¬ RungHyp 5 8 11 5 := by unfold RungHyp; decide  -- tile count 4450
example : ¬ RungHyp 5 8 13 4 := by unfold RungHyp; decide  -- tile count 4384
example : ¬ RungHyp 5 8 21 3 := by unfold RungHyp; decide  -- tile count 7362
example : ¬ RungHyp 5 9 11 7 := by unfold RungHyp; decide  -- tile count 7889
example : ¬ RungHyp 5 9 16 5 := by unfold RungHyp; decide  -- tile count 10775

#print axioms no_W_9_16_2
#print axioms no_W_13_19_3
#print axioms no_W_13_22_2
#print axioms agree_rung4_rung5
#print axioms rung5_applied

end Erdos634.Draft.WGapRung
