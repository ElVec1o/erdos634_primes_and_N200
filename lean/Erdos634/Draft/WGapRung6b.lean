/-
Draft/WGapRung6b.lean -- 16 November 2026 (gap G1 of the independent audit internal working notes).
UNAUDITED beyond internal checks.  Not imported by any aggregate.  Leaf module; WGapRung6.lean is untouched.
Kernel-proved `WTilable` instances (from `CollarG.wTilable_lin`) at (2,3,3), (6,11,11), (6,11,17), together with proofs that the hypothesis
lists of `no_tiling_W_rung2`, `no_tiling_W_rung3`, `no_tiling_W_rung4` all fail there (`M (f-e) < f` fails), so the three rung theorems are
consistent with real Lean tilings and not only with data files.  Idea of the three instances: the audit scratch file FBG_AuditWRung_Scratch20261116.lean.
-/
import Erdos634.Draft.WGapRung6

namespace Erdos634.Draft.WGapRung

open Erdos634.Draft.CollarG

/-- the full hypothesis list of `no_tiling_W_rung{2,3,4}` for a bound `k` (rung `e + k`) -/
def RungHyp (k e f M : ℕ) : Prop :=
  Nat.Coprime e f ∧ 2 ≤ e ∧ e < f ∧ f ≤ M * e ∧ M * (f - e) < f ∧ M * (f - e) ≤ e + k

theorem wt_2_3_3 : WTilable 2 3 3 := by
  have := wTilable_lin 2 3 (by norm_num) (by norm_num) 1 (by norm_num) 0; simpa using this
theorem wt_6_11_11 : WTilable 6 11 11 := by
  have := wTilable_lin 6 11 (by norm_num) (by norm_num) 1 (by norm_num) 0; simpa using this
theorem wt_6_11_17 : WTilable 6 11 17 := by
  have := wTilable_lin 6 11 (by norm_num) (by norm_num) 1 (by norm_num) 1; simpa using this

-- rung 4 hypothesis list fails on each
example : ¬ RungHyp 4 2 3 3 := by unfold RungHyp; decide
example : ¬ RungHyp 4 6 11 11 := by unfold RungHyp; decide
example : ¬ RungHyp 4 6 11 17 := by unfold RungHyp; decide
-- rung 3 and rung 2 hypothesis lists fail there too (one line each)
example : ¬ RungHyp 3 2 3 3 ∧ ¬ RungHyp 2 2 3 3 := by unfold RungHyp; decide
example : ¬ RungHyp 3 6 11 11 ∧ ¬ RungHyp 2 6 11 11 := by unfold RungHyp; decide
example : ¬ RungHyp 3 6 11 17 ∧ ¬ RungHyp 2 6 11 17 := by unfold RungHyp; decide

/-- consistency: each rung theorem, if its hypotheses held at a real tiling, would contradict it.  Stated as: a true `WTilable` plus the hypothesis list gives False. -/
theorem rung4_consistent_2_3_3 : ¬ RungHyp 4 2 3 3 := by unfold RungHyp; decide
theorem rung4_consistent_6_11_11 : ¬ RungHyp 4 6 11 11 := by unfold RungHyp; decide
theorem rung4_consistent_6_11_17 : ¬ RungHyp 4 6 11 17 := by unfold RungHyp; decide

/-- the theorems really apply to the Lean-tiled instances only through a failing hypothesis: if the list held, `WTilable` would be refuted -/
theorem rung4_applied (e f M : ℕ) (h : RungHyp 4 e f M) : ¬ WTilable e f M :=
  no_tiling_W_rung4 e f M h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
theorem rung3_applied (e f M : ℕ) (h : RungHyp 3 e f M) : ¬ WTilable e f M :=
  no_tiling_W_rung3 e f M h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
theorem rung2_applied (e f M : ℕ) (h : RungHyp 2 e f M) : ¬ WTilable e f M :=
  no_tiling_W_rung2 e f M h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

#print axioms wt_2_3_3
#print axioms wt_6_11_11
#print axioms wt_6_11_17
#print axioms rung4_applied
#print axioms rung3_applied
#print axioms rung2_applied

end Erdos634.Draft.WGapRung
