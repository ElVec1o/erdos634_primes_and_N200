import Erdos634.Draft.NogoCount37

/-!
# The count theorem with standard axioms only

`NogoCount37.nogoCount37_eq_10560` uses `native_decide` (which adds a non-standard
compiler-soundness axiom).

This file provides the same theorem using only [propext, Classical.choice, Quot.sound]
via kernel `decide` on the sum-decomposed computation:
  countValid37 = (allWords37.map (fun w => allOrients11.countP (fun o => validConfig w o))).sum

This avoids building the flat 245,760-pair list (which needs too much memory in the kernel).
Each word's 2048-orientation count is computed independently at peak O(2048) recursion depth.
maxRecDepth 8192 covers the 2048-deep countP spine; maxHeartbeats 0 for the kernel computation.
-/

namespace Erdos634.NogoCount37Kernel

open Erdos634.NogoCount37

-- ─────────────────────────────────────────────────────────────────────────────
-- General helper: countP on a flatMap equals the sum of per-key countPs
-- ─────────────────────────────────────────────────────────────────────────────

private theorem countP_flatMap_sum {α β : Type*} (f : α → List β) (p : β → Bool) :
    ∀ l : List α, (l.flatMap f).countP p = (l.map (fun a => (f a).countP p)).sum
  | [] => rfl
  | a :: t => by
    rw [List.flatMap_cons, List.countP_append, List.map_cons, List.sum_cons]
    exact congrArg₂ HAdd.hAdd rfl (countP_flatMap_sum f p t)

-- ─────────────────────────────────────────────────────────────────────────────
-- Reformulation of countValid37 as a word-by-word sum.
-- After rw [countP_flatMap_sum], the per-word count is
--   (allOrients11.map (fun o => (w, o))).countP (fun ⟨w', o⟩ => validConfig w' o)
-- which is definitionally equal to allOrients11.countP (fun o => validConfig w o)
-- via Function.comp beta reduction, so the rewrite identity closes by rfl.
-- ─────────────────────────────────────────────────────────────────────────────

private theorem countValid37_as_sum :
    countValid37 =
      (allWords37.map (fun w => allOrients11.countP (fun o => validConfig w o))).sum := by
  unfold countValid37
  rw [countP_flatMap_sum]
  simp only [List.countP_map]
  -- remaining goal: LHS uses (fun x => validConfig x.1 x.2) ∘ (fun o => (w, o))
  -- which is definitionally equal to fun o => validConfig w o
  rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- The sum equals 10560, proved by kernel `decide`.
-- 120 words × 2048 orientations each; the 2048-deep countP needs maxRecDepth ≥ 2048.
-- maxHeartbeats 0: the kernel computation is guaranteed finite.
-- ─────────────────────────────────────────────────────────────────────────────

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem wordSum_eq_10560 :
    (allWords37.map (fun w => allOrients11.countP (fun o => validConfig w o))).sum = 10560 := by
  decide

-- ─────────────────────────────────────────────────────────────────────────────
-- Main theorem: standard axioms only
-- ─────────────────────────────────────────────────────────────────────────────

/-- **`prop:nogoauto`, (3,7)-member count — standard axioms only.**
Identical conclusion to `NogoCount37.nogoCount37_eq_10560` but proved via kernel `decide`
on the word-by-word decomposition (no `native_decide`).
Axioms: [propext, Classical.choice, Quot.sound] only. -/
theorem nogoCount37_eq_10560_std : countValid37 = 10560 :=
  countValid37_as_sum.trans wordSum_eq_10560

#print axioms nogoCount37_eq_10560_std

end Erdos634.NogoCount37Kernel
