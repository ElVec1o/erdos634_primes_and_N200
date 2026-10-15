import Erdos634.OrderForcing

/-!
# Pincer window arithmetic behind a thick block

Behind a thick block (an f≤5 configuration), the pincer window arithmetic determines which (bp, cp) pairs escape. The
window closes at f≤5: every non-trivial pair (bp,cp) with 3≤bp≤f, 2≤cp≤f+1, bp≠cp
falls into one of four bounded subcases, each with reach ≤ 4.

The arithmetic content is in `OrderForcing.lean`:

1. **`pincer_window`**: for `3 ≤ f ≤ 5`, `3 ≤ bp ≤ f`, `2 ≤ cp ≤ f+1`, `bp ≠ cp`, the
   pair `(bp, cp)` satisfies one of four window conditions, each bounding the smaller
   coordinate by 4. This is the pure arithmetic of the window.

Only the arithmetic is formalized here; the geometric statement about the depth of the block structure is not.

No sorry, axioms [] (pure omega).
-/

namespace Erdos634.Draft.DepthWindowWrap

open Erdos634.OrderForcing

/-- Pincer window arithmetic: for f ≤ 5, every (bp,cp) pair is in one of four bounded windows. -/
theorem depth_window_arithmetic {f bp cp : ℕ} (hf : 3 ≤ f) (hf5 : f ≤ 5)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 4) ∨ (cp < bp ∧ f + 3 - bp ≤ 4) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 4) ∨ (bp = cp + 1 ∧ cp ≤ 4) :=
  pincer_window hf hf5 hb3 hbf hc2 hcf hne

/-- Non-vacuity: at f=3, bp=3, cp=2, the fourth window case holds (bp = cp+1, cp = 2 ≤ 4). -/
theorem depth_window_witness : (3 : ℕ) ≤ 3 ∧ (3 : ℕ) ≤ 5 ∧ (3 : ℕ) ≤ 3 ∧ (3 : ℕ) ≤ 3 ∧
    (2 : ℕ) ≤ 2 ∧ (2 : ℕ) ≤ 4 ∧ (3 : ℕ) ≠ 2 ∧
    (3 : ℕ) = 2 + 1 ∧ (2 : ℕ) ≤ 4 := by norm_num

#print axioms depth_window_arithmetic

end Erdos634.Draft.DepthWindowWrap
