import Erdos634.OrderForcing

/-!
# The reach-4 pincer window at f≤6: arithmetic kernel

At members with 3≤f≤6, the reach-4 pincer window is bounded:
with 3≤bp≤f and 2≤cp≤f+1 and bp≠cp, the pair (bp,cp) falls in one of four bounded windows
(each with bp or cp ≤ 5).

The arithmetic is proved in `OrderForcing.lean`:
- **`pincer_window_four`**: for 3≤f≤6, 3≤bp≤f, 2≤cp≤f+1, bp≠cp:
  (bp<cp∧bp≤5) ∨ (cp<bp∧f+3−bp≤5) ∨ (cp=bp+1∧f+3−cp≤5) ∨ (bp=cp+1∧cp≤5).

"Reach 4" and the pincer itself are placement statements about real tilings and are not covered here.

0 sorry, no axioms (pure omega).
-/

namespace Erdos634.Draft.Walls16Wrap

open Erdos634.OrderForcing

/-- Reach-4 pincer window at f≤6. -/
theorem walls16_pincer_window {f bp cp : ℕ} (hf : 3 ≤ f) (hf6 : f ≤ 6)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 5) ∨ (cp < bp ∧ f + 3 - bp ≤ 5) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 5) ∨ (bp = cp + 1 ∧ cp ≤ 5) :=
  pincer_window_four hf hf6 hb3 hbf hc2 hcf hne

/-- Non-vacuity: at f=4, bp=3, cp=4 (bp<cp, bp=3≤5). -/
theorem walls16_witness :
    (3 : ℕ) ≤ 4 ∧ (4 : ℕ) ≤ 6 ∧ (3 : ℕ) ≤ 3 ∧ (3 : ℕ) ≤ 4 ∧ (2 : ℕ) ≤ 4 ∧ (4 : ℕ) ≤ 5 ∧
    (3 : ℕ) ≠ 4 := by norm_num

#print axioms walls16_pincer_window

end Erdos634.Draft.Walls16Wrap
