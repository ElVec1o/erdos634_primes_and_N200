-- Draft/LemTightFormal.lean — the arithmetic of the γ-injection budget.
-- A side of parameter `p` carries `n_a = p f`, `n_b = 0`, `n_c = f − p e` (side equation
-- `p f · e f + n_c f² = f³`, γ-trap `n_c ≥ 1`), hence `k = p f + (f − p e)` edges and `k − 1`
-- junctions, so the γ-injection bound `#a + #b ≤ k − 1` has slack `(k−1) − (#a+#b) = f − p e − 1`.
-- Stated over ℤ (the existing `Frontier.gamma_slack`, `p_two_tight_iff` are ℕ-only and inline the
-- profile).  For p = 1 the slack f−e−1 is positive iff f ≥ e+2 (it is 0 at f = e+1).
import Mathlib.Tactic

namespace Erdos634.Draft.LemTightFormal

/-- Edge count `k` of a side of parameter `p` with the profile `(p f, 0, f − p e)`. -/
def edges (e f p : ℤ) : ℤ := p * f + 0 + (f - p * e)

/-- The slack of the γ-injection bound `#a + #b ≤ k − 1`: `(k − 1) − (#a + #b)`. -/
def slack (e f p : ℤ) : ℤ := (edges e f p - 1) - (p * f + 0)

/-- **`lem:tight`.**  The slack of a side of parameter `p` is `f − p e − 1`; at `p = 1` it is positive
exactly when `f ≥ e + 2` (and `0` at `f = e + 1`); at `p = 2` it vanishes exactly when `f = 2e + 1`. -/
theorem lem_tight (e f : ℤ) :
    (∀ p : ℤ, slack e f p = f - p * e - 1) ∧
    (0 < slack e f 1 ↔ e + 2 ≤ f) ∧
    (slack e f 1 = 0 ↔ f = e + 1) ∧
    (slack e f 2 = 0 ↔ f = 2 * e + 1) := by
  refine ⟨fun p => ?_, ?_, ?_, ?_⟩
  · unfold slack edges; ring
  · unfold slack edges; constructor <;> intro h <;> linarith
  · unfold slack edges; constructor <;> intro h <;> linarith
  · unfold slack edges; constructor <;> intro h <;> linarith

/-- The bound `#a + #b ≤ k − 1` itself holds for a side with `n_c ≥ 1`, i.e. `p e < f`. -/
theorem injection_bound (e f p : ℤ) (h : p * e < f) :
    p * f + 0 ≤ edges e f p - 1 := by
  unfold edges; linarith

/-- The tex's "in particular for `f > 2e`" (the range of `cor:ptwo`): the `p = 1` slack is positive,
indeed `≥ e`. -/
theorem slack_one_pos_of_two_lt (e f : ℤ) (h : 2 * e < f) : e ≤ slack e f 1 := by
  unfold slack edges; linarith

/-- Controls: `(1,2)` has slack `0` at `p = 1` (the tex clause "positive for every member" was false),
`(1,4)` has slack `2` at `p = 1`; `(3,7)` is tight at `p = 2` (`7 = 2·3 + 1`), `(1,4)` is not. -/
theorem controls :
    slack 1 2 1 = 0 ∧ slack 1 4 1 = 2 ∧ slack 3 7 2 = 0 ∧ slack 1 4 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [slack, edges]

end Erdos634.Draft.LemTightFormal

#print axioms Erdos634.Draft.LemTightFormal.lem_tight
#print axioms Erdos634.Draft.LemTightFormal.injection_bound
#print axioms Erdos634.Draft.LemTightFormal.slack_one_pos_of_two_lt
#print axioms Erdos634.Draft.LemTightFormal.controls
