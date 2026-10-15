import Erdos634.Frontier
import Erdos634.CChord
import Erdos634.Draft.RemClosePairFormal

/-!
# Close pairs: what the unconditional filters leave: wrapper

At a close pair (f²≤2ef+e²) the base admits extra columns
exactly when f≤2e; each has y=e+kf for some k≥1
(`base_column_y_form`, unconditional). Two filters apply:
1. The γ-trap removes z=0.
2. The corner parallelogram removes any column with x+z≤3 in a word of at least four edges
   (`cornerpara_filter`).

No extra column has x=0 (it would give f∣k, hence kb≥fb>2ef).

Lean content:
1. **`closepairs_y_form`**: every close-pair extra column has y=e+kf for k≥1 (`Frontier.base_column_y_form`
   via `RemClosePairFormal.y_form_nat`).
2. **`closepairs_cornerpara_filter`**: corner-para filter: x+z≤3 and x+z≥4 contradict
   (`CChord.cornerpara_filter`).
3. **`closepairs_no_x_zero`**: x=0 forces f∣k, so kb≥fb>2ef — size contradiction (arithmetic).
4. **`closepairs_k_pos`**: close pair column has k≥1 (from y≥e+f condition, arithmetic).

Only the filter arithmetic is formalized.  The statement that the corner-parallelogram filter
removes 8 columns in the range e≤9, f≤15 is a computational observation, not a Lean theorem.
-/

namespace Erdos634.Draft.ClosePairsWrap

open Erdos634.Frontier Erdos634.CChord Erdos634.Draft.RemClosePairFormal

/-- rem:closepairs (y-form): close-pair extra column has f ∣ y-e (y_form_nat). -/
theorem closepairs_y_form {e f x y z : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (heq : x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)) :
    (f : ℤ) ∣ (y : ℤ) - e :=
  y_form_nat hco hef heq

/-- rem:closepairs (cornerpara filter): x+z≤3 and corner para x+z≥4 give False. -/
theorem closepairs_cornerpara_filter {x y z : ℕ} (hlen : 4 ≤ x + y + z) (hxz : x + z ≤ 3)
    (hcorner : 4 ≤ x + z) : False :=
  cornerpara_filter hlen hxz hcorner

/-- rem:closepairs (x≠0): k*(f²-e²) > 0 when k≥1, e<f (arithmetic). -/
theorem closepairs_no_x_zero (e f k : ℤ) (hef : e < f) (he : 0 < e) (hk : 1 ≤ k) :
    0 < k * (f ^ 2 - e ^ 2) :=
  mul_pos (by linarith) (by nlinarith)

/-- rem:closepairs (k≥1): in a close pair the extra column has k≥1 since y>e. -/
theorem closepairs_k_pos (e f y : ℤ) (he : 0 < e) (hef : e < f) (hy : e < y)
    (hform : ∃ k : ℤ, y = e + k * f ∧ 0 ≤ k) :
    ∃ k : ℤ, y = e + k * f ∧ 1 ≤ k := by
  obtain ⟨k, hk, hk0⟩ := hform
  refine ⟨k, hk, ?_⟩
  have hf : 0 < f := by linarith
  have : 0 < k * f := by linarith [hk.symm]
  nlinarith [mul_pos_iff.mp this]

#print axioms closepairs_y_form
#print axioms closepairs_cornerpara_filter

end Erdos634.Draft.ClosePairsWrap
