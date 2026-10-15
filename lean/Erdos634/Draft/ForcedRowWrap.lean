import Erdos634.ForcedRow

namespace Erdos634.Draft.ForcedRowWrap

open Erdos634.ForcedRow

/-- Thin wrapper: the row count identity `(2k-1) + (k-1)² = k²`. -/
theorem wrap_row_count (k : ℤ) : (2 * k - 1) + (k - 1) ^ 2 = k ^ 2 :=
  row_count k

/-- Thin wrapper: the junction ledger — slot figure closes a straight angle. -/
theorem wrap_junction_ledger (α β : ℝ) (h : 3 * α + 2 * β = Real.pi) :
    (2 * α + β) + α + β = Real.pi :=
  junction_ledger α β h

/-- Thin wrapper: the slot residual is exactly β. -/
theorem wrap_slot_residual_beta (α β : ℝ) (h : 3 * α + 2 * β = Real.pi) :
    Real.pi - (2 * α + β) - α = β :=
  slot_residual_beta α β h

/-- Thin wrapper: base letters are distinct for 1 ≤ e < f (with coprimality and side identity). -/
theorem wrap_base_letter_distinct (e f b : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) :
    e * f ≠ b ∧ b ≠ f ^ 2 :=
  base_letter_distinct e f b he hef hcop hb

-- Non-vacuity: at e=1, f=2, b=3 (since 3 + 1 = 4 = 2²), gcd(1,2)=1 — sides e*f=2, b=3, f²=4 distinct.
example : (1 : ℕ) * 2 ≠ 3 ∧ 3 ≠ 2 ^ 2 :=
  wrap_base_letter_distinct 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms wrap_row_count
#print axioms wrap_junction_ledger

end Erdos634.Draft.ForcedRowWrap
