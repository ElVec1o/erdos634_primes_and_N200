import Mathlib
import Erdos634.MarchRecurrence

/-!
# Search-tree sizes for the adjacent words `(bp, bp−1)` as finite statements

The sequence (search-tree sizes for the adjacent words `(bp, bp−1)`, `bp = 4, …, 15`) is fixed here as a
literal list, and every arithmetic assertion about it is a kernel-checked statement:

* `sizes_recurrence` — `a(n) = a(n−1) + a(n−2) + 2` at every `bp = 6, …, 15`;
* `sizes_shift_fib` — `a(4 + j) + 2 = 207·F(j+1) + 94·F(j)` for `j = 0, …, 11` (`F = Nat.fib`), i.e.
  `a + 2` is a pure Fibonacci sequence, consistent with `MarchRecurrence.shift_to_fibonacci`;
* `sizes_ratio` — the last ratio `38172/23591` lies within `10⁻⁴` of `φ = (1+√5)/2`.

Not a Lean statement: that these numbers are the sizes of the search program's refutation trees
(a measurement).  The refutations themselves exist for every `f ≥ 3` by
`E1BaseWord.e1_family_f_ge_3_congruent` (`Draft.HeurFinDep.findep_no_completion`).

Standard axioms; no `sorry`.
-/

namespace Erdos634.Draft.HeurFib

/-- The reported sizes for `bp = 4, …, 15` (index `i` ↔ `bp = i + 4`). -/
def sizes : List ℕ := [205, 299, 506, 807, 1315, 2124, 3441, 5567, 9010, 14579, 23591, 38172]

theorem sizes_length : sizes.length = 12 := rfl

/-- **The recurrence** `a(n) = a(n−1) + a(n−2) + 2` at every `bp = 6, …, 15`. -/
theorem sizes_recurrence :
    ∀ i : Fin 10, sizes.getD (i + 2) 0 = sizes.getD (i + 1) 0 + sizes.getD i 0 + 2 := by
  decide

/-- **`a + 2` is Fibonacci**: `a(4 + j) + 2 = 207·F(j+1) + 94·F(j)`, `j = 0, …, 11`. -/
theorem sizes_shift_fib :
    ∀ j : Fin 12, sizes.getD j 0 + 2 = 207 * Nat.fib (j + 1) + 94 * Nat.fib j := by
  decide

/-- The shifted list satisfies the pure Fibonacci recurrence (the finite instance of
`MarchRecurrence.shift_to_fibonacci`). -/
theorem sizes_shift_pure :
    ∀ i : Fin 10, sizes.getD (i + 2) 0 + 2 = (sizes.getD (i + 1) 0 + 2) + (sizes.getD i 0 + 2) := by
  decide

/-- The two pre-registered values are the recurrence's predictions from their predecessors. -/
theorem predicted_values : (5567 + 3441 + 2 = 9010) ∧ (14579 + 9010 + 2 = 23591) := by decide

/-- **Growth**: the last ratio is within `10⁻⁴` of the golden ratio. -/
theorem sizes_ratio : |(38172 : ℝ) / 23591 - (1 + Real.sqrt 5) / 2| < 1 / 10000 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hlo : (2.2360679 : ℝ) < Real.sqrt 5 := by nlinarith
  have hhi : Real.sqrt 5 < (2.2360680 : ℝ) := by nlinarith
  rw [abs_lt]; constructor <;> norm_num <;> linarith

end Erdos634.Draft.HeurFib
