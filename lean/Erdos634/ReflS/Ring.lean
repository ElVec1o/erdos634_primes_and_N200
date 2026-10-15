import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! ReflS/Ring.lean -- the coefficient ring `R = ℤ[√21]` (Mathlib's `ℤ√21`), with LIGHT imports: this is all the
generated certificate data modules need, so they do not load the whole of Mathlib. -/

namespace ReflS

/-- the radicand -/
abbrev K : ℕ := 21

instance : Zsqrtd.Nonsquare K := ⟨fun n h => by
  have h' : 21 = n * n := h
  have h4 : n ≤ 4 := by
    by_contra hc
    push_neg at hc
    have : 25 ≤ n * n := by nlinarith
    omega
  interval_cases n <;> omega⟩

/-- the coefficient ring `ℤ[√21]` -/
abbrev R := ℤ√(K : ℤ)

/-- data constructors for elements of `R` (used by the generated certificates) -/
def zi (a : Int) : R := ⟨a, 0⟩
def zr (a b : Int) : R := ⟨a, b⟩

end ReflS
