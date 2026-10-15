import Erdos634.InvariantCore

/-!
# InvariantCore — flux/charge invariant core algebra: wrapper

`InvariantCore.*` provides the abstract algebraic core of the flux invariant argument.

Key results:
1. **`sum_antisym_of_involution`**: an antisymmetric function's weighted sum over an involution is 0.
2. **`cancellation_core`**: the interior part cancels, leaving only the boundary sum.
3. **`tile_value_core`**: ε(j₀)·c + ε(j₀+2)·a + ε(j₀+3)·b = ε(j₀)·(c+a−b).
4. **`integrality_parity`**: ±1 signs: 2 | (∑ sgn i) − N.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.InvariantCoreWrap

open Erdos634.InvariantCore

theorem invcore_sum_antisym {D : Type*} [Fintype D]
    (neg : D → D) (hinv : Function.Involutive neg)
    (L f : D → ℤ) (hL : ∀ d, L (neg d) = L d) (hf : ∀ d, f (neg d) = - f d) :
    ∑ d, L d * f d = 0 :=
  sum_antisym_of_involution neg hinv L f hL hf

theorem invcore_cancellation {D : Type*} [Fintype D]
    (neg : D → D) (hinv : Function.Involutive neg)
    (Lint Lbd f : D → ℤ)
    (hLint : ∀ d, Lint (neg d) = Lint d) (hf : ∀ d, f (neg d) = - f d) :
    ∑ d, (Lint d + Lbd d) * f d = ∑ d, Lbd d * f d :=
  cancellation_core neg hinv Lint Lbd f hLint hf

theorem invcore_tile_value (a b c j₀ : ℤ) :
    ε j₀ * c + ε (j₀ + 2) * a + ε (j₀ + 3) * b = ε j₀ * (c + a - b) :=
  tile_value_core a b c j₀

theorem invcore_integrality_parity (N : ℕ) (sgn : Fin N → ℤ)
    (hs : ∀ i, sgn i = 1 ∨ sgn i = -1) :
    (2 : ℤ) ∣ (∑ i, sgn i) - (N : ℤ) :=
  integrality_parity N sgn hs

/-- Non-vacuity: ε 0 = 1 (j₀=0, even). -/
theorem invcore_witness : ε (0:ℤ) = 1 := by simp [ε]

#print axioms invcore_sum_antisym
#print axioms invcore_cancellation
#print axioms invcore_tile_value
#print axioms invcore_integrality_parity

end Erdos634.Draft.InvariantCoreWrap
