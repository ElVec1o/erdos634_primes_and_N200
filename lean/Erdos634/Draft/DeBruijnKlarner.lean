/-
Draft/DeBruijnKlarner.lean -- the divisibility criterion for brick tilings of a rectangle (de Bruijn; Klarner).

Cells are the points of `ℕ × ℕ`; `box x₀ y₀ w h` is the `w × h` block of cells with lower corner `(x₀, y₀)`.

    theorem brick_dvd : an `m × n` box is the disjoint union of `a × b` and `b × a` boxes  →  a ∣ m ∨ a ∣ n

Proof: weight the cell `(x, y)` by `ζ^(x+y)`, `ζ` a primitive `a`-th root of unity.  A box with a side of length `a`
has weight sum `0`; the `m × n` box has weight sum `(∑_{x<m} ζ^x)(∑_{y<n} ζ^y)`, and `∑_{x<m} ζ^x = 0` forces
`ζ^m = 1`, that is `a ∣ m`.

A classical statement (N. G. de Bruijn 1969, D. A. Klarner 1969); the Lean proof is a formal reproduction.
No sorry, no native_decide.
-/
import Mathlib

open Finset

namespace Erdos634.Draft.DeBruijnKlarner

/-- the `w × h` block of cells with lower corner `(x₀, y₀)` -/
def box (x₀ y₀ w h : ℕ) : Finset (ℕ × ℕ) := Finset.Ico x₀ (x₀ + w) ×ˢ Finset.Ico y₀ (y₀ + h)

variable {a : ℕ} {ζ : ℂ}

/-- weight sum of a run of `w` consecutive exponents -/
theorem run_sum (ζ : ℂ) (x₀ w : ℕ) :
    ∑ x ∈ Finset.Ico x₀ (x₀ + w), ζ ^ x = ζ ^ x₀ * ∑ k ∈ Finset.range w, ζ ^ k := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => pow_add ζ x₀ k)

/-- weight sum of a box -/
theorem box_sum (ζ : ℂ) (x₀ y₀ w h : ℕ) :
    ∑ p ∈ box x₀ y₀ w h, ζ ^ (p.1 + p.2)
      = (ζ ^ x₀ * ∑ k ∈ Finset.range w, ζ ^ k) * (ζ ^ y₀ * ∑ k ∈ Finset.range h, ζ ^ k) := by
  unfold box
  rw [Finset.sum_product, ← run_sum, ← run_sum, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => pow_add ζ x y))

/-- a full period of a primitive root sums to zero -/
theorem period_sum (hζ : IsPrimitiveRoot ζ a) (ha : 1 < a) : ∑ k ∈ Finset.range a, ζ ^ k = 0 :=
  hζ.geom_sum_eq_zero ha

/-- if the first `m` powers of a primitive `a`-th root sum to zero, then `a ∣ m` -/
theorem dvd_of_sum_zero (hζ : IsPrimitiveRoot ζ a) {m : ℕ} (h : ∑ k ∈ Finset.range m, ζ ^ k = 0) : a ∣ m := by
  have h1 : (ζ - 1) * ∑ k ∈ Finset.range m, ζ ^ k = ζ ^ m - 1 := mul_geom_sum ζ m
  rw [h, mul_zero] at h1
  exact (hζ.pow_eq_one_iff_dvd m).mp (sub_eq_zero.mp h1.symm)

/-- **de Bruijn–Klarner divisibility.**  If the `m × n` box is the disjoint union of boxes of shape `a × b` or
`b × a`, then `a ∣ m` or `a ∣ n`. -/
theorem brick_dvd {a b m n : ℕ} (ha : 0 < a) {ι : Type*} (S : Finset ι) (x₀ y₀ w h : ι → ℕ)
    (hshape : ∀ i ∈ S, (w i = a ∧ h i = b) ∨ (w i = b ∧ h i = a))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (box (x₀ i) (y₀ i) (w i) (h i)) (box (x₀ j) (y₀ j) (w j) (h j)))
    (hcover : S.biUnion (fun i => box (x₀ i) (y₀ i) (w i) (h i)) = box 0 0 m n) :
    a ∣ m ∨ a ∣ n := by
  rcases Nat.lt_or_ge 1 a with ha1 | ha1
  · have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / a)) a :=
      Complex.isPrimitiveRoot_exp a ha.ne'
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / a) with hζdef
    have hzero : ∀ i ∈ S, ∑ p ∈ box (x₀ i) (y₀ i) (w i) (h i), ζ ^ (p.1 + p.2) = 0 := by
      intro i hi
      rw [box_sum]
      rcases hshape i hi with ⟨hw, -⟩ | ⟨-, hh⟩
      · rw [hw, period_sum hζ ha1]; ring
      · rw [hh, period_sum hζ ha1]; ring
    have htot : ∑ p ∈ box 0 0 m n, ζ ^ (p.1 + p.2) = 0 := by
      rw [← hcover, Finset.sum_biUnion (fun i hi j hj hij => hdisj i hi j hj hij)]
      exact Finset.sum_eq_zero hzero
    rw [box_sum, pow_zero, one_mul, one_mul] at htot
    rcases mul_eq_zero.mp htot with h0 | h0
    · exact Or.inl (dvd_of_sum_zero hζ h0)
    · exact Or.inr (dvd_of_sum_zero hζ h0)
  · have : a = 1 := by omega
    exact Or.inl (this ▸ one_dvd m)

end Erdos634.Draft.DeBruijnKlarner

#print axioms Erdos634.Draft.DeBruijnKlarner.brick_dvd
