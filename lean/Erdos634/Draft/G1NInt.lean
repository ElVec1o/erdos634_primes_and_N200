import Mathlib

/-!
# Clearing denominators

Shape-independent.  If the sides `A B C > 0` of a `120`-degree triangle (`C^2 = A^2+AB+B^2`) have rational ratios
`A = q B`, `C = r B`, then `(A,B,C) = K (a,b,c)` with `a b c` natural, `gcd(a,b) = 1`, `c^2 = a^2+ab+b^2`, `K > 0`.
-/

namespace Erdos634.Draft.G1NInt

/-- A positive rational whose square is a natural number is a natural number. -/
theorem rat_sq_nat (x : ℚ) (n : ℕ) (h : x ^ 2 = n) (hx : 0 < x) : ∃ c : ℕ, x = c := by
  have h1 : (x ^ 2).den = 1 := by rw [h]; exact Rat.den_natCast n
  rw [Rat.den_pow] at h1
  have hd : x.den = 1 := by
    simpa using h1
  have hnum : ((x.num : ℤ) : ℚ) = x := Rat.coe_int_num_of_den_eq_one hd
  have hnpos : 0 < x.num := Rat.num_pos.mpr hx
  refine ⟨x.num.toNat, ?_⟩
  have : ((x.num.toNat : ℤ) : ℚ) = x.num := by rw [Int.toNat_of_nonneg hnpos.le]
  have h2 : (x.num.toNat : ℚ) = x := by
    have := this; push_cast at this ⊢; rw [this, hnum]
  exact h2.symm

theorem integer_tile_of_ratios {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hc : C ^ 2 = A ^ 2 + A * B + B ^ 2) (q r : ℚ) (hq : A = q * B) (hr : C = r * B) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  have hqpos : 0 < q := by
    have : (0 : ℝ) < q := by
      by_contra h; push Not at h
      have : q * B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hB.le
      linarith
    exact_mod_cast this
  have hrpos : 0 < r := by
    have : (0 : ℝ) < r := by
      by_contra h; push Not at h
      have : r * B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hB.le
      linarith
    exact_mod_cast this
  -- r^2 = q^2 + q + 1 over Q
  have hrq : r ^ 2 = q ^ 2 + q + 1 := by
    have key : ((r : ℝ) ^ 2 - ((q : ℝ) ^ 2 + q + 1)) * B ^ 2 = 0 := by
      rw [hq, hr] at hc; nlinarith
    have := (mul_eq_zero.mp key).resolve_right (pow_ne_zero 2 hB.ne')
    exact_mod_cast sub_eq_zero.mp this
  set a : ℕ := q.num.toNat with ha
  set b : ℕ := q.den with hb
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
  have hbpos : 0 < b := q.pos
  have hapos : 0 < a := by rw [ha]; exact Int.lt_toNat.mpr hnum
  have haQ : (a : ℚ) = q.num := by
    rw [ha]; have := Int.toNat_of_nonneg hnum.le
    exact_mod_cast this
  have hqab : q * b = a := by
    rw [haQ, hb]; exact Rat.mul_den_eq_num q
  have hcop : Nat.Coprime a b := by
    have h := q.reduced
    have e : a = q.num.natAbs := by
      rw [ha]; omega
    rw [e]; exact h
  -- c
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hx2 : (r * b) ^ 2 = ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℚ) := by
    push_cast
    have : (r * b) ^ 2 = r ^ 2 * b ^ 2 := by ring
    rw [this, hrq, ← hqab]; ring
  obtain ⟨c, hcx⟩ := rat_sq_nat (r * b) _ hx2 (by positivity)
  have hcsq : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    have h : ((c : ℚ)) ^ 2 = ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℚ) := by rw [← hcx]; exact hx2
    exact_mod_cast h
  refine ⟨B / b, a, b, c, by positivity, hapos, hbpos, hcop, hcsq, ?_, ?_, ?_⟩
  · have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
    have : (q : ℝ) * b = a := by exact_mod_cast hqab
    rw [hq]; field_simp; linarith
  · have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
    field_simp
  · have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
    have : (r : ℝ) * b = c := by exact_mod_cast hcx
    rw [hr]; field_simp; linarith

end Erdos634.Draft.G1NInt

#print axioms Erdos634.Draft.G1NInt.rat_sq_nat
#print axioms Erdos634.Draft.G1NInt.integer_tile_of_ratios
