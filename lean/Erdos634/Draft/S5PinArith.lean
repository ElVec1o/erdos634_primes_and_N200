import Mathlib.Tactic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Arithmetic of the pinned `c`-tile

Tile sides `a = e f`, `b = f² − e²`, `c = f²` with `0 < e < f` coprime.  A chain of tile edges that starts with a `b`
(or a `c`) cannot have total length `a`, and one that starts with an `a` (or a `c`) cannot have total length `b`.
These are the two word facts used along the upper edges of a `c`-tile whose ends are pinned.
Pure integer arithmetic; no sorry.
-/

namespace Erdos634.Draft.S5PinArith

theorem coprime_ab {e f : ℤ} (hcop : IsCoprime e f) : IsCoprime (e * f) (f ^ 2 - e ^ 2) := by
  have h1 : IsCoprime e (f ^ 2 - e ^ 2) := by
    have h := (hcop.pow_right (n := 2)).add_mul_left_right (-e)
    have e1 : f ^ 2 + e * -e = f ^ 2 - e ^ 2 := by ring
    rwa [e1] at h
  have h2 : IsCoprime f (f ^ 2 - e ^ 2) := by
    have h0 : IsCoprime f (-(e ^ 2)) := (hcop.symm.pow_right (n := 2)).neg_right
    have h := h0.add_mul_left_right f
    have e1 : -(e ^ 2) + f * f = f ^ 2 - e ^ 2 := by ring
    rwa [e1] at h
  exact h1.mul_left h2

/-- a word containing a `b` does not have length `a` -/
theorem no_word_a {e f : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (x y z : ℕ) (hy : 1 ≤ y) :
    (x : ℤ) * (e * f) + (y : ℤ) * (f ^ 2 - e ^ 2) + (z : ℤ) * f ^ 2 ≠ e * f := by
  intro h
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg _
  have hz0 : (0 : ℤ) ≤ (z : ℤ) := Int.natCast_nonneg _
  have hy1 : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy
  have hf : 0 < f := by linarith
  have ha : 0 < e * f := mul_pos he hf
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hca : e * f < f ^ 2 := by nlinarith
  -- no `c`
  have hz : (z : ℤ) = 0 := by
    by_contra hne
    have hz1 : (1 : ℤ) ≤ (z : ℤ) := by omega
    nlinarith [mul_nonneg hx0 ha.le, mul_le_mul_of_nonneg_right hy1 hb.le,
      mul_le_mul_of_nonneg_right hz1 (by positivity : (0 : ℤ) ≤ f ^ 2)]
  -- no `a`
  have hx : (x : ℤ) = 0 := by
    by_contra hne
    have hx1 : (1 : ℤ) ≤ (x : ℤ) := by omega
    nlinarith [mul_le_mul_of_nonneg_right hx1 ha.le, mul_le_mul_of_nonneg_right hy1 hb.le]
  rw [hz, hx] at h
  have hdvd : (f ^ 2 - e ^ 2) ∣ e * f := ⟨(y : ℤ), by linarith⟩
  have hunit : IsUnit (f ^ 2 - e ^ 2) := (coprime_ab hcop).isUnit_of_dvd' hdvd (dvd_refl _)
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · nlinarith
  · linarith

/-- a word containing an `a` or a `c` does not have length `b` -/
theorem no_word_b {e f : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (x y z : ℕ)
    (hxz : 1 ≤ x ∨ 1 ≤ z) :
    (x : ℤ) * (e * f) + (y : ℤ) * (f ^ 2 - e ^ 2) + (z : ℤ) * f ^ 2 ≠ f ^ 2 - e ^ 2 := by
  intro h
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg _
  have hy0 : (0 : ℤ) ≤ (y : ℤ) := Int.natCast_nonneg _
  have hz0 : (0 : ℤ) ≤ (z : ℤ) := Int.natCast_nonneg _
  have hf : 0 < f := by linarith
  have ha : 0 < e * f := mul_pos he hf
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have he2 : 0 < e ^ 2 := by positivity
  -- no `c`
  have hz : (z : ℤ) = 0 := by
    by_contra hne
    have hz1 : (1 : ℤ) ≤ (z : ℤ) := by omega
    nlinarith [mul_nonneg hx0 ha.le, mul_nonneg hy0 hb.le,
      mul_le_mul_of_nonneg_right hz1 (by positivity : (0 : ℤ) ≤ f ^ 2)]
  have hx1 : (1 : ℤ) ≤ (x : ℤ) := by
    rcases hxz with h1 | h1
    · exact_mod_cast h1
    · exfalso
      have : (1 : ℤ) ≤ (z : ℤ) := by exact_mod_cast h1
      omega
  -- no `b`
  have hy : (y : ℤ) = 0 := by
    by_contra hne
    have hy1 : (1 : ℤ) ≤ (y : ℤ) := by omega
    nlinarith [mul_le_mul_of_nonneg_right hx1 ha.le, mul_le_mul_of_nonneg_right hy1 hb.le]
  rw [hz, hy] at h
  have hdvd : e * f ∣ f ^ 2 - e ^ 2 := ⟨(x : ℤ), by linarith⟩
  have hunit : IsUnit (e * f) := (coprime_ab hcop).isUnit_of_dvd' (dvd_refl _) hdvd
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · nlinarith
  · linarith

/-- **Base word of the family `(2, k, k+1)`**: with a `c`-edge the word is `a + c + (k−1) b` (so exactly one `c`). -/
theorem base_word_k {k : ℤ} (hk : 1 ≤ k) (P Q R : ℕ) (hR : 1 ≤ R)
    (h : 2 * k * ((k + 1) ^ 2 - k ^ 2) = (P : ℤ) * (k * (k + 1)) + (Q : ℤ) * ((k + 1) ^ 2 - k ^ 2)
      + (R : ℤ) * (k + 1) ^ 2) : R = 1 := by
  have hP0 : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg _
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
  have hR1 : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
  have hb : (k + 1) ^ 2 - k ^ 2 = 2 * k + 1 := by ring
  rw [hb] at h
  -- (R − P)(k+1)² ≡ 0 mod (2k+1), and (k+1)² is a unit mod 2k+1
  have hdvd : (2 * k + 1) ∣ ((R : ℤ) - P) := by
    have h1 : (2 * k + 1) ∣ ((R : ℤ) - P) * (k + 1) ^ 2 :=
      ⟨2 * k - Q - P * (k + 1), by linear_combination -h⟩
    have hc : IsCoprime (2 * k + 1) ((k + 1) ^ 2) := by
      have : IsCoprime (2 * k + 1) (k + 1) := ⟨-1, 2, by ring⟩
      exact this.pow_right
    exact hc.dvd_of_dvd_mul_right h1
  obtain ⟨m, hm⟩ := hdvd
  -- size: |R − P| < 2k+1
  have hRP : (R : ℤ) = P := by
    have hk0 : 0 < k := by linarith
    rcases lt_trichotomy m 0 with hneg | hzero | hpos
    · -- P ≥ R + (2k+1): P a ≥ (2k+2) k (k+1) > 2k(2k+1)
      have hP : (P : ℤ) ≥ R + (2 * k + 1) := by nlinarith
      nlinarith [mul_nonneg hQ0 (by linarith : (0 : ℤ) ≤ 2 * k + 1),
        mul_nonneg (by linarith : (0 : ℤ) ≤ (R : ℤ)) (by positivity : (0 : ℤ) ≤ (k + 1) ^ 2),
        mul_le_mul_of_nonneg_right hP (by nlinarith : (0 : ℤ) ≤ k * (k + 1))]
    · rw [hzero] at hm; linarith
    · -- R ≥ P + (2k+1): R c ≥ (2k+1)(k+1)² > 2k(2k+1)
      have hRge : (R : ℤ) ≥ 2 * k + 1 := by nlinarith
      nlinarith [mul_nonneg hQ0 (by linarith : (0 : ℤ) ≤ 2 * k + 1),
        mul_nonneg hP0 (by nlinarith : (0 : ℤ) ≤ k * (k + 1)),
        mul_le_mul_of_nonneg_right hRge (by positivity : (0 : ℤ) ≤ (k + 1) ^ 2)]
  -- R = P: P (k+1) + Q = 2k, so P ≤ 1
  rw [hRP] at h
  have h2 : (P : ℤ) * (k + 1) + Q = 2 * k := by
    have h3 : ((P : ℤ) * (k + 1) + Q - 2 * k) * (2 * k + 1) = 0 := by linear_combination -h
    have hne : (2 * k + 1) ≠ 0 := by linarith
    have := (mul_eq_zero.mp h3).resolve_right hne
    linarith
  have hP1 : (P : ℤ) ≤ 1 := by
    by_contra hgt
    have : (2 : ℤ) ≤ P := by omega
    nlinarith
  have : (R : ℤ) = 1 := by rw [hRP]; rw [hRP] at hR1; omega
  exact_mod_cast this

/-- the only word of length `a` is the single letter `a` -/
theorem word_a_single {e f : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (x y z : ℕ)
    (h : (x : ℤ) * (e * f) + (y : ℤ) * (f ^ 2 - e ^ 2) + (z : ℤ) * f ^ 2 = e * f) : x + y + z = 1 := by
  have hf : 0 < f := by linarith
  have ha : 0 < e * f := mul_pos he hf
  have hy : y = 0 := by
    by_contra hne
    exact no_word_a he hef hcop x y z (by omega) h
  subst hy
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg _
  have hz : z = 0 := by
    by_contra hne
    have hz1 : (1 : ℤ) ≤ (z : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hca : e * f < f ^ 2 := by nlinarith
    nlinarith [mul_nonneg hx0 ha.le, mul_le_mul_of_nonneg_right hz1 (by positivity : (0 : ℤ) ≤ f ^ 2)]
  subst hz
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  have hx : (x : ℤ) = 1 := by
    have h1 : ((x : ℤ) - 1) * (e * f) = 0 := by linear_combination h
    have := (mul_eq_zero.mp h1).resolve_right ha.ne'
    linarith
  have : x = 1 := by exact_mod_cast hx
  omega

/-- the only word of length `b` is the single letter `b` -/
theorem word_b_single {e f : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (x y z : ℕ)
    (h : (x : ℤ) * (e * f) + (y : ℤ) * (f ^ 2 - e ^ 2) + (z : ℤ) * f ^ 2 = f ^ 2 - e ^ 2) : x + y + z = 1 := by
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hx : x = 0 := by
    by_contra hne
    exact no_word_b he hef hcop x y z (Or.inl (by omega)) h
  have hz : z = 0 := by
    by_contra hne
    exact no_word_b he hef hcop x y z (Or.inr (by omega)) h
  subst hx; subst hz
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add] at h
  have hy : (y : ℤ) = 1 := by
    have h1 : ((y : ℤ) - 1) * (f ^ 2 - e ^ 2) = 0 := by linear_combination h
    have := (mul_eq_zero.mp h1).resolve_right hb.ne'
    linarith
  have : y = 1 := by exact_mod_cast hy
  omega

end Erdos634.Draft.S5PinArith

#print axioms Erdos634.Draft.S5PinArith.no_word_a
#print axioms Erdos634.Draft.S5PinArith.no_word_b
#print axioms Erdos634.Draft.S5PinArith.base_word_k
