import Mathlib.Tactic
import Erdos634.Draft.GLCArith

/-!
# More word arithmetic for the tile `(k², 2k+1, k(k+1))`, `k ≥ 2` (G2)

* `b_not_dvd_c`        : `b ∤ c` (so the segment `[Y,Z]` of length `c - b` is not a sum of edges);
* `word_c`             : `p a + q b + r c = c ⇒ (p,q,r) = (0,0,1)` (the `c`-edge is covered by one `c`-edge only);
* `a_sub_b_nonrep`     : `b + p a + q b + r c = a` has no solution (`a − b` is not a sum of edge lengths, for `k ≥ 2`);
* real scaled forms `hword_c_real` (shape of `far_chain_counts`' `hword`).
-/

namespace Erdos634.GLC

theorem b_not_dvd_c (k q : ℕ) (hk : 2 ≤ k) (h : q * (2 * k + 1) = k * (k + 1)) : False := by
  have h1 : ((2 * k + 1 : ℕ) : ℤ) * (2 * k + 1 - 4 * q) = 1 := by
    have h' : (q : ℤ) * (2 * k + 1) = (k : ℤ) * (k + 1) := by exact_mod_cast h
    push_cast; linear_combination (-4) * h'
  have := Int.eq_one_of_mul_eq_one_right (by positivity) h1
  omega

theorem word_c (k : ℕ) (hk : 2 ≤ k) (p q r : ℕ)
    (h : p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) = k * (k + 1)) : p = 0 ∧ q = 0 ∧ r = 1 := by
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hr : r ≤ 1 := by
    by_contra hr
    have : 2 * (k * (k + 1)) ≤ r * (k * (k + 1)) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  interval_cases r
  · exfalso
    rcases Nat.lt_or_ge p 2 with hp | hp
    · interval_cases p
      · exact b_not_dvd_c k q hk (by simpa using h)
      · have h2 : q * (2 * k + 1) = k := by nlinarith
        rcases Nat.eq_zero_or_pos q with hq | hq
        · subst hq; omega
        · have : 2 * k + 1 ≤ q * (2 * k + 1) := Nat.le_mul_of_pos_left _ hq
          omega
    · nlinarith
  · have hp : p = 0 := by
      by_contra hp
      have : 1 * k ^ 2 ≤ p * k ^ 2 := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    subst hp
    have hq : q = 0 := by
      by_contra hq
      have : 1 * (2 * k + 1) ≤ q * (2 * k + 1) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    exact ⟨rfl, hq, rfl⟩

theorem a_sub_b_nonrep (k : ℕ) (hk : 2 ≤ k) (p q r : ℕ)
    (h : (2 * k + 1) + p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) = k ^ 2) : False := by
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hr : r = 0 := by
    by_contra hr
    have : k * (k + 1) ≤ r * (k * (k + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  subst hr
  have hp : p = 0 := by
    by_contra hp
    have : 1 * k ^ 2 ≤ p * k ^ 2 := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  subst hp
  exact no_dvd_aux k (q + 1) hk (by nlinarith)

theorem hword_c_real (k : ℕ) (hk : 2 ≤ k) {s : ℝ} (hs : 0 < s) (x y z : ℕ)
    (h : (x : ℝ) * (s * (k : ℝ) ^ 2) + y * (s * (2 * k + 1)) + z * (s * (k * (k + 1)))
      = s * (k * (k + 1))) : x = 0 ∧ y = 0 ∧ z = 1 := by
  have h1 : ((x * k ^ 2 + y * (2 * k + 1) + z * (k * (k + 1)) : ℕ) : ℝ) = ((k * (k + 1) : ℕ) : ℝ) := by
    have : s * ((x : ℝ) * (k : ℝ) ^ 2 + y * (2 * k + 1) + z * (k * (k + 1))) = s * (k * (k + 1)) := by
      linear_combination h
    have := mul_left_cancel₀ hs.ne' this
    push_cast; exact this
  exact word_c k hk x y z (by exact_mod_cast h1)

/-- Full form of the word lemma for `a` (scaled): `x a + y b + z c = a ⇒ (x,y,z) = (1,0,0)`. -/
theorem hword_a_full (k : ℕ) (hk : 2 ≤ k) {s : ℝ} (hs : 0 < s) (x y z : ℕ)
    (h : (x : ℝ) * (s * (k : ℝ) ^ 2) + y * (s * (2 * k + 1)) + z * (s * (k * (k + 1)))
      = s * (k : ℝ) ^ 2) : x = 1 ∧ y = 0 ∧ z = 0 := by
  have h1 : ((x * k ^ 2 + y * (2 * k + 1) + z * (k * (k + 1)) : ℕ) : ℝ) = ((k ^ 2 : ℕ) : ℝ) := by
    have : s * ((x : ℝ) * (k : ℝ) ^ 2 + y * (2 * k + 1) + z * (k * (k + 1))) = s * (k : ℝ) ^ 2 := by
      linear_combination h
    have := mul_left_cancel₀ hs.ne' this
    push_cast; exact this
  exact word_a k hk x y z (by exact_mod_cast h1)

/-- Witness: `k = 2`, tile `(4,5,6)`: `6 = 1·6` only. -/
theorem word_c_k2 : ∀ p q r : ℕ, p * 4 + q * 5 + r * 6 = 6 → p = 0 ∧ q = 0 ∧ r = 1 := by
  intro p q r h
  exact word_c 2 le_rfl p q r (by norm_num; omega)

/-- Degenerate case `k = 1` (tile `(1,3,2)`): `c = 2 = 2a`, so `word_c` fails. -/
theorem word_c_fails_k1 : (2 : ℕ) * 1 ^ 2 + 0 * (2 * 1 + 1) + 0 * (1 * (1 + 1)) = 1 * (1 + 1) ∧
    ¬ ((2 : ℕ) = 0 ∧ (0 : ℕ) = 0 ∧ (0 : ℕ) = 1) := by decide

end Erdos634.GLC

#print axioms Erdos634.GLC.word_c
#print axioms Erdos634.GLC.a_sub_b_nonrep
