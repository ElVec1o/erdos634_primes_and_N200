import Mathlib.Tactic

/-!
# Word arithmetic for the tile `(k², 2k+1, k(k+1))` (`γ = 2α`, `cos α = (k+1)/(2k)`)

For `k ≥ 2`, `a = k²`, `b = 2k+1`, `c = k(k+1)`:
* `word_a`  : `p a + q b + r c = a  ⇒  (p,q,r) = (1,0,0)`   (the corner chord, an `a`-edge, is covered by ONE `a`-edge);
* `word_2a` : `p a + q b + r c = 2a ⇒  (p,q,r) = (2,0,0)`   (uniqueness `2a = (2,0,0)` used in G2);
* real/scaled forms `hword_a_real`, `hword_2a_real` for a tile scaled by `s > 0`, in the exact shape of
  `far_chain_single_gen`'s `hword`.
* Degenerate case `word_2a_fails_k1`: at `k = 1` (degenerate tile `(1,3,2)`) `2a = 0a+0b+1c`, so `2 ≤ k` is needed.
-/

namespace Erdos634.GLC

theorem no_dvd_aux (k q : ℕ) (hk : 2 ≤ k) (h : q * (2 * k + 1) = k ^ 2) : False := by
  have h1 : ((2 * k + 1 : ℕ) : ℤ) * (4 * q - 2 * k + 1) = 1 := by
    have h' : (q : ℤ) * (2 * k + 1) = (k : ℤ) ^ 2 := by exact_mod_cast h
    push_cast; linear_combination 4 * h'
  have := Int.eq_one_of_mul_eq_one_right (by positivity) h1
  omega

theorem no_dvd_aux2 (k q : ℕ) (hk : 2 ≤ k) (h : q * (2 * k + 1) = 2 * k ^ 2) : False := by
  have h1 : ((2 * k + 1 : ℕ) : ℤ) * (2 * q - 2 * k + 1) = 1 := by
    have h' : (q : ℤ) * (2 * k + 1) = 2 * (k : ℤ) ^ 2 := by exact_mod_cast h
    push_cast; linear_combination 2 * h'
  have := Int.eq_one_of_mul_eq_one_right (by positivity) h1
  omega

theorem no_dvd_aux3 (k q : ℕ) (hk : 2 ≤ k) (h : q * (2 * k + 1) + k ^ 2 + k = 2 * k ^ 2) : False := by
  have h1 : ((2 * k + 1 : ℕ) : ℤ) * (4 * q - 2 * k + 3) = 3 := by
    have h' : (q : ℤ) * (2 * k + 1) + (k : ℤ) ^ 2 + k = 2 * (k : ℤ) ^ 2 := by exact_mod_cast h
    push_cast; linear_combination 4 * h'
  have hk' : (5 : ℤ) ≤ 2 * k + 1 := by omega
  rcases le_or_gt (4 * (q : ℤ) - 2 * k + 3) 0 with hm | hm
  · nlinarith
  · push_cast at h1; nlinarith

/-- The corner chord is a single `a`-edge. -/
theorem word_a (k : ℕ) (hk : 2 ≤ k) (p q r : ℕ)
    (h : p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) = k ^ 2) : p = 1 ∧ q = 0 ∧ r = 0 := by
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hr : r = 0 := by
    by_contra hr
    have : k * (k + 1) ≤ r * (k * (k + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  subst hr
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p
    · exact absurd (by simpa using h) (fun h' => no_dvd_aux k q hk h')
    · refine ⟨rfl, ?_, rfl⟩
      nlinarith
  · nlinarith

/-- Uniqueness of the representation of `2a`. -/
theorem word_2a (k : ℕ) (hk : 2 ≤ k) (p q r : ℕ)
    (h : p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) = 2 * k ^ 2) : p = 2 ∧ q = 0 ∧ r = 0 := by
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hr : r ≤ 1 := by
    by_contra hr
    have : 2 * (k * (k + 1)) ≤ r * (k * (k + 1)) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  interval_cases r
  · rcases Nat.lt_or_ge p 3 with hp | hp
    · interval_cases p
      · exact absurd (by simpa using h) (fun h' => no_dvd_aux2 k q hk h')
      · exact absurd (by nlinarith) (fun h' => no_dvd_aux k q hk h')
      · refine ⟨rfl, ?_, rfl⟩
        nlinarith
    · nlinarith
  · have hp : p = 0 := by
      by_contra hp
      have : 1 * k ^ 2 ≤ p * k ^ 2 := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    subst hp
    exact absurd (by nlinarith) (fun h' => no_dvd_aux3 k q hk h')

/-- Real, scaled form of `word_a`, the shape of `hword` in `far_chain_single_gen` with `L = a`. -/
theorem hword_a_real (k : ℕ) (hk : 2 ≤ k) {s : ℝ} (hs : 0 < s) (x y z : ℕ)
    (h : (x : ℝ) * (s * (k : ℝ) ^ 2) + y * (s * (2 * k + 1)) + z * (s * (k * (k + 1)))
      = s * (k : ℝ) ^ 2) : x + y + z = 1 := by
  have h1 : ((x * k ^ 2 + y * (2 * k + 1) + z * (k * (k + 1)) : ℕ) : ℝ) = ((k ^ 2 : ℕ) : ℝ) := by
    have : s * ((x : ℝ) * (k : ℝ) ^ 2 + y * (2 * k + 1) + z * (k * (k + 1))) = s * (k : ℝ) ^ 2 := by
      linear_combination h
    have := mul_left_cancel₀ hs.ne' this
    push_cast; exact this
  obtain ⟨hx, hy, hz⟩ := word_a k hk x y z (by exact_mod_cast h1)
  omega

theorem hword_2a_real (k : ℕ) (hk : 2 ≤ k) {s : ℝ} (hs : 0 < s) (x y z : ℕ)
    (h : (x : ℝ) * (s * (k : ℝ) ^ 2) + y * (s * (2 * k + 1)) + z * (s * (k * (k + 1)))
      = 2 * (s * (k : ℝ) ^ 2)) : x = 2 ∧ y = 0 ∧ z = 0 := by
  have h1 : ((x * k ^ 2 + y * (2 * k + 1) + z * (k * (k + 1)) : ℕ) : ℝ) = ((2 * k ^ 2 : ℕ) : ℝ) := by
    have : s * ((x : ℝ) * (k : ℝ) ^ 2 + y * (2 * k + 1) + z * (k * (k + 1))) = s * (2 * (k : ℝ) ^ 2) := by
      linear_combination h
    have := mul_left_cancel₀ hs.ne' this
    push_cast; exact this
  exact word_2a k hk x y z (by exact_mod_cast h1)

/-- At `k = 1` (degenerate tile `(1,3,2)`) the conclusion of `word_2a` fails:
`2a = 0·a + 0·b + 1·c` has the solution `(0,0,1)`. -/
theorem word_2a_fails_k1 : (0 : ℕ) * 1 ^ 2 + 0 * (2 * 1 + 1) + 1 * (1 * (1 + 1)) = 2 * 1 ^ 2 ∧
    ¬ ((0 : ℕ) = 2 ∧ (0 : ℕ) = 0 ∧ (1 : ℕ) = 0) := by decide

/-- Witness: `k = 2`, tile `(4,5,6)`: `4 = 1·4`, and `8 = 2·4` only. -/
theorem word_a_k2 : ∀ p q r : ℕ, p * 4 + q * 5 + r * 6 = 4 → p = 1 ∧ q = 0 ∧ r = 0 := by
  intro p q r h
  exact word_a 2 le_rfl p q r (by norm_num; omega)

end Erdos634.GLC

#print axioms Erdos634.GLC.word_a
#print axioms Erdos634.GLC.word_2a
#print axioms Erdos634.GLC.hword_a_real
