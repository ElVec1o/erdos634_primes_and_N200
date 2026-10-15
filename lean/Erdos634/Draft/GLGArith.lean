import Mathlib.Tactic

/-!
# Word arithmetic for the leaf-G family `N = 4(2k+1)`, tile `(k², 2k+1, k(k+1))`, `k ≥ 3`

Pure arithmetic, for the leaf `CaseGClosed`:
* `leg_words`  : legs `X = 2k(2k+1)`: `(p,q,r) ∈ {(0,2k,0),(1,k,1),(2,0,2)}`;
* `base_words` : base `Y = 2(k+1)(2k+1)` with `r ≥ 1`: `(p,q,r) ∈ {(1,k+2,1),(2,2,2)}`
  (the only other word `(0,2k+2,0)` has `r = 0`).
-/

namespace Erdos634.GLG

/-- `p k + r (k+1) = 2k+1 ⇒ (p,r) = (1,1)`, `k ≥ 3`. -/
theorem lin_a (k p r : ℕ) (hk : 3 ≤ k) (h : p * k + r * (k + 1) = 2 * k + 1) : p = 1 ∧ r = 1 := by
  have hr : r ≤ 1 := by
    by_contra hr; push Not at hr
    have : 2 * (k + 1) ≤ r * (k + 1) := Nat.mul_le_mul_right _ hr
    omega
  have hp : p ≤ 2 := by
    by_contra hp; push Not at hp
    have : 3 * k ≤ p * k := Nat.mul_le_mul_right _ hp
    omega
  interval_cases r <;> interval_cases p <;> omega

/-- `p k + r (k+1) = 4k+2 ⇒ (p,r) = (2,2)`, `k ≥ 3`. -/
theorem lin_b (k p r : ℕ) (hk : 3 ≤ k) (h : p * k + r * (k + 1) = 4 * k + 2) : p = 2 ∧ r = 2 := by
  have hr : r ≤ 3 := by
    by_contra hr; push Not at hr
    have : 4 * (k + 1) ≤ r * (k + 1) := Nat.mul_le_mul_right _ hr
    omega
  have hp : p ≤ 4 := by
    by_contra hp; push Not at hp
    have : 5 * k ≤ p * k := Nat.mul_le_mul_right _ hp
    omega
  interval_cases r <;> interval_cases p <;> omega

theorem k_dvd_q (k q c : ℕ) (h : k ∣ q * (2 * k + 1) + k * c) : k ∣ q := by
  have h1 : k ∣ q * (2 * k + 1) := (Nat.dvd_add_left (Dvd.intro _ rfl)).mp h
  have hc : Nat.Coprime k (2 * k + 1) := by
    simp
  exact hc.dvd_of_dvd_mul_right h1

theorem leg_words (k p q r : ℕ) (hk : 3 ≤ k)
    (h : p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) = 2 * k * (2 * k + 1)) :
    (p = 0 ∧ q = 2 * k ∧ r = 0) ∨ (p = 1 ∧ q = k ∧ r = 1) ∨ (p = 2 ∧ q = 0 ∧ r = 2) := by
  have hdvd : k ∣ q * (2 * k + 1) + k * (p * k + r * (k + 1)) :=
    ⟨2 * (2 * k + 1) , by nlinarith⟩
  obtain ⟨t, ht⟩ := k_dvd_q k q _ hdvd
  have ht2 : t ≤ 2 := by
    by_contra hh; push Not at hh
    have : q * (2 * k + 1) > 2 * k * (2 * k + 1) := by
      have : q ≥ 3 * k := by rw [ht]; nlinarith
      nlinarith
    omega
  have hk0 : 0 < k := by omega
  interval_cases t
  · -- q = 0
    have e : p * k + r * (k + 1) = 4 * k + 2 := by
      have : k * (p * k + r * (k + 1)) = k * (4 * k + 2) := by subst ht; nlinarith
      exact Nat.eq_of_mul_eq_mul_left hk0 this
    obtain ⟨h1, h2⟩ := lin_b k p r hk e
    right; right; exact ⟨h1, by omega, h2⟩
  · have e : p * k + r * (k + 1) = 2 * k + 1 := by
      have : k * (p * k + r * (k + 1)) = k * (2 * k + 1) := by subst ht; nlinarith
      exact Nat.eq_of_mul_eq_mul_left hk0 this
    obtain ⟨h1, h2⟩ := lin_a k p r hk e
    right; left; exact ⟨h1, by omega, h2⟩
  · have hq : q = 2 * k := by omega
    subst hq
    have hp0 : p = 0 := by
      by_contra hp; have : 1 ≤ p := Nat.pos_of_ne_zero hp
      nlinarith
    have hr0 : r = 0 := by
      by_contra hp; have : 1 ≤ r := Nat.pos_of_ne_zero hp
      subst hp0; nlinarith
    left; exact ⟨hp0, rfl, hr0⟩

theorem base_words (k p q r : ℕ) (hk : 3 ≤ k) (hr : 1 ≤ r)
    (h : p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) = 2 * (k + 1) * (2 * k + 1)) :
    (p = 1 ∧ q = k + 2 ∧ r = 1) ∨ (p = 2 ∧ q = 2 ∧ r = 2) := by
  -- q = 2 + s k
  have hq2 : q ≤ 2 * k + 2 := by
    by_contra hh; push Not at hh
    have : q * (2 * k + 1) ≥ (2 * k + 3) * (2 * k + 1) := Nat.mul_le_mul_right _ hh
    nlinarith
  have hdvd : (k : ℤ) ∣ ((q : ℤ) - 2) * (2 * k + 1) := by
    refine ⟨2 * (2 * k + 1) - p * k - r * (k + 1) , ?_⟩
    have : (p : ℤ) * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) = 2 * (k + 1) * (2 * k + 1) := by
      exact_mod_cast h
    linear_combination this
  have hc : IsCoprime (k : ℤ) (2 * k + 1) := by
    refine ⟨-2, 1, by ring⟩
  have hd := hc.dvd_of_dvd_mul_right hdvd
  obtain ⟨s, hs⟩ := hd
  have hs3 : s = 0 ∨ s = 1 ∨ s = 2 := by
    have hq2' : (q : ℤ) ≤ 2 * k + 2 := by exact_mod_cast hq2
    have hqn : (0 : ℤ) ≤ q := by positivity
    have hk3 : (3 : ℤ) ≤ k := by exact_mod_cast hk
    have : s ≥ 0 := by
      by_contra hneg; push Not at hneg
      nlinarith
    have : s ≤ 2 := by
      by_contra hneg; push Not at hneg
      nlinarith
    omega
  have key : ∀ q0 : ℕ, (q : ℤ) = q0 + s * k → q = q0 + s.toNat * k := by
    intro q0 hq0
    have : s = (s.toNat : ℤ) := by omega
    rw [this] at hq0; exact_mod_cast hq0
  rcases hs3 with rfl | rfl | rfl
  · have hq : q = 2 := by omega
    subst hq
    have e : p * k + r * (k + 1) = 4 * k + 2 := by
      have : k * (p * k + r * (k + 1)) = k * (4 * k + 2) := by nlinarith
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    obtain ⟨h1, h2⟩ := lin_b k p r hk e
    right; exact ⟨h1, rfl, h2⟩
  · have hq : q = k + 2 := by omega
    subst hq
    have e : p * k + r * (k + 1) = 2 * k + 1 := by
      have : k * (p * k + r * (k + 1)) = k * (2 * k + 1) := by nlinarith
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    obtain ⟨h1, h2⟩ := lin_a k p r hk e
    left; exact ⟨h1, rfl, h2⟩
  · exfalso
    have hq : q = 2 * k + 2 := by omega
    subst hq
    nlinarith [Nat.mul_le_mul_right (k * (k + 1)) hr]

end Erdos634.GLG
