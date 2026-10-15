/-
Draft/PI3FKernel.lean -- Theorem T, step (c-arith):
the arithmetic of the length system `(a, b, c)` of a π/3 tile with invariant pair `(m₁, m₂)` and non-square
`D = (m₁+m₂)² - 16 N`.

* `split_gen`     : an integer relation `P a + Q b + R c = S w` forces `P = Q` and
                    `(P+Q)(m₁+m₂) + 2R(m₁-m₂) = 4 N w`  (generalises `E60V.splitV`, which needed `R = -Q`).
* `kernel_floor`  : **the length-kernel floor.**  If `2 N gcd(m₁+m₂, m₁-m₂) < m₁² - m₂²` (i.e. `ℓκ > 2N`), then every
                    nonzero integer relation `n₀ a + n₁ b + n₂ c = 0` has one-sided length strictly greater than the
                    side `S` of the equilateral target.  (Same shape as `InterfaceFloor.interface_floor`, for this
                    length system.)
No sorry, no native_decide.
-/
import Erdos634.Draft.E60VMod3

namespace Erdos634.Draft.PI3F

open Erdos634.Draft.CompositeE5Gen

/-- **The irrational split, general `R`.**  An integer identity `P a + Q b + R c = S w` with `D` non-square forces
`P = Q` and `(P + Q)(m₁ + m₂) + 2 R (m₁ - m₂) = 4 N w`. -/
theorem split_gen {N : ℕ} {a b c S : ℝ} (m₁ m₂ : ℤ) (hN : 0 < N)
    (h1 : (m₁ : ℝ) * (a + b - c) = 3 * S) (h2 : (m₂ : ℝ) * (a + b + c) = 3 * S)
    (harea : S ^ 2 = N * a * b) (hprod : m₁ * m₂ = 3 * (N : ℤ)) (hS0 : 0 < S)
    (hD : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)))
    (P Q R w : ℤ) (h : (P : ℝ) * a + Q * b + R * c = S * w) :
    P = Q ∧ (P + Q) * (m₁ + m₂) + 2 * R * (m₁ - m₂) = 4 * (N : ℤ) * w := by
  have hprodR : (m₁ : ℝ) * m₂ = 3 * N := by exact_mod_cast hprod
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : 2 * (N : ℝ) * (a + b) = S * (m₁ + m₂) := by
    have : 3 * ((2 * (N : ℝ) * (a + b)) - S * (m₁ + m₂)) = 0 := by
      linear_combination (m₂ : ℝ) * h1 + (m₁ : ℝ) * h2 - 2 * (a + b) * hprodR
    linarith
  have e2 : 2 * (N : ℝ) * c = S * (m₁ - m₂) := by
    have : 3 * ((2 * (N : ℝ) * c) - S * (m₁ - m₂)) = 0 := by
      linear_combination (m₁ : ℝ) * h2 - (m₂ : ℝ) * h1 - 2 * c * hprodR
    linarith
  have hX : (2 * (N : ℝ) * (a - b)) ^ 2 = S ^ 2 * (((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ) : ℝ) := by
    push_cast
    linear_combination ((2 * (N : ℝ) * (a + b) + S * (m₁ + m₂))) * e1 + 16 * (N : ℝ) * harea
  have hK : ((P : ℝ) - Q) * (2 * (N : ℝ) * (a - b)) =
      S * (((4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ)) : ℝ) := by
    push_cast
    linear_combination (4 * (N : ℝ)) * h - ((P : ℝ) + Q) * e1 - 2 * (R : ℝ) * e2
  have hPQ : P = Q := by
    by_contra hpq
    apply hD
    have hpq' : P - Q ≠ 0 := sub_ne_zero.mpr hpq
    have hL : ((P - Q : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hpq'
    refine isSquare_of_rat_sq _ (4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂)) (P - Q) hpq' ?_
    have hS2 : S ^ 2 ≠ 0 := by positivity
    have hX' : 2 * (N : ℝ) * (a - b) =
        S * ((((4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ)) : ℝ) / ((P - Q : ℤ) : ℝ)) := by
      push_cast at hL hK ⊢
      field_simp
      linear_combination hK
    rw [hX'] at hX
    have : S ^ 2 * (((((4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ)) : ℝ) /
          ((P - Q : ℤ) : ℝ))) ^ 2 = S ^ 2 * (((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ) : ℝ) := by
      rw [← hX]; ring
    exact mul_left_cancel₀ hS2 this
  refine ⟨hPQ, ?_⟩
  subst hPQ
  have h4 : S * ((4 * (N : ℤ) * w - (P + P) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ) : ℝ) = 0 := by
    rw [← hK]; ring
  rcases mul_eq_zero.mp h4 with h0 | h0
  · exact absurd h0 hS0.ne'
  · have hz : (4 * (N : ℤ) * w - (P + P) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ) = 0 := by
      exact_mod_cast h0
    linarith

/-- **The length-kernel floor.**  With `2 N gcd(m₁+m₂, m₁−m₂) < m₁² − m₂²` (`ℓκ > 2N`), every nonzero integer relation
`n₀ a + n₁ b + n₂ c = 0` has one-sided length `> S`. -/
theorem kernel_floor {N : ℕ} {a b c S : ℝ} (m₁ m₂ : ℤ) (hN : 0 < N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : (m₁ : ℝ) * (a + b - c) = 3 * S) (h2 : (m₂ : ℝ) * (a + b + c) = 3 * S)
    (harea : S ^ 2 = N * a * b) (hprod : m₁ * m₂ = 3 * (N : ℤ)) (hS0 : 0 < S)
    (hD : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)))
    (hfl : 2 * (N : ℤ) * (Int.gcd (m₁ + m₂) (m₁ - m₂) : ℤ) < (m₁ + m₂) * (m₁ - m₂))
    (n₀ n₁ n₂ : ℤ) (hn : ¬ (n₀ = 0 ∧ n₁ = 0 ∧ n₂ = 0))
    (hrel : (n₀ : ℝ) * a + n₁ * b + n₂ * c = 0) :
    S < ((max n₀ 0 : ℤ) : ℝ) * a + ((max n₁ 0 : ℤ) : ℝ) * b + ((max n₂ 0 : ℤ) : ℝ) * c := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hPQ, hz⟩ := split_gen (N := N) (a := a) (b := b) (c := c) (S := S) m₁ m₂ hN h1 h2 harea hprod hS0 hD
    n₀ n₁ n₂ 0 (by simpa using hrel)
  subst hPQ
  have e1 : 2 * (N : ℝ) * (a + b) = S * (m₁ + m₂) := by
    have hprodR : (m₁ : ℝ) * m₂ = 3 * N := by exact_mod_cast hprod
    have : 3 * ((2 * (N : ℝ) * (a + b)) - S * (m₁ + m₂)) = 0 := by
      linear_combination (m₂ : ℝ) * h1 + (m₁ : ℝ) * h2 - 2 * (a + b) * hprodR
    linarith
  have e2 : 2 * (N : ℝ) * c = S * (m₁ - m₂) := by
    have hprodR : (m₁ : ℝ) * m₂ = 3 * N := by exact_mod_cast hprod
    have : 3 * ((2 * (N : ℝ) * c) - S * (m₁ - m₂)) = 0 := by
      linear_combination (m₁ : ℝ) * h2 - (m₂ : ℝ) * h1 - 2 * c * hprodR
    linarith
  -- signs of s = m₁ + m₂ and c₀ = m₁ - m₂
  have hs : 0 < m₁ + m₂ := by
    have : (0 : ℝ) < ((m₁ + m₂ : ℤ) : ℝ) := by
      push_cast
      by_contra hneg
      push Not at hneg
      nlinarith [mul_pos hNR hNR, mul_pos hNR (add_pos ha hb), mul_pos hS0 hS0]
    exact_mod_cast this
  have hc0 : 0 < m₁ - m₂ := by
    have : (0 : ℝ) < ((m₁ - m₂ : ℤ) : ℝ) := by
      push_cast
      by_contra hneg
      push Not at hneg
      nlinarith [mul_pos hNR hc, mul_pos hS0 hS0]
    exact_mod_cast this
  set s : ℤ := m₁ + m₂ with hsdef
  set c0 : ℤ := m₁ - m₂ with hc0def
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsR' : (s : ℝ) = (m₁ : ℝ) + m₂ := by rw [hsdef]; push_cast; ring
  have hc0R' : (c0 : ℝ) = (m₁ : ℝ) - m₂ := by rw [hc0def]; push_cast; ring
  have hc0R : (0 : ℝ) < c0 := by exact_mod_cast hc0
  -- relation: n₀ s + n₂ c0 = 0
  have hz' : n₀ * s = - (n₂ * c0) := by linarith
  -- gcd decomposition
  have hg : 0 < Int.gcd s c0 := Int.gcd_pos_of_ne_zero_left _ hs.ne'
  obtain ⟨s', hs'⟩ := Int.gcd_dvd_left (a := s) (b := c0)
  obtain ⟨c0', hc0'⟩ := Int.gcd_dvd_right (a := s) (b := c0)
  set g : ℤ := (Int.gcd s c0 : ℤ) with hgdef
  have hgpos : 0 < g := Int.natCast_pos.mpr hg
  have hcop : IsCoprime s' c0' := by
    have h1 : Int.gcd s c0 = Int.natAbs g * Int.gcd s' c0' := by
      conv_lhs => rw [hs', hc0']
      exact Int.gcd_mul_left _ _ _
    have h2 : Int.natAbs g = Int.gcd s c0 := by simp [hgdef]
    rw [h2] at h1
    have h3 : Int.gcd s' c0' = 1 := by
      have : Int.gcd s c0 * 1 = Int.gcd s c0 * Int.gcd s' c0' := by rw [mul_one]; exact h1
      exact (Nat.eq_of_mul_eq_mul_left hg this).symm
    exact Int.isCoprime_iff_gcd_eq_one.mpr h3
  have hs'pos : 0 < s' := by
    by_contra h0; push Not at h0; nlinarith
  have hc0'pos : 0 < c0' := by
    by_contra h0; push Not at h0; nlinarith
  have hcancel : n₀ * s' = - (n₂ * c0') := by
    have : g * (n₀ * s') = g * (- (n₂ * c0')) := by
      rw [hs', hc0'] at hz'; linarith
    exact mul_left_cancel₀ hgpos.ne' this
  have hfl' : 2 * (N : ℤ) < g * s' * c0' := by
    have : 2 * (N : ℤ) * g < g * (g * s' * c0') := by
      have e : s * c0 = g * (g * s' * c0') := by rw [hs', hc0']; ring
      rw [← e]; exact hfl
    nlinarith
  rcases lt_trichotomy n₀ 0 with hneg | hzero | hpos
  · -- n₀ < 0 : n₂ > 0, the `c`-side is the long one
    have hn2 : 0 < n₂ := by
      by_contra h0; push Not at h0
      nlinarith [mul_pos hs'pos hc0'pos]
    have hdvd : s' ∣ n₂ := by
      have : s' ∣ n₂ * c0' := ⟨-n₀, by linarith⟩
      exact hcop.dvd_of_dvd_mul_right this
    have hge : s' ≤ n₂ := Int.le_of_dvd hn2 hdvd
    have hmax2 : ((max n₂ 0 : ℤ) : ℝ) = n₂ := by
      rw [max_eq_left hn2.le]
    have hbig : 2 * (N : ℤ) < n₂ * c0 := by
      rw [hc0']
      nlinarith [mul_pos hgpos hc0'pos]
    have hbigR : 2 * (N : ℝ) < n₂ * c0 := by exact_mod_cast hbig
    have hm0 : (0 : ℝ) ≤ ((max n₀ 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hm1 : (0 : ℝ) ≤ ((max n₀ 0 : ℤ) : ℝ) := hm0
    rw [hmax2]
    have hn2R : (0 : ℝ) < n₂ := by exact_mod_cast hn2
    have key : 0 < 2 * (N : ℝ) * (n₂ * c - S) := by
      calc 2 * (N : ℝ) * (n₂ * c - S) = n₂ * (2 * N * c) - 2 * N * S := by ring
        _ = n₂ * (S * c0) - 2 * N * S := by rw [e2, hc0R']
        _ = S * (n₂ * c0 - 2 * N) := by ring
        _ > 0 := mul_pos hS0 (sub_pos.mpr hbigR)
    have key2 : 0 < (n₂ : ℝ) * c - S := (mul_pos_iff_of_pos_left (by positivity)).mp key
    nlinarith [mul_nonneg hm0 ha.le, mul_nonneg hm1 hb.le]
  · exfalso
    subst hzero
    apply hn
    refine ⟨rfl, rfl, ?_⟩
    have : n₂ * c0' = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hc0'pos.ne'
  · -- n₀ > 0 : the `a`,`b` sides are long
    have hdvd : c0' ∣ n₀ := by
      have : c0' ∣ n₀ * s' := ⟨-n₂, by linarith⟩
      exact hcop.symm.dvd_of_dvd_mul_right this
    have hge : c0' ≤ n₀ := Int.le_of_dvd hpos hdvd
    have hbig : 2 * (N : ℤ) < n₀ * s := by
      rw [hs']
      nlinarith [mul_pos hgpos hs'pos]
    have hbigR : 2 * (N : ℝ) < n₀ * s := by exact_mod_cast hbig
    have hmax0 : ((max n₀ 0 : ℤ) : ℝ) = n₀ := by rw [max_eq_left hpos.le]
    have hmax1 : ((max n₀ 0 : ℤ) : ℝ) = n₀ := hmax0
    have hm2 : (0 : ℝ) ≤ ((max n₂ 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    rw [hmax0]
    have hn0R : (0 : ℝ) < n₀ := by exact_mod_cast hpos
    have key : 0 < 2 * (N : ℝ) * (n₀ * (a + b) - S) := by
      calc 2 * (N : ℝ) * (n₀ * (a + b) - S) = n₀ * (2 * N * (a + b)) - 2 * N * S := by ring
        _ = n₀ * (S * s) - 2 * N * S := by rw [e1, hsR']
        _ = S * (n₀ * s - 2 * N) := by ring
        _ > 0 := mul_pos hS0 (sub_pos.mpr hbigR)
    have key2 : 0 < (n₀ : ℝ) * (a + b) - S := (mul_pos_iff_of_pos_left (by positivity)).mp key
    nlinarith [mul_nonneg hm2 hc.le]

end Erdos634.Draft.PI3F

#print axioms Erdos634.Draft.PI3F.split_gen
#print axioms Erdos634.Draft.PI3F.kernel_floor
