/-
Draft/HBCQ6.lean -- HBC item (4): Lemma Q at squarefree p = 6 (and any squarefree p >= 5 with p % 4 = 2).  Copy of
`Row2.lemmaQ_sqfreeE` with `7 <= p` weakened to `5 <= p` and the `17 <= p` branch dropped: for p % 4 = 2, `p m'^2 <= 16`
gives `m'^2 = 1` as soon as p >= 5 (p = 2 genuinely fails: cos(pi/4) = sqrt2/2), and `U^2 - 4W = p = 2 mod 4` is impossible.
-/
import Erdos634.Draft.NSQCaseB

open scoped Classical
open Real

namespace Erdos634.Geometry

theorem sqfree_not_sq2 {n : ℕ} (hn : Squarefree n) (h2 : 2 ≤ n) : ¬ IsSquare n := by
  rintro ⟨m, rfl⟩
  have hu : IsUnit m := hn m ⟨1, by ring⟩
  have : m = 1 := Nat.isUnit_iff.mp hu
  subst this; omega

theorem Row2.lemmaQ_sqfree6 {p : ℕ} (hp : Squarefree p) (hp5 : 5 ≤ p) (hp2 : p % 4 = 2) {s : ℝ}
    (hs : s ^ 2 = p) {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * π) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hc : Row2.QMu s (Real.cos θ)) :
    θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3) := by
  have hpns : ¬ IsSquare p := sqfree_not_sq2 hp (by omega)
  obtain ⟨r, hr⟩ := hθ
  obtain ⟨q₁, q₂, hq⟩ := hc
  have hsq : s ^ 2 = ((p : ℚ) : ℝ) := by rw [hs]; push_cast; ring
  -- `s` is irrational
  have hirr : ∀ q : ℚ, s ≠ q := by
    intro q hsq'
    have habs : √(p : ℝ) = |(q : ℝ)| := by
      rw [← hsq', ← hs, Real.sqrt_sq_eq_abs]
    exact (irrational_sqrt_natCast_iff.mpr hpns) ⟨|q|, by rw [habs]; push_cast; rfl⟩
  -- `x = a + b s`, `x' = a − b s`
  set a : ℚ := 2 * q₁ with ha
  set b : ℚ := 2 * q₂ with hb
  set x : ℝ := 2 * Real.cos θ with hx
  have hxab : x = (a : ℝ) + b * s := by rw [hx, hq, ha, hb]; push_cast; ring
  set x' : ℝ := (a : ℝ) - b * s with hx'
  -- `x` is integral; so is `x'`
  have hxint : IsIntegral ℤ x := by
    rw [hx, hr]; exact Real.isIntegral_two_mul_cos_rat_mul_pi r
  have hx'int : IsIntegral ℤ x' := by
    obtain ⟨P, hPm, hP⟩ := hxint
    obtain ⟨A, B, h1, h2⟩ := Row2.poly_conj hsq a b P
    rw [hxab, h1] at hP
    have hB : B = 0 := by
      by_contra hB0
      apply hirr (-A / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 0 := by rw [hB] at hP; simpa using hP
    exact ⟨P, hPm, by rw [hx', h2, hA, hB]; simp⟩
  -- `|x| ≤ 2` and `|x'| ≤ 2`
  have hxle : |x| ≤ 2 := by
    rw [hx, abs_mul, abs_two]
    have := Real.abs_cos_le_one θ
    linarith
  set n : ℕ := 2 * r.den with hn
  have hnpos : 0 < n := by positivity
  have hchebx : Row2.cheb x n = 2 := by
    rw [hx, Row2.cheb_cos θ n, hr]
    have : ((n : ℕ) : ℝ) * ((r : ℝ) * π) = (r.num : ℝ) * (2 * π) := by
      rw [hn]; push_cast
      have hd : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
      linear_combination (2 * π) * hd
    rw [this, Real.cos_int_mul_two_pi]; ring
  have hx'le : |x'| ≤ 2 := by
    obtain ⟨A, B, h1, h2⟩ := Row2.cheb_conj hsq a b n
    rw [← hxab, hchebx] at h1
    have hB : B = 0 := by
      by_contra hB0
      apply hirr ((2 - A) / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 2 := by rw [hB] at h1; simpa using h1.symm
    refine Row2.abs_le_two_of_cheb hnpos ?_
    rw [hx', h2, hA, hB]; simp
  -- `U = x + x' = 2a ∈ ℤ`, `W = x x' = a² − b² p ∈ ℤ`
  obtain ⟨U, hU⟩ := (hxint.add hx'int).exists_int_iff_exists_rat.mp
    ⟨2 * a, by rw [hxab, hx']; push_cast; ring⟩
  obtain ⟨W, hW⟩ := (hxint.mul hx'int).exists_int_iff_exists_rat.mp
    ⟨a * a - b * b * p, by rw [hxab, hx']; push_cast; linear_combination (-(b : ℝ) ^ 2) * hs⟩
  -- `V = 2b`, `p V² = U² − 4W`
  have hVZ : ((p : ℝ)) * ((2 * b : ℚ) : ℝ) ^ 2 = ((U ^ 2 - 4 * W : ℤ) : ℝ) := by
    have e1 : (U : ℝ) = 2 * a := by rw [← hU, hxab, hx']; ring
    have e2 : (W : ℝ) = a * a - b * b * p := by
      rw [← hW, hxab, hx']; linear_combination (-(b : ℝ) ^ 2) * hs
    push_cast; rw [e1, e2]; ring
  -- `pV ∈ ℤ`
  have hpVint : IsIntegral ℤ (((p * (2 * b) : ℚ)) : ℝ) := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    have : (((p * (2 * b) : ℚ)) : ℝ) ^ 2 = (((p : ℤ) * (U ^ 2 - 4 * W) : ℤ) : ℝ) := by
      push_cast at hVZ ⊢; rw [← hVZ]; ring
    rw [this]; exact Row2.isIntegral_intCast _
  obtain ⟨m, hm⟩ := hpVint.exists_int_iff_exists_rat.mp ⟨_, rfl⟩
  -- `m² = p (U² − 4W)`, so `p ∣ m`
  have hm2 : m ^ 2 = (p : ℤ) * (U ^ 2 - 4 * W) := by
    have : ((m ^ 2 : ℤ) : ℝ) = (((p : ℤ) * (U ^ 2 - 4 * W) : ℤ) : ℝ) := by
      push_cast at hVZ hm ⊢; rw [← hm, ← hVZ]; ring
    exact_mod_cast this
  obtain ⟨m', hm'⟩ : (p : ℤ) ∣ m :=
    ((Int.squarefree_natCast.mpr hp).dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp ⟨_, hm2⟩
  have hpne : p ≠ 0 := by omega
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpne
  have hZ : U ^ 2 - 4 * W = (p : ℤ) * m' ^ 2 := by
    rw [hm'] at hm2
    have : (p : ℤ) * ((p : ℤ) * m' ^ 2) = (p : ℤ) * (U ^ 2 - 4 * W) := by rw [← hm2]; ring
    exact (mul_left_cancel₀ hp0 this).symm
  -- `V = m'`
  have hVm : ((2 * b : ℚ) : ℝ) = m' := by
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hpne
    have : (p : ℝ) * ((2 * b : ℚ) : ℝ) = (p : ℝ) * m' := by
      have := hm.symm; rw [hm'] at this; push_cast at this ⊢; linarith
    exact mul_left_cancel₀ hp0' this
  -- the bound `p m'² ≤ 16`
  have hbound : (p : ℝ) * (m' : ℝ) ^ 2 ≤ 16 := by
    have hdiff : x - x' = ((2 * b : ℚ) : ℝ) * s := by rw [hxab, hx']; push_cast; ring
    have h4 : |x - x'| ≤ 4 := by
      calc |x - x'| ≤ |x| + |x'| := abs_sub _ _
        _ ≤ 4 := by linarith
    rw [hdiff, hVm] at h4
    have h16 : ((m' : ℝ) * s) ^ 2 ≤ 16 := by
      have := sq_le_sq' (abs_le.mp h4).1 (abs_le.mp h4).2
      linarith
    rw [mul_pow, hs] at h16; linarith
  have hbound' : (p : ℤ) * m' ^ 2 ≤ 16 := by exact_mod_cast hbound
  have hm'0 : m' = 0 := by
    by_contra hne
    have h1 : 0 < m' ^ 2 := by positivity
    rcases (Or.inr hp2 : 17 ≤ p ∨ p % 4 = 2) with h17 | h42
    · have h17' : (17 : ℤ) ≤ p := by exact_mod_cast h17
      nlinarith
    · have hp7' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      have hp4 : (p : ℤ) % 4 = 2 := by omega
      have hr : -1 ≤ m' ∧ m' ≤ 1 := by constructor <;> nlinarith
      have hm1 : m' ^ 2 = 1 := by
        obtain ⟨h1', h2'⟩ := hr
        have : m' = -1 ∨ m' = 1 := by omega
        rcases this with rfl | rfl <;> norm_num
      rw [hm1] at hZ
      -- `U² − 4W = p ≡ 2 (mod 4)` is impossible
      rcases Int.even_or_odd' U with ⟨k, hk | hk⟩
      · have : U ^ 2 = 4 * (k * k) := by rw [hk]; ring
        omega
      · have : U ^ 2 = 4 * (k * k + k) + 1 := by rw [hk]; ring
        omega
  -- so `b = 0` and `cos θ = a/2 ∈ ℚ`
  have hb0 : (b : ℝ) = 0 := by
    have := hVm; rw [hm'0] at this; push_cast at this; linarith
  have hcosq : ∃ q : ℚ, Real.cos θ = q := ⟨a / 2, by
    have : x = a := by rw [hxab, hb0]; ring
    rw [hx] at this; push_cast; linarith⟩
  have hmem := niven_angle_eq ⟨r, hr⟩ hcosq ⟨hθ0.le, hθπ.le⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · exact absurd h hθ0.ne'
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h hθπ.ne



end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.lemmaQ_sqfree6
