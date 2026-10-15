/-
Draft/R8ZFLeaf.lean -- the F3 / F3' leaf with the integer `z = ν c` kept.  No sorry / native_decide.

`R8Gen2.F3.f3_core` and `F3Prime.f3prime_core` already derive, from `Paper.cor_int` (fluxes) and the F3/F3' area formula,
THREE INTEGERS  s = nu(2a+b) (resp. nu(a+2b)),  j = nu b (resp. nu a),  z = nu c  with 4N = 3(s+j)(s+3j)  -- and the
identity  k^2 = 3(4z^2 - s^2),  k = 3j,  i.e.  4 z^2 = s^2 + 3 j^2.   `NoF3 N` discarded z.  Keeping it:

    NoF3z N :  forall s j z : Z, 0<j<s, 0<z, 4N = 3(s+j)(s+3j)  ->  4 z^2 /= s^2 + 3 j^2.

Every arithmetic F3 survivor with IRRATIONAL c (s^2+3j^2 not a perfect square) satisfies `NoF3z`.  No geometry is needed.
Here: the copies `F3.f3_prime_contradiction`, `F3Prime.f3prime_contradiction` with hypothesis `NoF3z N`, then
`gapR8_of_arith_z`, the decidable `NoF3zChk`, the leaf `LeafR8z`, the condition `C'' N` and
    theorem not_tile_of_conditions'' (N : N) (h : C'' N) (D : CongruentDissection N) : False.
The copied proofs are those of `ChainCompositeR8b`, except `NoF3 N` -> `NoF3z N` and the final
step (see `h9` in `f3_core`, `f3prime_core`).
-/
import Erdos634.Draft.AllN2Cond

namespace Erdos634.Draft.R8ZF

/-- `NoF3` with the integer `z = nu c` kept: no integers `0<j<s`, `0<z` with `4N = 3(s+j)(s+3j)` and `4z^2 = s^2+3j^2`. -/
def NoF3z (N : ℕ) : Prop :=
  ∀ s j z : ℤ, 0 < j → j < s → 0 < z → 4 * (N : ℤ) = 3 * (s + j) * (s + 3 * j) →
    4 * z ^ 2 ≠ s ^ 2 + 3 * j ^ 2

/-- `NoF3 N ⇒ NoF3z N`: the new leaf is weaker. -/
theorem noF3z_of_noF3 {N : ℕ} (h : Erdos634.Draft.R8Gen2.NoF3 N) : NoF3z N :=
  fun s j _ hj hjs _ h4 _ => h s j hj hjs h4

end Erdos634.Draft.R8ZF

namespace Erdos634.Draft.R8ZF.F3

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F3AreaFormula (F3_area_formula)

/-! ## Auxiliary -/

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- F3 factor identities
private lemma F3_factor_alpha (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) = ν * (c - 2 * a - b) * (c + a - b) := by
  linear_combination -2 * ν * hc2

private lemma F3_factor_beta (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) = -(ν * (c + 2 * a + b) * (c + b - a)) := by
  linear_combination 2 * ν * hc2

/-! ## Core: given integers s = ν(2a+b) > 0 and z = νc > 0, derive False -/

private lemma f3_core
    {N : ℕ} (hNo : NoF3z N)
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (a + 2 * b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (2 * a + b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  -- Establish the key ℝ identities for the two factors
  have hA_R : (N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      6 * ν ^ 2 * (a + b) * (2 * a + b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hB_R : (N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      2 * ν ^ 2 * (2 * a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  -- The ℝ identity: N·4s² = (N+3s²−3z²)·(N+s²−3z²)
  have hR_eq : (N : ℝ) * 4 * (s : ℝ) ^ 2 =
      ((N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
      ((N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
    rw [hA_R, hB_R, hNreal, hs_R]; ring
  -- Cast to ℤ
  have hZ_eq : (N : ℤ) * 4 * s ^ 2 =
      ((N : ℤ) + 3 * s ^ 2 - 3 * z ^ 2) * ((N : ℤ) + s ^ 2 - 3 * z ^ 2) := by
    have hRZ : ((N : ℤ) : ℝ) * 4 * (s : ℝ) ^ 2 =
        (((N : ℤ) : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
        (((N : ℤ) : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
      push_cast; exact hR_eq
    exact_mod_cast hRZ
  -- Define M = N+2s²−3z², show M² = s²(s²+4N)
  set M : ℤ := (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 with hM_def
  have hM_sq : M ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := by linear_combination -hZ_eq
  -- s | M (from s² | M²)
  have hs_dvd : s ∣ M := by
    have hsq_dvd : s ^ 2 ∣ M ^ 2 := ⟨s ^ 2 + 4 * (N : ℤ), by linarith [hM_sq]⟩
    exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hsq_dvd
  -- Set m = M/s, derive m² = s²+4N
  obtain ⟨m, hm⟩ := hs_dvd   -- M = s * m
  have hm_sq : m ^ 2 = s ^ 2 + 4 * (N : ℤ) := by
    have : s ^ 2 * m ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) :=
      calc s ^ 2 * m ^ 2 = (s * m) ^ 2 := by ring
        _ = M ^ 2 := by rw [← hm]
        _ = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := hM_sq
    exact Int.eq_of_mul_eq_mul_left (pow_ne_zero _ hs_pos.ne') this
  -- Set k = m − 2s; compute k·s = N − 3z²
  set k : ℤ := m - 2 * s
  have hks : k * s = (N : ℤ) - 3 * z ^ 2 := by
    have h1 : s * m = M := hm.symm ▸ rfl
    have h2 : M = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := hM_def
    have h3 : m * s = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := by linarith [mul_comm s m, h1, h2]
    nlinarith [h3]
  -- k² = 3(4z²−s²) via k² = m² − 4ms + 4s² = (s²+4N) − 4(N−3z²+2s²) + 4s²
  have hm_s : m * s = (N : ℤ) - 3 * z ^ 2 + 2 * s ^ 2 := by nlinarith [hks]
  have hk_sq : k ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by nlinarith [hm_sq, hm_s]
  -- 4z² > s² (from ν²(2a+b)² < ν²·4c² under hc2)
  have h4z2s2_nn : 0 ≤ 4 * z ^ 2 - s ^ 2 := by
    have hineq : (s : ℝ) ^ 2 < 4 * (z : ℝ) ^ 2 := by
      rw [hs_R, hz_R]
      have : (2 * a + b) ^ 2 < 4 * c ^ 2 := by nlinarith [hc2, mul_pos ha hb]
      nlinarith [sq_pos_of_pos hν]
    have hZ : (s : ℤ) ^ 2 < 4 * z ^ 2 := by exact_mod_cast hineq
    linarith
  -- 3 | k (from 3 | k²)
  have h3_dvd_k_sq : (3 : ℤ) ∣ k ^ 2 := ⟨4 * z ^ 2 - s ^ 2, by linarith [hk_sq]⟩
  have h3_dvd_k : (3 : ℤ) ∣ k :=
    (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h3_dvd_k_sq
  obtain ⟨j, hj⟩ := h3_dvd_k   -- k = 3j
  have hmk : m = 3 * j + 2 * s := by simp only [k] at hj; linarith
  have hkR : (k : ℝ) = 3 * (ν * b) := by
    have h1 : (k : ℝ) * s = (N : ℝ) - 3 * (z : ℝ) ^ 2 := by exact_mod_cast hks
    have h2 : (N : ℝ) - 3 * (z : ℝ) ^ 2 = 3 * (ν * b) * s := by
      rw [hs_R, hz_R, hNreal]; linear_combination (-3 * ν ^ 2) * hc2
    have hs_ne : (s : ℝ) ≠ 0 := by exact_mod_cast hs_pos.ne'
    exact mul_right_cancel₀ hs_ne (h1.trans h2)
  have hjR : (j : ℝ) = ν * b := by
    have h3j : (k : ℝ) = 3 * (j : ℝ) := by exact_mod_cast hj
    linarith
  have hjpos : 0 < j := by
    have : (0 : ℝ) < (j : ℝ) := by rw [hjR]; exact mul_pos hν hb
    exact_mod_cast this
  have hjs : j < s := by
    have : (j : ℝ) < (s : ℝ) := by
      rw [hjR, hs_R]; nlinarith [mul_pos hν ha]
    exact_mod_cast this
  have h4N : (4 : ℤ) * (N : ℤ) = 3 * (s + j) * (s + 3 * j) := by
    rw [hmk] at hm_sq; linear_combination (-1 : ℤ) * hm_sq
  have h9 : (3 * j) ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by rw [← hj]; exact hk_sq
  exact hNo s j z hjpos hjs hz_pos h4N (by nlinarith [h9])

/-! ## Main theorem -/

/-- No prime `N > 3` admits a `CongruentDissection` with a 2π/3 model and an F3Data target. -/
theorem f3_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNo : NoF3z N) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  -- Area formula
  have hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (a + 2 * b) :=
    F3_area_formula D hm ht ha hb hν
  -- cor_int gives Mα, Mβ with flux equations
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  -- lemmaW_F3 gives the explicit flux values (two sign choices each)
  have hW_α := Row8.lemmaW_F3_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F3_beta D.target hα ht
  -- Factor identities under hc2
  have hfact_α := F3_factor_alpha ν hc2
  have hfact_β := F3_factor_beta ν hc2
  -- Divisor positivity
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  -- Mα + Mβ and Mβ − Mα are both even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  -- Handle all 4 sign combinations
  -- In each case: derive hMα_val and hMβ_val, extract s = ν(2a+b) and z = νc from
  -- the sum/difference of Mα, Mβ, then apply f3_core.
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα*(c+a-b) = ν*(c-2a-b)*(c+a-b), Mβ*(c+b-a) = -ν*(c+2a+b)*(c+b-a)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (c - 2 * a - b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = -(ν * (c + 2 * a + b)) :=
      mul_right_cancel₀ hdiv_β.ne' (by linear_combination hMβ_R.trans hfact_β)
    -- 2ν(2a+b) = -(Mα+Mβ); 2νc = -(Mβ-Mα)
    have h2s : 2 * (ν * (2 * a + b)) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (-p : ℝ) = ν * (2 * a + b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (-q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hNo ha hb hν hc2 hNreal (-p) hs_pos (by exact_mod_cast hs_R)
      (-q) hz_pos (by exact_mod_cast hz_R)
  · -- (+-): Mα = ν(c-2a-b), Mβ = ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c - 2 * a - b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = ν * (c + 2 * a + b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(2a+b) = Mβ-Mα; 2νc = Mα+Mβ
    have h2s : 2 * (ν * (2 * a + b)) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (q : ℝ) = ν * (2 * a + b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hNo ha hb hν hc2 hNreal q hs_pos (by exact_mod_cast hs_R)
      p hz_pos (by exact_mod_cast hz_R)
  · -- (-+): Mα = -ν(c-2a-b), Mβ = -ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c - 2 * a - b)) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = -(ν * (c + 2 * a + b)) :=
      mul_right_cancel₀ hdiv_β.ne' (by linear_combination hMβ_R.trans hfact_β)
    -- 2ν(2a+b) = -(Mβ-Mα); 2νc = -(Mα+Mβ)
    have h2s : 2 * (ν * (2 * a + b)) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (-q : ℝ) = ν * (2 * a + b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (-p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hNo ha hb hν hc2 hNreal (-q) hs_pos (by exact_mod_cast hs_R)
      (-p) hz_pos (by exact_mod_cast hz_R)
  · -- (--): Mα = -ν(c-2a-b), Mβ = ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c - 2 * a - b)) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = ν * (c + 2 * a + b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(2a+b) = Mα+Mβ; 2νc = Mβ-Mα
    have h2s : 2 * (ν * (2 * a + b)) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (p : ℝ) = ν * (2 * a + b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hNo ha hb hν hc2 hNreal p hs_pos (by exact_mod_cast hs_R)
      q hz_pos (by exact_mod_cast hz_R)


end Erdos634.Draft.R8ZF.F3

namespace Erdos634.Draft.R8ZF.F3Prime

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F3PrimeAreaFormula (F3prime_area_formula)

/-! ## Auxiliary -/

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- F3′ factor identities (a↔b of F3)
private lemma F3prime_factor_alpha (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) = -(ν * (c + a + 2 * b) * (c + a - b)) := by
  linear_combination 2 * ν * hc2

private lemma F3prime_factor_beta (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) = ν * (c - a - 2 * b) * (c + b - a) := by
  linear_combination -2 * ν * hc2

/-! ## Core: given integers s = ν(a+2b) > 0 and z = νc > 0, derive False -/

private lemma f3prime_core
    {N : ℕ} (hNo : NoF3z N)
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) (hcpos : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (a + 2 * b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  have hA_R : (N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      6 * ν ^ 2 * (a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hB_R : (N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      2 * ν ^ 2 * (2 * a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hR_eq : (N : ℝ) * 4 * (s : ℝ) ^ 2 =
      ((N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
      ((N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
    rw [hA_R, hB_R, hNreal, hs_R]; ring
  have hZ_eq : (N : ℤ) * 4 * s ^ 2 =
      ((N : ℤ) + 3 * s ^ 2 - 3 * z ^ 2) * ((N : ℤ) + s ^ 2 - 3 * z ^ 2) := by
    have hRZ : ((N : ℤ) : ℝ) * 4 * (s : ℝ) ^ 2 =
        (((N : ℤ) : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
        (((N : ℤ) : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
      push_cast; exact hR_eq
    exact_mod_cast hRZ
  set M : ℤ := (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 with hM_def
  have hM_sq : M ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := by linear_combination -hZ_eq
  have hs_dvd : s ∣ M := by
    have hsq_dvd : s ^ 2 ∣ M ^ 2 := ⟨s ^ 2 + 4 * (N : ℤ), by linarith [hM_sq]⟩
    exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hsq_dvd
  obtain ⟨m, hm⟩ := hs_dvd
  have hm_sq : m ^ 2 = s ^ 2 + 4 * (N : ℤ) := by
    have : s ^ 2 * m ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) :=
      calc s ^ 2 * m ^ 2 = (s * m) ^ 2 := by ring
        _ = M ^ 2 := by rw [← hm]
        _ = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := hM_sq
    exact Int.eq_of_mul_eq_mul_left (pow_ne_zero _ hs_pos.ne') this
  set k : ℤ := m - 2 * s
  have hks : k * s = (N : ℤ) - 3 * z ^ 2 := by
    have h1 : s * m = M := hm.symm ▸ rfl
    have h2 : M = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := hM_def
    have h3 : m * s = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := by linarith [mul_comm s m, h1, h2]
    nlinarith [h3]
  have hm_s : m * s = (N : ℤ) - 3 * z ^ 2 + 2 * s ^ 2 := by nlinarith [hks]
  have hk_sq : k ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by nlinarith [hm_sq, hm_s]
  have h4z2s2_nn : 0 ≤ 4 * z ^ 2 - s ^ 2 := by
    have hineq : (s : ℝ) ^ 2 < 4 * (z : ℝ) ^ 2 := by
      rw [hs_R, hz_R]
      have : (a + 2 * b) ^ 2 < 4 * c ^ 2 := by nlinarith [hc2, sq_pos_of_pos ha]
      nlinarith [sq_pos_of_pos hν]
    have hZ : (s : ℤ) ^ 2 < 4 * z ^ 2 := by exact_mod_cast hineq
    linarith
  have h3_dvd_k_sq : (3 : ℤ) ∣ k ^ 2 := ⟨4 * z ^ 2 - s ^ 2, by linarith [hk_sq]⟩
  have h3_dvd_k : (3 : ℤ) ∣ k :=
    (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h3_dvd_k_sq
  obtain ⟨j, hj⟩ := h3_dvd_k   -- k = 3j
  have hmk : m = 3 * j + 2 * s := by simp only [k] at hj; linarith
  have hkR : (k : ℝ) = 3 * (ν * a) := by
    have h1 : (k : ℝ) * s = (N : ℝ) - 3 * (z : ℝ) ^ 2 := by exact_mod_cast hks
    have h2 : (N : ℝ) - 3 * (z : ℝ) ^ 2 = 3 * (ν * a) * s := by
      rw [hs_R, hz_R, hNreal]; linear_combination (-3 * ν ^ 2) * hc2
    have hs_ne : (s : ℝ) ≠ 0 := by exact_mod_cast hs_pos.ne'
    exact mul_right_cancel₀ hs_ne (h1.trans h2)
  have hjR : (j : ℝ) = ν * a := by
    have h3j : (k : ℝ) = 3 * (j : ℝ) := by exact_mod_cast hj
    linarith
  have hjpos : 0 < j := by
    have : (0 : ℝ) < (j : ℝ) := by rw [hjR]; exact mul_pos hν ha
    exact_mod_cast this
  have hjs : j < s := by
    have : (j : ℝ) < (s : ℝ) := by
      rw [hjR, hs_R]; nlinarith [mul_pos hν hb]
    exact_mod_cast this
  have h4N : (4 : ℤ) * (N : ℤ) = 3 * (s + j) * (s + 3 * j) := by
    rw [hmk] at hm_sq; linear_combination (-1 : ℤ) * hm_sq
  have h9 : (3 * j) ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by rw [← hj]; exact hk_sq
  exact hNo s j z hjpos hjs hz_pos h4N (by nlinarith [h9])

/-! ## Main theorem -/

/-- No prime `N > 3` admits a `CongruentDissection` with a 2π/3 model and an F3PrimeData target. -/
theorem f3prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNo : NoF3z N) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  have hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b) :=
    F3prime_area_formula D hm ht ha hb hν
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  have hW_α := Row8.lemmaW_F3prime_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F3prime_beta D.target hα ht
  have hfact_α := F3prime_factor_alpha ν hc2
  have hfact_β := F3prime_factor_beta ν hc2
  -- Divisors: α-divisor = (c+a-b), β-divisor = (c+b-a)
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα = -(ν*(c+a+2b)), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    -- 2ν(a+2b) = -(Mα+Mβ); 2νc = Mβ-Mα
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (-p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hNo ha hb hν hcpos hc2 hNreal (-p) hs_pos (by exact_mod_cast hs_R)
      q hz_pos (by exact_mod_cast hz_R)
  · -- (+-): Mα = -(ν*(c+a+2b)), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(a+2b) = Mβ-Mα; 2νc = -(Mα+Mβ)
    have h2s : 2 * (ν * (a + 2 * b)) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (-p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hNo ha hb hν hcpos hc2 hNreal q hs_pos (by exact_mod_cast hs_R)
      (-p) hz_pos (by exact_mod_cast hz_R)
  · -- (-+): Mα = ν*(c+a+2b), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    -- 2ν(a+2b) = -(Mβ-Mα); 2νc = Mα+Mβ
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (-q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hNo ha hb hν hcpos hc2 hNreal (-q) hs_pos (by exact_mod_cast hs_R)
      p hz_pos (by exact_mod_cast hz_R)
  · -- (--): Mα = ν*(c+a+2b), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(a+2b) = Mα+Mβ; 2νc = -(Mβ-Mα)
    have h2s : 2 * (ν * (a + 2 * b)) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (-q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hNo ha hb hν hcpos hc2 hNreal p hs_pos (by exact_mod_cast hs_R)
      (-q) hz_pos (by exact_mod_cast hz_R)


end Erdos634.Draft.R8ZF.F3Prime

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.R8ZF

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.R8F2to4Bridge
open Erdos634.Draft.R8Gen2 (NoF2 NoF4z)

/-- **`GapR8 N` from `NoF2`, `NoF3z`, `NoF4z`.**  `gapR8_of_arith2` with `NoF3` weakened to `NoF3z`. -/
theorem gapR8_of_arith_z (N : ℕ) (h2 : NoF2 N) (h3 : NoF3z N) (h4 : NoF4z N) : Chain15.GapR8 N := by
  intro D α a b c hirr hm hshape
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4s | hF4'
  · obtain ⟨ν, hνpos, hd⟩ := f2_data_of_shape D hm hF2
    exact Erdos634.Draft.R8Gen2.F2.f2_prime_contradiction D hirr hm hd ha0 hb0 hνpos h2
  · obtain ⟨ν, hνpos, hd⟩ := f3_data_of_shape D hm hF3
    exact F3.f3_prime_contradiction D hirr hm hd ha0 hb0 hνpos h3
  · obtain ⟨ν, hνpos, hd⟩ := f3prime_data_of_shape D hm hF3'
    exact F3Prime.f3prime_contradiction D hirr hm hd ha0 hb0 hνpos h3
  · obtain ⟨ν, hνpos, hd⟩ := f4_data_of_shape D hm hF4s
    exact Erdos634.Draft.R8Gen2.F4.f4_prime_contradiction D hirr hm hd ha0 hb0 hνpos h4
  · obtain ⟨ν, hνpos, hd⟩ := f4prime_data_of_shape D hm hF4'
    exact Erdos634.Draft.R8Gen2.F4Prime.f4prime_prime_contradiction D hirr hm hd ha0 hb0 hνpos h4

/-! ## The decidable check -/

/-- Decidable form of `NoF3z`: every solution `(s, j)` of `4N = 3(s+j)(s+3j)` in the box has `s^2+3j^2` not four times a
square. -/
def NoF3zChk (N : ℕ) : Prop :=
  ∀ j ≤ N, 0 < j → j * j ≤ N → ∀ s ≤ 2 * N, j < s → s * s ≤ 2 * N →
    4 * N = 3 * (s + j) * (s + 3 * j) →
    ¬ ((s * s + 3 * (j * j)) % 4 = 0 ∧
        Nat.sqrt ((s * s + 3 * (j * j)) / 4) * Nat.sqrt ((s * s + 3 * (j * j)) / 4) =
          (s * s + 3 * (j * j)) / 4)

instance (N : ℕ) : Decidable (NoF3zChk N) := by unfold NoF3zChk; infer_instance

theorem noF3z_of_chk {N : ℕ} (h : NoF3zChk N) : NoF3z N := by
  intro s j z hj hjs hz heq hzeq
  lift j to ℕ using hj.le
  lift s to ℕ using (by omega)
  lift z to ℕ using hz.le
  have heq' : 4 * N = 3 * (s + j) * (s + 3 * j) := by exact_mod_cast heq
  have hj0 : 0 < j := by exact_mod_cast hj
  have hjs' : j < s := by exact_mod_cast hjs
  have h1 : j * j ≤ N := by nlinarith
  have h2 : s * s ≤ 2 * N := by nlinarith
  have hzeq' : 4 * (z * z) = s * s + 3 * (j * j) := by
    have : (4 * (z * z) : ℤ) = s * s + 3 * (j * j) := by nlinarith [hzeq]
    exact_mod_cast this
  apply h j (by nlinarith) hj0 h1 s (by nlinarith) hjs' h2 heq'
  have h3 : (s * s + 3 * (j * j)) / 4 = z * z := by omega
  refine ⟨by omega, ?_⟩
  rw [h3, Nat.sqrt_eq]

/-- `NoF3Chk N ⇒ NoF3zChk N` (the new check is weaker). -/
theorem noF3zChk_of_noF3Chk {N : ℕ} (h : Erdos634.Draft.AllNExclusion.NoF3Chk N) : NoF3zChk N := by
  intro j hjN hj hj2 s hs hjs hs2 heq _
  exact absurd heq (h j hjN hj hj2 s hs hjs hs2)

theorem gapR8_of_chk_z {N : ℕ} (h2 : Erdos634.Draft.AllNExclusion.NoF2Chk N) (h3 : NoF3zChk N)
    (h4 : Erdos634.Draft.AllNExclusion.NoF4zChk N) : Chain15.GapR8 N :=
  gapR8_of_arith_z N (Erdos634.Draft.AllNExclusion.noF2_of_chk h2) (noF3z_of_chk h3)
    (Erdos634.Draft.AllNExclusion.noF4z_of_chk h4)

/-! ## The extended all-N condition `C''` -/

open Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2

def LeafR8z (N : ℕ) : Prop := NoF2Chk N ∧ NoF3zChk N ∧ NoF4zChk N

/-- **The condition `C'' N`** = `C' N` with `NoF3Chk` replaced by the weaker `NoF3zChk`. -/
def C'' (N : ℕ) : Prop :=
  LeafSqf N ∧ LeafRange N ∧ LeafEll N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafE' N ∧ LeafF1 N ∧ LeafS2 N ∧
    LeafS3 N ∧ LeafIso N ∧ LeafR8z N

instance (N : ℕ) : Decidable (LeafR8z N) := by unfold LeafR8z; infer_instance
instance (N : ℕ) : Decidable (C'' N) := by unfold C''; infer_instance

theorem C''_of_C' {N : ℕ} (h : C' N) : C'' N := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, ⟨m1, m2, m3⟩⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, m1, noF3zChk_of_noF3Chk m2, m3⟩

/-- **No `N` satisfying `C'' N` is a tile count.**  Proof of `not_tile_of_conditions'` with `gapR8_of_chk_z`. -/
theorem not_tile_of_conditions'' (N : ℕ) (h : C'' N) (D : CongruentDissection N) : False := by
  obtain ⟨hsq, ⟨h7, h17⟩, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, ⟨hF2c, hF3c, hF4c⟩⟩ := h
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk hsq hEll
  refine chain_gen3 N hsq (s1Closed_of_sqfree N hsq hN0)
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_isoQRef N (isoQRef_of_chk hN0 hS3))
    (isoH9b_of_chk hN0 hIso)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq h7 h17 hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq h7 h17) hns)
    ?_ (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree N hsq) ?_ ?_ ?_
    (gapR8_of_chk_z hF2c hF3c hF4c) D
  · rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hE with h4 | ⟨h11, h60, -⟩
    · exact gapE60_of_mod4_two N h4
    · exact gapE60_of_chk' h11 h60
  · rcases hE with h4 | ⟨-, -, h120⟩
    · exact gapE120_of_mod4_two N h4
    · exact gapE120_of_chk hN0 h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chk (by omega) hf

/-! ## Non-vacuity: `NoF3z` is strictly weaker than `NoF3` on the real survivor `N = 105`
(`s = 8, j = 2`: `s^2+3j^2 = 76`, `19` is not a square, tile `(3,2,sqrt 19)`). -/

theorem noF3Chk_105_false : ¬ Erdos634.Draft.AllNExclusion.NoF3Chk 105 :=
  fun h => h 2 (by norm_num) (by norm_num) (by norm_num) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem noF3zChk_105 : NoF3zChk 105 := by decide +kernel
/-- `N = 4830` has a RATIONAL-c F3 survivor (`s=59, j=11`, `s^2+3j^2 = 3844 = 62^2`): `NoF3zChk` fails. -/
theorem noF3zChk_4830_false : ¬ NoF3zChk 4830 := fun h =>
  h 11 (by norm_num) (by norm_num) (by norm_num) 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨by norm_num, by decide +kernel⟩

theorem noF3Chk_210_false : ¬ Erdos634.Draft.AllNExclusion.NoF3Chk 210 :=
  fun h => h 3 (by norm_num) (by norm_num) (by norm_num) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Witness for `C''`**: `N = 210` (squarefree, irrational-c F3 survivor `s=11, j=3`, `s^2+3j^2=148`, `37` non-square;
the only failing leaf of `C'` is `NoF3Chk`) satisfies `C''` but not `C'`. -/
theorem C''_210 : C'' 210 := by decide +kernel
theorem C''_273 : C'' 273 := by decide +kernel
theorem not_C'_210 : ¬ C' 210 := fun h => by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨-, m2, -⟩⟩ := h
  exact noF3Chk_210_false m2
/-- Hence `not_tile_of_conditions''` is not a corollary of `not_tile_of_conditions'` at `N = 210`. -/
theorem witness_210 : C'' 210 ∧ ¬ C' 210 := ⟨C''_210, not_C'_210⟩

end Erdos634.Draft.R8ZF

#print axioms Erdos634.Draft.R8ZF.F3.f3_prime_contradiction
#print axioms Erdos634.Draft.R8ZF.F3Prime.f3prime_contradiction
#print axioms Erdos634.Draft.R8ZF.gapR8_of_arith_z
#print axioms Erdos634.Draft.R8ZF.not_tile_of_conditions''
#print axioms Erdos634.Draft.R8ZF.noF3zChk_105
#print axioms Erdos634.Draft.R8ZF.noF3zChk_4830_false
#print axioms Erdos634.Draft.R8ZF.witness_210
#print axioms Erdos634.Draft.R8ZF.C''_273
