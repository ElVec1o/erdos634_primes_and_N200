import Mathlib
import Erdos634.Draft.G1NInt
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row8F3
import Erdos634.Draft.FluxE2Pi3Row8F4
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.R8F3AreaFormula
import Erdos634.Draft.R8F4AreaFormula
import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.R8F2to4Bridge
import Erdos634.Draft.F1Bridge

/-!
# Rationality of the tile for the F3, F3', F4, F4' targets, no primality

Bodies are `R8F3Contradiction.f3_prime_contradiction` and
`R8F4Contradiction.f4_prime_contradiction` with primality removed (the parities of `M_alpha, M_beta` come from
`Paper.cor_int`, `M == N mod 2`, so evenness of `M_beta +- M_alpha` needs no oddness of `N`):
* F3 (`s = nu(2a+b)`, `z = nu c` integers): the integer `k = m - 2s` of the old core satisfies `k^2 = 9 nu^2 b^2`, so `nu b = |k|/3` is
  rational (old core used primality only AFTER this point, to get `3 | N`).
* F4 (`xa = nu a`, `xc = nu c` integers): `y = (N - xa^2 - xc^2)/(2 xa) = nu b` is rational (old core used primality only for the final factorization).
F3' and F4' are the mirrors under `alpha <-> beta` (swap `a <-> b`).
-/

open scoped Classical

namespace Erdos634.Draft.G1NF34

open Erdos634.Geometry Erdos634.Row8Arith Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.R8F3AreaFormula (F3_area_formula)
open Erdos634.Draft.R8F4AreaFormula (F4_area_formula)

/-- Scaled rational coordinates give rational ratios. -/
theorem rat_of_scaled {a b c ν : ℝ} (hν : 0 < ν) (hb : 0 < b) (u v w : ℚ)
    (hu : (u : ℝ) = ν * a) (hv : (v : ℝ) = ν * b) (hw : (w : ℝ) = ν * c) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  have hvne : (v : ℝ) ≠ 0 := by rw [hv]; exact (mul_pos hν hb).ne'
  refine ⟨u / v, w / v, ?_, ?_⟩
  · push_cast; rw [hu, hv]; field_simp
  · push_cast; rw [hw, hv]; field_simp

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

private lemma f3_rat_core
    {N : ℕ}
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (a + 2 * b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (2 * a + b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
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
  -- k = ±3 ν b
  have hk_R : (k : ℝ) ^ 2 = (3 * (ν * b)) ^ 2 := by
    have h1 : (k : ℝ) ^ 2 = 3 * (4 * (z : ℝ) ^ 2 - (s : ℝ) ^ 2) := by exact_mod_cast hk_sq
    rw [h1, hs_R, hz_R]; linear_combination 12 * ν ^ 2 * hc2
  have hk_abs : 3 * (ν * b) = |(k : ℝ)| := by
    have : (|(k : ℝ)|) ^ 2 = (3 * (ν * b)) ^ 2 := by rw [sq_abs]; exact hk_R
    exact ((pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero).mp this).symm
  have hv : ((((|k| : ℤ) : ℚ) / 3 : ℚ) : ℝ) = ν * b := by
    push_cast; linarith [hk_abs]
  have hu : (((((s : ℚ) - ((|k| : ℤ) : ℚ) / 3) / 2 : ℚ)) : ℝ) = ν * a := by
    push_cast; linarith [hs_R, hk_abs]
  have hw : (((z : ℚ)) : ℝ) = ν * c := by push_cast; exact hz_R
  exact rat_of_scaled hν hb _ _ _ hu hv hw

private lemma f4_rat_core
    {N : ℕ}
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = (ν * a + ν * b) * (2 * (ν * a) + ν * b))
    (xa : ℤ) (hxa_pos : 0 < xa) (hxa_R : (xa : ℝ) = ν * a)
    (xc : ℤ) (hxc_R : (xc : ℝ) = ν * c) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  -- Step 1: N - xa² - xc² = 2*xa*(ν*b)  (using c² = a²+ab+b²)
  have hNid : (N : ℝ) - (xa : ℝ) ^ 2 - (xc : ℝ) ^ 2 = 2 * (xa : ℝ) * (ν * b) := by
    have hc2' : (ν * c) ^ 2 = (ν * a) ^ 2 + (ν * a) * (ν * b) + (ν * b) ^ 2 := by
      have h1 : (ν * c) ^ 2 = ν ^ 2 * c ^ 2 := by ring
      have h2 : (ν * a) ^ 2 = ν ^ 2 * a ^ 2 := by ring
      have h3 : (ν * b) ^ 2 = ν ^ 2 * b ^ 2 := by ring
      nlinarith [sq_nonneg ν, hc2]
    rw [hNreal, hxa_R, hxc_R]
    nlinarith [hc2']
  -- Step 2: define y_q ∈ ℚ = (N - xa² - xc²) / (2*xa)
  have hxa_ne_q : (xa : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (Int.ne_of_gt hxa_pos)
  set y_q : ℚ := ((N : ℚ) - (xa : ℚ) ^ 2 - (xc : ℚ) ^ 2) / (2 * (xa : ℚ))
  -- Step 3: (y_q : ℝ) = ν * b
  have hy_R : (y_q : ℝ) = ν * b := by
    have h2xa_ne_q : (2 : ℚ) * xa ≠ 0 := mul_ne_zero two_ne_zero hxa_ne_q
    have h2xa_ne : (2 : ℝ) * (xa : ℝ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr (Int.ne_of_gt hxa_pos))
    -- In ℚ: y_q * (2 * xa) = N - xa² - xc² (by definition of y_q)
    have hq_mul : y_q * (2 * (xa : ℚ)) = (N : ℚ) - xa ^ 2 - xc ^ 2 :=
      div_mul_cancel₀ _ h2xa_ne_q
    -- Cast to ℝ
    have hR_eq : (y_q : ℝ) * (2 * (xa : ℝ)) = (N : ℝ) - (xa : ℝ) ^ 2 - (xc : ℝ) ^ 2 := by
      exact_mod_cast hq_mul
    exact mul_right_cancel₀ h2xa_ne (by linarith [hNid])
  -- Step 4: y_q > 0
  have hy_pos : 0 < y_q := by
    have : (0 : ℝ) < (y_q : ℝ) := by rw [hy_R]; exact mul_pos hν hb
    exact_mod_cast this
  -- Step 5: xa.toNat > 0
  have hxa_nat_pos : 0 < xa.toNat := by
    have h : 0 < (xa.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hxa_pos.le]; exact hxa_pos
    exact_mod_cast h
  -- Step 6: (xa.toNat : ℝ) = ν * a
  have hxa_nat_R : (xa.toNat : ℝ) = ν * a := by
    have h : (xa.toNat : ℤ) = xa := Int.toNat_of_nonneg hxa_pos.le
    have : (xa.toNat : ℝ) = (xa : ℝ) := by exact_mod_cast h
    rw [this, hxa_R]
  -- Step 7: (N : ℚ) = (xa.toNat + y_q) * (2 * xa.toNat + y_q)
  have hNq : (N : ℚ) = ((xa.toNat : ℚ) + y_q) * (2 * (xa.toNat : ℚ) + y_q) := by
    have hNR : (N : ℝ) = ((xa.toNat : ℝ) + (y_q : ℝ)) * (2 * (xa.toNat : ℝ) + (y_q : ℝ)) := by
      rw [hxa_nat_R, hy_R]; linarith [hNreal]
    exact_mod_cast show ((N : ℚ) : ℝ) =
        (((xa.toNat : ℚ) + y_q) * (2 * (xa.toNat : ℚ) + y_q) : ℚ) by push_cast; linarith [hNR]
  have hxa_Q : ((xa : ℚ) : ℝ) = ν * a := by push_cast; exact hxa_R
  have hxc_Q : ((xc : ℚ) : ℝ) = ν * c := by push_cast; exact hxc_R
  exact rat_of_scaled hν hb _ _ _ hxa_Q hy_R hxc_Q

/-! ## Mains -/

theorem f3_ratio {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
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
    exact f3_rat_core ha hb hν hc2 hNreal (-p) hs_pos (by exact_mod_cast hs_R)
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
    exact f3_rat_core ha hb hν hc2 hNreal q hs_pos (by exact_mod_cast hs_R)
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
    exact f3_rat_core ha hb hν hc2 hNreal (-q) hs_pos (by exact_mod_cast hs_R)
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
    exact f3_rat_core ha hb hν hc2 hNreal p hs_pos (by exact_mod_cast hs_R)
      q hz_pos (by exact_mod_cast hz_R)


theorem f4_ratio {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F4Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  -- Side positivity
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  -- c² = a²+ab+b²
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  -- c > 0
  have hcpos : 0 < c := hc0
  -- Area formula: N = ν²(a+b)(2a+b) = (νa + νb)(2νa + νb)
  have hNreal : (N : ℝ) = (ν * a + ν * b) * (2 * (ν * a) + ν * b) := by
    have h := F4_area_formula D hm ht ha hb hν; ring_nf at h ⊢; linarith
  -- cor_int: Mα, Mβ ∈ ℤ, parities, flux equations
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  -- Lemma W
  have hW_α := Row8.lemmaW_F4_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F4_beta D.target hα ht
  -- Divisor positivity
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  -- Factor identities
  have hfact_α := F4_factor_alpha hc2  -- (a-c)*(c+a-b) = -b*(2a+b-c)
  have hfact_β := F4_factor_beta hc2   -- (a+c)*(c+b-a) = b*(2a+b+c)
  -- Mα + Mβ and Mβ - Mα are both even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  -- From each sign case, extract Mα = ε₁*ν(c-a) and Mβ = ε₂*ν(a+c), then call f4_core
  -- Helper to extract νa from a sum s where 2*s = ε*(Mβ ± Mα)
  -- We handle all 4 sign combos.
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα*(c+a-b) = ν*b*(2a+b-c), Mβ*(c+b-a) = ν*b*(2a+b+c)
    -- → Mα = ν(c-a), Mβ = ν(a+c)
    -- → Mβ - Mα = 2νa, Mβ + Mα = 2νc
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * b * (2 * a + b - c) := hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * b * (2 * a + b + c) := hflux_β.symm.trans hβ_pos
    -- Mα = ν(c-a) [from factor: (a-c)(c+a-b) = -b(2a+b-c) → b(2a+b-c) = (c-a)(c+a-b)]
    have hMα_val : (Mα : ℝ) = ν * (c - a) := by
      have : (Mα : ℝ) * (c + a - b) = ν * (c - a) * (c + a - b) := by
        linear_combination hMα_R + ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = ν * (a + c) := by
      have : (Mβ : ℝ) * (c + b - a) = ν * (a + c) * (c + b - a) := by
        linear_combination hMβ_R - ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    -- 2νa = Mβ - Mα (as reals)
    have h2νa : 2 * (ν * a) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    -- 2νc = Mβ + Mα
    have h2νc : 2 * (ν * c) = (Mβ : ℝ) + Mα := by rw [hMα_val, hMβ_val]; ring
    -- Get integer xa = (Mβ - Mα)/2
    obtain ⟨d, hd⟩ := hdiff_even  -- Mβ - Mα = 2*d
    obtain ⟨s, hs⟩ := hsum_even   -- Mα + Mβ = 2*s → Mβ + Mα = 2*s
    have hxa_R : (d : ℝ) = ν * a := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νa]
    have hxc_R : (s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νc]
    have hd_pos : 0 < d := by
      have : (0 : ℝ) < d := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_rat_core ha hb hν hc2 hNreal d hd_pos hxa_R s hxc_R
  · -- (+-): Mα*(c+a-b) = ν*b*(2a+b-c), Mβ*(c+b-a) = -ν*b*(2a+b+c)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * b * (2 * a + b - c) := hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * b * (2 * a + b + c)) := hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c - a) := by
      have : (Mα : ℝ) * (c + a - b) = ν * (c - a) * (c + a - b) := by
        linear_combination hMα_R + ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = -(ν * (a + c)) := by
      have : (Mβ : ℝ) * (c + b - a) = -(ν * (a + c)) * (c + b - a) := by
        linear_combination hMβ_R + ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    -- 2νa = -(Mβ + Mα)
    have h2νa : 2 * (ν * a) = -((Mβ : ℝ) + Mα) := by rw [hMα_val, hMβ_val]; ring
    -- 2νc = Mα - Mβ
    have h2νc : 2 * (ν * c) = (Mα : ℝ) - Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even   -- Mα + Mβ = 2*s
    obtain ⟨d, hd⟩ := hdiff_even  -- Mβ - Mα = 2*d → Mα - Mβ = 2*(-d)
    -- xa = -s (since 2νa = -(Mβ+Mα) = -(2s) ... wait Mα+Mβ = 2s and Mβ+Mα = 2s)
    have hxa_R : (-s : ℝ) = ν * a := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νa]
    have hxc_R : (-d : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νc]
    have hms_pos : 0 < -s := by
      have : (0 : ℝ) < (-s : ℝ) := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_rat_core ha hb hν hc2 hNreal (-s) hms_pos (by exact_mod_cast hxa_R) (-d)
      (by exact_mod_cast hxc_R)
  · -- (-+): Mα*(c+a-b) = -ν*b*(2a+b-c), Mβ*(c+b-a) = ν*b*(2a+b+c)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * b * (2 * a + b - c)) := hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * b * (2 * a + b + c) := hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c - a)) := by
      have : (Mα : ℝ) * (c + a - b) = -(ν * (c - a)) * (c + a - b) := by
        linear_combination hMα_R - ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = ν * (a + c) := by
      have : (Mβ : ℝ) * (c + b - a) = ν * (a + c) * (c + b - a) := by
        linear_combination hMβ_R - ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    have h2νa : 2 * (ν * a) = (Mβ : ℝ) + Mα := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even
    obtain ⟨d, hd⟩ := hdiff_even
    have hxa_R : (s : ℝ) = ν * a := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νa]
    have hxc_R : (d : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νc]
    have hs_pos : 0 < s := by
      have : (0 : ℝ) < (s : ℝ) := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_rat_core ha hb hν hc2 hNreal s hs_pos (by exact_mod_cast hxa_R) d
      (by exact_mod_cast hxc_R)
  · -- (--): both negative
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * b * (2 * a + b - c)) := hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * b * (2 * a + b + c)) := hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c - a)) := by
      have : (Mα : ℝ) * (c + a - b) = -(ν * (c - a)) * (c + a - b) := by
        linear_combination hMα_R - ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = -(ν * (a + c)) := by
      have : (Mβ : ℝ) * (c + b - a) = -(ν * (a + c)) * (c + b - a) := by
        linear_combination hMβ_R + ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    have h2νa : 2 * (ν * a) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = -((Mβ : ℝ) + Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even
    obtain ⟨d, hd⟩ := hdiff_even
    have hxa_R : (-d : ℝ) = ν * a := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νa]
    have hxc_R : (-s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νc]
    have hmd_pos : 0 < -d := by
      have : (0 : ℝ) < (-d : ℝ) := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_rat_core ha hb hν hc2 hNreal (-d) hmd_pos (by exact_mod_cast hxa_R) (-s)
      (by exact_mod_cast hxc_R)


/-! ## Statements -/

open Erdos634.Draft.G1NInt in
private theorem tile_of_ratio {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ}
    (hm : D.model.TwoPiThreeData α A B C) (h : ∃ q r : ℚ, A = (q : ℝ) * B ∧ C = (r : ℝ) * B) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  obtain ⟨q, r, hq, hr⟩ := h
  obtain ⟨-, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  exact integer_tile_of_ratios ha hb hc (c_sq D.model hm) q r hq hr

theorem integer_tile_F3 {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C)
    (ht : TgtAngles D α (2 * α) (3 * (Real.pi / 3 - α))) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  obtain ⟨-, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨ν, hν, hF⟩ := Erdos634.Draft.R8F2to4Bridge.f3_data_of_shape D hm ht
  exact tile_of_ratio D hm (f3_ratio D hα hm hF ha hb hν)

theorem integer_tile_F4 {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C)
    (ht : TgtAngles D α (2 * (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α))) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  obtain ⟨-, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨ν, hν, hF⟩ := Erdos634.Draft.R8F2to4Bridge.f4_data_of_shape D hm ht
  exact tile_of_ratio D hm (f4_ratio D hα hm hF ha hb hν)

private theorem tgt_congr {N : ℕ} {D : CongruentDissection N} {x y z x' y' z' : ℝ}
    (h : TgtAngles D x y z) (hx : x = x') (hy : y = y') (hz : z = z') : TgtAngles D x' y' z' := by
  subst hx; subst hy; subst hz; exact h

private theorem mirror {A B C : ℝ}
    (h : ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ B = K * a ∧ A = K * b ∧ C = K * c) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  obtain ⟨K, a, b, c, hK, ha, hb, hcop, hc, h1, h2, h3⟩ := h
  exact ⟨K, b, a, c, hK, hb, ha, hcop.symm, by rw [hc]; ring, h2, h1, h3⟩

theorem integer_tile_F3' {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C)
    (ht : TgtAngles D (Real.pi / 3 - α) (2 * (Real.pi / 3 - α)) (3 * α)) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  have hα' : IrrPi (Real.pi / 3 - α) := fun ⟨r, hr⟩ => hα ⟨1 / 3 - r, by push_cast at hr ⊢; linarith⟩
  have hm' := Erdos634.Geometry.twoPiThreeData_swap D.model hm
  exact mirror (integer_tile_F3 D hα' hm' (tgt_congr ht rfl rfl (by ring)))

theorem integer_tile_F4' {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C)
    (ht : TgtAngles D (Real.pi / 3 - α) (2 * α) (α + 2 * (Real.pi / 3 - α))) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  have hα' : IrrPi (Real.pi / 3 - α) := fun ⟨r, hr⟩ => hα ⟨1 / 3 - r, by push_cast at hr ⊢; linarith⟩
  have hm' := Erdos634.Geometry.twoPiThreeData_swap D.model hm
  exact mirror (integer_tile_F4 D hα' hm' (tgt_congr ht rfl (by ring) (by ring)))

end Erdos634.Draft.G1NF34

#print axioms Erdos634.Draft.G1NF34.f3_ratio
#print axioms Erdos634.Draft.G1NF34.f4_ratio
#print axioms Erdos634.Draft.G1NF34.integer_tile_F3
#print axioms Erdos634.Draft.G1NF34.integer_tile_F4
#print axioms Erdos634.Draft.G1NF34.integer_tile_F3'
#print axioms Erdos634.Draft.G1NF34.integer_tile_F4'
