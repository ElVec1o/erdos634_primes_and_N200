import Mathlib
import Erdos634.Draft.G1NInt
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row8F2
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.FluxDSideWord
import Erdos634.Draft.R8F2to4Bridge

/-!
# Rationality of the tile for the F2 target, no primality

The body is `R8F2Contradiction.f2_prime_contradiction` with every use of
primality removed: the parities of `M_alpha, M_beta` come from `Paper.cor_int` (`M == N mod 2`), the side-word step
`f2_w_rational` is copied verbatim (it never used primality), and the `delta = 0` branch (`a = b`, forcing alpha = pi/6) is
closed by `IrrPi alpha`.  Result: `f2_ratio` (a/b, c/b rational) and `integer_tile_F2`.
-/

open scoped Classical

namespace Erdos634.Draft.G1NF2

open Erdos634.Geometry Erdos634.Row8Arith Erdos634.Draft.TheoremPConditional

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- Factor identities
private lemma F2_factor_alpha {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (a - b - c) * (c + a - b) = -(3 * ν * a * b) := by linear_combination -ν * hc2

private lemma F2_factor_beta {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    -(ν * (a - b + c)) * (c + b - a) = -(3 * ν * a * b) := by linear_combination -ν * hc2

-- Flux value rewritten as -(3νab) — pure arithmetic
private lemma flux_eq_neg3ab {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b)) = -(3 * ν * a * b) := by
  linear_combination ν * hc2

-- When δ = ν(a−b) ≠ 0, the side-word walk on the target forces ν(a+b) ∈ ℚ.
-- δ < 0: use walk on target.oppLen(τ 0) = ν·a·(a+2b);  coefficient na+nb−δ > 0.
-- δ > 0: use walk on target.oppLen(τ 1) = ν·b·(2a+b);  coefficient na+nb+δ > 0.
-- Key algebraic identity (verified by ring): from na·u+nb·v+nc·z = u·(u+2v) (or v·(2u+v))
-- and u²+uv+v² = z², one derives (na+nb∓δ)·w = integer, giving w ∈ ℚ.
private lemma f2_w_rational {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ0 : δ ≠ 0)
    {z : ℤ} (hz : (z : ℝ) = ν * c) :
    ∃ w_q : ℚ, (w_q : ℝ) = ν * (a + b) := by
  obtain ⟨σ_m, -, hm_a, -, hm_b, -, hm_c⟩ := hm
  obtain ⟨-, hgrid⟩ := ht
  obtain ⟨τ, -, ht0, -, ht1, -, -⟩ := hgrid
  -- (νa)²+(νa)(νb)+(νb)² = (νc)² = z²
  have hc2_nuv : (ν * a) ^ 2 + (ν * a) * (ν * b) + (ν * b) ^ 2 = (z : ℝ) ^ 2 := by
    rw [hz]; linear_combination -ν ^ 2 * hc2
  -- δ = νa − νb
  have hδ_uv : (δ : ℝ) = ν * a - ν * b := by linarith [hδ]
  rcases lt_or_gt_of_ne (show (δ : ℝ) ≠ 0 by exact_mod_cast hδ0) with hδ_neg | hδ_pos
  · -- δ < 0: walk on target.oppLen(τ 0) = ν·a·(a+2b)
    obtain ⟨na, nb, nc, hwalk⟩ := D.side_word σ_m hm_a hm_b hm_c (τ 0)
    have hwalkR : (na : ℝ) * a + nb * b + nc * c = ν * (a * (a + 2 * b)) :=
      hwalk.symm.trans ht0
    -- Multiply by ν: na·(νa) + nb·(νb) + nc·(νc) = (νa)·((νa)+2(νb))
    have h5 : (na : ℝ) * (ν * a) + nb * (ν * b) + nc * (z : ℝ) =
        (ν * a) * (ν * a + 2 * (ν * b)) := by
      rw [hz]; linear_combination ν * hwalkR
    -- (na+nb−δ)·w = 2z²−δ²−(na−nb)·δ−2nc·z
    have hW_eq : ((na : ℝ) + nb - (δ : ℝ)) * (ν * (a + b)) =
        2 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 - ((na : ℝ) - nb) * (δ : ℝ) - 2 * nc * (z : ℝ) := by
      rw [show ν * (a + b) = ν * a + ν * b from by ring, hδ_uv]
      linear_combination 2 * h5 + 2 * hc2_nuv
    have hδ_neg_int : δ < 0 := by exact_mod_cast hδ_neg
    have hden_pos : (0 : ℤ) < (na : ℤ) + nb - δ := by
      have h1 : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
      have h2 : (0 : ℤ) ≤ (nb : ℤ) := Int.natCast_nonneg nb
      omega
    set num_z : ℤ := 2 * z ^ 2 - δ ^ 2 - ((na : ℤ) - nb) * δ - 2 * nc * z
    set den_z : ℤ := (na : ℤ) + nb - δ
    refine ⟨(num_z : ℚ) / (den_z : ℚ), ?_⟩
    have hden_ne_r : (den_z : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hW' : (den_z : ℝ) * (ν * (a + b)) = (num_z : ℝ) := by
      simp only [den_z, num_z]; push_cast; linarith [hW_eq]
    simp only [Rat.cast_div, Rat.cast_intCast]
    rw [div_eq_iff hden_ne_r]; linear_combination -hW'
  · -- δ > 0: walk on target.oppLen(τ 1) = ν·b·(2a+b)
    obtain ⟨na, nb, nc, hwalk⟩ := D.side_word σ_m hm_a hm_b hm_c (τ 1)
    have hwalkR : (na : ℝ) * a + nb * b + nc * c = ν * (b * (2 * a + b)) :=
      hwalk.symm.trans ht1
    have h5 : (na : ℝ) * (ν * a) + nb * (ν * b) + nc * (z : ℝ) =
        (ν * b) * (2 * (ν * a) + (ν * b)) := by
      rw [hz]; linear_combination ν * hwalkR
    -- (na+nb+δ)·w = 2z²−δ²+(na−nb)·δ−2nc·z
    have hW_eq : ((na : ℝ) + nb + (δ : ℝ)) * (ν * (a + b)) =
        2 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 - ((na : ℝ) - nb) * (δ : ℝ) - 2 * nc * (z : ℝ) := by
      rw [show ν * (a + b) = ν * a + ν * b from by ring, hδ_uv]
      linear_combination 2 * h5 + 2 * hc2_nuv
    have hδ_pos_int : (0 : ℤ) < δ := by exact_mod_cast hδ_pos
    have hden_pos : (0 : ℤ) < (na : ℤ) + nb + δ := by
      have h1 : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
      have h2 : (0 : ℤ) ≤ (nb : ℤ) := Int.natCast_nonneg nb
      omega
    set num_z : ℤ := 2 * z ^ 2 - δ ^ 2 - ((na : ℤ) - nb) * δ - 2 * nc * z
    set den_z : ℤ := (na : ℤ) + nb + δ
    refine ⟨(num_z : ℚ) / (den_z : ℚ), ?_⟩
    have hden_ne_r : (den_z : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hW' : (den_z : ℝ) * (ν * (a + b)) = (num_z : ℝ) := by
      simp only [den_z, num_z]; push_cast; linarith [hW_eq]
    simp only [Rat.cast_div, Rat.cast_intCast]
    rw [div_eq_iff hden_ne_r]; linear_combination -hW'


/-- `a = b` is impossible for an irrational-angle `2pi/3` tile (it forces `alpha = pi/6`). -/
private lemma no_a_eq_b {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) (hab : a = b) : False := by
  obtain ⟨hcos, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  subst hab
  have h3 : c = Real.sqrt 3 * a := by
    have hs : (Real.sqrt 3 * a) ^ 2 = c ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; nlinarith [hc2]
    have : 0 ≤ Real.sqrt 3 * a := by positivity
    exact (pow_left_inj₀ hc.le this two_ne_zero).mp hs.symm
  have hcos' : Real.cos α = Real.cos (Real.pi / 6) := by
    rw [hcos, Real.cos_pi_div_six, h3]
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsp : 0 < Real.sqrt 3 := by positivity
    field_simp
    nlinarith [hs3]
  have hα0 : 0 ≤ α ∧ α ≤ Real.pi := by
    obtain ⟨σm, h0, -⟩ := hm
    have p1 : 0 < D.model.angleAt (σm 0) := Erdos634.MarchFlank.cornerAngle_pos D.model (σm 0)
    have p2 : D.model.angleAt (σm 0) < Real.pi :=
      Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model (σm 0)
    rw [h0] at p1 p2
    exact ⟨p1.le, p2.le⟩
  have h6 : (Real.pi / 6) ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have := Real.injOn_cos ⟨hα0.1, hα0.2⟩ h6 hcos'
  exact hα ⟨1 / 6, by push_cast; linarith⟩

private lemma f2_rat_core {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν) (hα : IrrPi α)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (δ : ℤ) (hδ : (δ : ℝ) = ν * (a - b))
    (z : ℤ) (hz : (z : ℝ) = ν * c) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0] at hδ
    have : ν * (a - b) = 0 := by rw [← hδ]; simp
    have hab : a = b := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hν.ne'
      · linarith
    exact no_a_eq_b D hα hm hab
  obtain ⟨w, hw⟩ := f2_w_rational D hm ht ha hb hν hc2 hδ hδ0 hz
  have hv : (((w - δ) / 2 : ℚ) : ℝ) = ν * b := by
    push_cast; rw [hw, hδ]; ring
  have hu : (((w + δ) / 2 : ℚ) : ℝ) = ν * a := by
    push_cast; rw [hw, hδ]; ring
  have hvne : (((w - δ) / 2 : ℚ) : ℝ) ≠ 0 := by rw [hv]; exact (mul_pos hν hb).ne'
  refine ⟨((w + δ) / 2) / ((w - δ) / 2), (z : ℚ) / ((w - δ) / 2), ?_, ?_⟩
  · push_cast at hvne hu hv ⊢
    rw [hu, hv]; field_simp
  · push_cast at hvne hz hv ⊢
    rw [hv, hz]; field_simp

theorem f2_ratio {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  have hW_α := Row8.lemmaW_F2_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F2_beta D.target hα ht
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hc0
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hc0
  -- Abbreviate the common flux scalar
  set V : ℝ := ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b))
  have hV : V = -(3 * ν * a * b) := flux_eq_neg3ab hc2
  have hfact_α : ν * (a - b - c) * (c + a - b) = V := by rw [hV]; exact F2_factor_alpha hc2
  have hfact_β : -(ν * (a - b + c)) * (c + b - a) = V := by rw [hV]; exact F2_factor_beta hc2
  -- Mα+Mβ and Mα-Mβ are even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mα - Mβ := by omega
  obtain ⟨d, hd⟩ := hdiff_even  -- Mα - Mβ = 2d
  obtain ⟨s, hs⟩ := hsum_even   -- Mα + Mβ = 2s
  -- Dispatch on the 4 sign combinations from lemmaW
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++) Mα = ν(a-b-c), Mβ = -(ν(a-b+c))
    -- flux_α = V, flux_β = V
    have hMα_eq : (Mα : ℝ) * (c + a - b) = ν * (a - b - c) * (c + a - b) := by
      have hV : (Mα : ℝ) * (c + a - b) = V := hflux_α.symm.trans hα_pos
      linarith [hfact_α]
    have hMβ_eq : (Mβ : ℝ) * (c + b - a) = -(ν * (a - b + c)) * (c + b - a) := by
      have hV : (Mβ : ℝ) * (c + b - a) = V := hflux_β.symm.trans hβ_pos
      linarith [hfact_β]
    have hMα_val : (Mα : ℝ) = ν * (a - b - c) := mul_right_cancel₀ hdiv_α.ne' hMα_eq
    have hMβ_val : (Mβ : ℝ) = -(ν * (a - b + c)) := mul_right_cancel₀ hdiv_β.ne' hMβ_eq
    -- Mα - Mβ = 2ν(a-b), Mα + Mβ = -2νc
    have h2d : (d : ℝ) = ν * (a - b) := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; linarith
    have h2s : (-s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    exact f2_rat_core D hm ht hα ha hb hν hc2 d h2d (-s) (by push_cast; linarith [h2s])
  · -- (+-) Mα = ν(a-b-c), Mβ = ν(a-b+c)
    -- flux_α = V, flux_β = -V
    have hMα_eq : (Mα : ℝ) * (c + a - b) = ν * (a - b - c) * (c + a - b) := by
      have hV : (Mα : ℝ) * (c + a - b) = V := hflux_α.symm.trans hα_pos
      linarith [hfact_α]
    have hMβ_neg_eq : (Mβ : ℝ) * (c + b - a) = ν * (a - b + c) * (c + b - a) := by
      have hMβV : (Mβ : ℝ) * (c + b - a) = -V := hflux_β.symm.trans hβ_neg
      have hfact : ν * (a - b + c) * (c + b - a) = -V := by linarith [hfact_β]
      linarith [hMβV, hfact]
    have hMα_val : (Mα : ℝ) = ν * (a - b - c) := mul_right_cancel₀ hdiv_α.ne' hMα_eq
    have hMβ_val : (Mβ : ℝ) = ν * (a - b + c) := mul_right_cancel₀ hdiv_β.ne' hMβ_neg_eq
    -- Mα - Mβ = -2νc, Mα + Mβ = 2ν(a-b)
    have h2d : (-d : ℝ) = ν * c := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    have h2s : (s : ℝ) = ν * (a - b) := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; linarith
    exact f2_rat_core D hm ht hα ha hb hν hc2 s h2s (-d) (by push_cast; linarith [h2d])
  · -- (-+) Mα = -(ν(a-b-c)), Mβ = -(ν(a-b+c))
    -- flux_α = -V, flux_β = V
    have hMα_neg_eq : (Mα : ℝ) * (c + a - b) = -(ν * (a - b - c)) * (c + a - b) := by
      have hMαV : (Mα : ℝ) * (c + a - b) = -V := hflux_α.symm.trans hα_neg
      have hfact : -(ν * (a - b - c)) * (c + a - b) = -V := by linarith [hfact_α]
      linarith [hMαV, hfact]
    have hMβ_eq : (Mβ : ℝ) * (c + b - a) = -(ν * (a - b + c)) * (c + b - a) := by
      have hV : (Mβ : ℝ) * (c + b - a) = V := hflux_β.symm.trans hβ_pos
      linarith [hfact_β]
    have hMα_val : (Mα : ℝ) = -(ν * (a - b - c)) := mul_right_cancel₀ hdiv_α.ne' hMα_neg_eq
    have hMβ_val : (Mβ : ℝ) = -(ν * (a - b + c)) := mul_right_cancel₀ hdiv_β.ne' hMβ_eq
    -- Mα - Mβ = 2νc, Mα + Mβ = -2ν(a-b)
    have h2d : (d : ℝ) = ν * c := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; linarith
    have h2s : (-s : ℝ) = ν * (a - b) := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    exact f2_rat_core D hm ht hα ha hb hν hc2 (-s) (by push_cast; linarith [h2s]) d h2d
  · -- (--) Mα = -(ν(a-b-c)), Mβ = ν(a-b+c)
    -- flux_α = -V, flux_β = -V
    have hMα_neg_eq : (Mα : ℝ) * (c + a - b) = -(ν * (a - b - c)) * (c + a - b) := by
      have hMαV : (Mα : ℝ) * (c + a - b) = -V := hflux_α.symm.trans hα_neg
      have hfact : -(ν * (a - b - c)) * (c + a - b) = -V := by linarith [hfact_α]
      linarith [hMαV, hfact]
    have hMβ_neg_eq : (Mβ : ℝ) * (c + b - a) = ν * (a - b + c) * (c + b - a) := by
      have hMβV : (Mβ : ℝ) * (c + b - a) = -V := hflux_β.symm.trans hβ_neg
      have hfact : ν * (a - b + c) * (c + b - a) = -V := by linarith [hfact_β]
      linarith [hMβV, hfact]
    have hMα_val : (Mα : ℝ) = -(ν * (a - b - c)) := mul_right_cancel₀ hdiv_α.ne' hMα_neg_eq
    have hMβ_val : (Mβ : ℝ) = ν * (a - b + c) := mul_right_cancel₀ hdiv_β.ne' hMβ_neg_eq
    -- Mα - Mβ = -2ν(a-b), Mα + Mβ = 2νc
    have h2d : (-d : ℝ) = ν * (a - b) := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    have h2s : (s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; linarith
    exact f2_rat_core D hm ht hα ha hb hν hc2 (-d) (by push_cast; linarith [h2d]) s h2s


/-- **Integer tile, F2 target.** -/
theorem integer_tile_F2 {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C)
    (ht : TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α))) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  obtain ⟨-, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨ν, hν, hF2⟩ := Erdos634.Draft.R8F2to4Bridge.f2_data_of_shape D hm ht
  obtain ⟨q, r, hq, hr⟩ := f2_ratio D hα hm hF2 ha hb hν
  exact Erdos634.Draft.G1NInt.integer_tile_of_ratios ha hb hc (c_sq D.model hm) q r hq hr

end Erdos634.Draft.G1NF2

#print axioms Erdos634.Draft.G1NF2.f2_ratio
#print axioms Erdos634.Draft.G1NF2.integer_tile_F2
