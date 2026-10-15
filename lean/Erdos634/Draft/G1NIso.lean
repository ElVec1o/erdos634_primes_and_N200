import Mathlib
import Erdos634.Draft.G1NInt
import Erdos634.Rationality
import Erdos634.Draft.ThmIso
import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.FluxPaperCorIntAnchored
import Erdos634.Draft.FluxE2Pi3Row9
import Erdos634.Draft.FluxERow9Arith

/-!
# Rationality of the tile for the two isosceles targets, without primality

The argument is that of `ISUCore.thmIsoCore` with its arithmetic bridge (`thmIso_arith_bridge`, private,
which finishes with primality) replaced by the rational step it begins with (`Rationality.tile_rational`).
`iso_ratio`: `D` any `CongruentDissection N` (any `N`), tile `TwoPiThreeData alpha a b c`, `IrrPi alpha`, target `IsoTP`
(the two isosceles shapes isoAlpha/isoBeta)  ==>  `a/b, c/b` rational.  `integer_tile_iso` composes with `G1NInt`.
-/

open scoped Classical

namespace Erdos634.Draft.G1NIso

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

private lemma twoPiThreeData_swap {T : Tri} {α a b c : ℝ}
    (h : T.TwoPiThreeData α a b c) :
    T.TwoPiThreeData (Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0, ha, h1, hb, h2, hc⟩ := h
  refine ⟨σ * Equiv.swap 0 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact h1
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact hb
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; rw [h0]; ring
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; exact ha
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact h2
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact hc

private lemma irrPi_beta {α : ℝ} (h : IrrPi α) : IrrPi (Real.pi / 3 - α) :=
  fun ⟨r, hr⟩ => h ⟨1 / 3 - r, by push_cast at hr ⊢; linarith⟩

-- r²=q²+q+1 forces q.den = r.den

private lemma twoPiThree_c_sq' {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha', -, hb', hγ, hc'⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha', hb', hc', hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith


set_option maxHeartbeats 800000 in
private lemma iso_arith_rat
    (N : ℕ)
    (a b c μ : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hμ : 0 < μ)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (harea : (N : ℝ) * b = μ ^ 2 * (a + 2 * b))
    (nA nB : ℤ)
    (hA : (nA : ℝ) = (μ / b) * (c - a - b))
    (hB : (nB : ℝ) = (μ / b) * (c + a + b)) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  have hP_ne : μ / b ≠ 0 := (div_pos hμ hb).ne'
  exact Erdos634.Rationality.tile_rational a b c (μ/b) hc2 hb.ne' hP_ne (by positivity) N nA nB
    (by push_cast; field_simp [hb.ne']; linarith [harea])
    (by push_cast; linarith [hA])
    (by push_cast; linarith [hB])

set_option maxHeartbeats 800000 in
theorem iso_ratio : ∀ (N : ℕ) (D : CongruentDissection N),
    ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → IsoTP D α →
      ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  intro N D α a b c hα hm hisoTP
  obtain ⟨_, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := twoPiThree_c_sq' hm
  obtain ⟨hiso_α, hiso_β⟩ := Row9.iso_closed_forms a b c hc2
  obtain ⟨hcamb_pos, hcbma_pos, Mα, Mβ, hMα_raw, hMβ_raw, -, -, -⟩ :=
    Paper.cor_int_at D hα hm 0
  rw [fAlphaAt_zero] at hMα_raw; rw [fBetaAt_zero] at hMβ_raw
  -- Flux equations from lemmaCF sign cases
  have hA_eq : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fAlpha α hα).weight = μ*(a+2*b-2*c) →
      (Mα : ℝ) = (μ/b)*(c-a-b) := fun μ _ sgn => by
    rw [hMα_raw, sgn]; field_simp [hcamb_pos.ne', hb.ne']; nlinarith [hiso_α]
  have hA_neg : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fAlpha α hα).weight = -(μ*(a+2*b-2*c)) →
      ((-Mα : ℤ) : ℝ) = (μ/b)*(c-a-b) := fun μ _ sgn => by
    push_cast
    have hgoal : -(Mα : ℝ) = μ*(a+2*b-2*c) / (c+a-b) := by rw [hMα_raw, sgn]; ring
    rw [hgoal]; field_simp [hcamb_pos.ne', hb.ne']; nlinarith [hiso_α]
  have hB_eq : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fBeta α hα).weight = μ*(a+2*b+2*c) →
      (Mβ : ℝ) = (μ/b)*(c+a+b) := fun μ _ sgn => by
    rw [hMβ_raw, sgn]; field_simp [hcbma_pos.ne', hb.ne']; nlinarith [hiso_β]
  have hB_neg : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fBeta α hα).weight = -(μ*(a+2*b+2*c)) →
      ((-Mβ : ℤ) : ℝ) = (μ/b)*(c+a+b) := fun μ _ sgn => by
    push_cast
    have hgoal : -(Mβ : ℝ) = μ*(a+2*b+2*c) / (c+b-a) := by rw [hMβ_raw, sgn]; ring
    rw [hgoal]; field_simp [hcbma_pos.ne', hb.ne']; nlinarith [hiso_β]
  rcases hisoTP with htgt | htgt
  -- Branch 1
  · obtain ⟨μ, hμ, hbase⟩ := base_alpha_of_isoTP D hm htgt
    have harea := Erdos634.Draft.ThmIso.base_alpha_area_identity D hm hbase ha hb hμ
    obtain hcf_α | hcf_α := Row9.lemmaCF_alpha D.target hα hbase <;>
    obtain hcf_β | hcf_β := Row9.lemmaCF_beta D.target hα hbase
    · exact iso_arith_rat N a b c μ ha hb hc hμ hc2 harea Mα Mβ
        (hA_eq μ hμ hcf_α) (hB_eq μ hμ hcf_β)
    · exact iso_arith_rat N a b c μ ha hb hc hμ hc2 harea Mα (-Mβ)
        (hA_eq μ hμ hcf_α) (hB_neg μ hμ hcf_β)
    · exact iso_arith_rat N a b c μ ha hb hc hμ hc2 harea (-Mα) Mβ
        (hA_neg μ hμ hcf_α) (hB_eq μ hμ hcf_β)
    · exact iso_arith_rat N a b c μ ha hb hc hμ hc2 harea (-Mα) (-Mβ)
        (hA_neg μ hμ hcf_α) (hB_neg μ hμ hcf_β)
  -- Branch 2
  · have hm' := twoPiThreeData_swap hm
    have hα' := irrPi_beta hα
    have htgt' : TgtAngles D (Real.pi/3-α) (Real.pi/3-α)
        ((Real.pi/3-α) + 3*(Real.pi/3-(Real.pi/3-α))) := by convert htgt using 2; ring
    obtain ⟨μ, hμ, hbase⟩ := base_alpha_of_isoTP D hm' htgt'
    have hc2' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by linarith [hc2, mul_comm a b]
    have harea := Erdos634.Draft.ThmIso.base_alpha_area_identity D hm' hbase hb ha hμ
    obtain ⟨hiso_α', hiso_β'⟩ := Row9.iso_closed_forms b a c hc2'
    obtain ⟨hcamb_pos', hcbma_pos', Mα', Mβ', hMα_raw', hMβ_raw', -, -, -⟩ :=
      Paper.cor_int_at D hα' hm' 0
    rw [fAlphaAt_zero] at hMα_raw'; rw [fBetaAt_zero] at hMβ_raw'
    have hA_eq' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fAlpha (Real.pi/3-α) hα').weight = μ*(b+2*a-2*c) →
        (Mα' : ℝ) = (μ/a)*(c-b-a) := fun μ _ sgn => by
      rw [hMα_raw', sgn]; field_simp [hcamb_pos'.ne', ha.ne']; nlinarith [hiso_α']
    have hA_neg' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fAlpha (Real.pi/3-α) hα').weight = -(μ*(b+2*a-2*c)) →
        ((-Mα' : ℤ) : ℝ) = (μ/a)*(c-b-a) := fun μ _ sgn => by
      push_cast
      have hgoal : -(Mα' : ℝ) = μ*(b+2*a-2*c) / (c+b-a) := by rw [hMα_raw', sgn]; ring
      rw [hgoal]; field_simp [hcamb_pos'.ne', ha.ne']; nlinarith [hiso_α']
    have hB_eq' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fBeta (Real.pi/3-α) hα').weight = μ*(b+2*a+2*c) →
        (Mβ' : ℝ) = (μ/a)*(c+b+a) := fun μ _ sgn => by
      rw [hMβ_raw', sgn]; field_simp [hcbma_pos'.ne', ha.ne']; nlinarith [hiso_β']
    have hB_neg' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fBeta (Real.pi/3-α) hα').weight = -(μ*(b+2*a+2*c)) →
        ((-Mβ' : ℤ) : ℝ) = (μ/a)*(c+b+a) := fun μ _ sgn => by
      push_cast
      have hgoal : -(Mβ' : ℝ) = μ*(b+2*a+2*c) / (c+a-b) := by rw [hMβ_raw', sgn]; ring
      rw [hgoal]; field_simp [hcbma_pos'.ne', ha.ne']; nlinarith [hiso_β']
    have key : ∃ q r : ℚ, b = (q : ℝ) * a ∧ c = (r : ℝ) * a := by
      obtain hcf_α | hcf_α := Row9.lemmaCF_alpha D.target hα' hbase <;>
      obtain hcf_β | hcf_β := Row9.lemmaCF_beta D.target hα' hbase
      · exact iso_arith_rat N b a c μ hb ha hc hμ hc2' harea Mα' Mβ'
          (hA_eq' μ hμ hcf_α) (hB_eq' μ hμ hcf_β)
      · exact iso_arith_rat N b a c μ hb ha hc hμ hc2' harea Mα' (-Mβ')
          (hA_eq' μ hμ hcf_α) (hB_neg' μ hμ hcf_β)
      · exact iso_arith_rat N b a c μ hb ha hc hμ hc2' harea (-Mα') Mβ'
          (hA_neg' μ hμ hcf_α) (hB_eq' μ hμ hcf_β)
      · exact iso_arith_rat N b a c μ hb ha hc hμ hc2' harea (-Mα') (-Mβ')
          (hA_neg' μ hμ hcf_α) (hB_neg' μ hμ hcf_β)
    obtain ⟨q', r', h1, h2⟩ := key
    have hq' : (q' : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact hb.ne' h1
    refine ⟨(q' : ℚ)⁻¹, r' * q'⁻¹, ?_, ?_⟩
    · push_cast; field_simp; linarith
    · push_cast; field_simp; rw [h2, h1]; ring


/-- **Integer tile, isosceles targets.**  `IsoTP D alpha`, tile `(A,B,C)` real: `(A,B,C) = K (a,b,c)`, naturals, primitive. -/
theorem integer_tile_iso {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C) (hiso : IsoTP D α) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  obtain ⟨q, r, hq, hr⟩ := iso_ratio N D α A B C hα hm hiso
  obtain ⟨-, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  exact Erdos634.Draft.G1NInt.integer_tile_of_ratios ha hb hc (twoPiThree_c_sq' hm) q r hq hr

end Erdos634.Draft.G1NIso

#print axioms Erdos634.Draft.G1NIso.iso_ratio
#print axioms Erdos634.Draft.G1NIso.integer_tile_iso
