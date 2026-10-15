-- No sorry, no native_decide, no axioms.
-- Control for `F1FreeStatement`: certified 1944-tiling of the F1' triangle (135,189,216) (angles
-- (beta, alpha+beta, 2alpha+beta)) by the 2pi/3 tile (3,5,7); N = m^2 a(a+b), (a,b,c)=(5,3,7)->(3,5,7)
-- labels, m = 9 (Zhang Prop 9).
import Erdos634.Draft.G3CF1p1944
import Erdos634.Draft.G3CAng

open scoped Classical

namespace Erdos634.Draft.G3CF1pControl

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.G3CF1p1944 (cert cert_ok cert_len)

noncomputable abbrev D := cd cert cert_ok

theorem m_opp0 : D.model.oppLen 0 = 1890 * 5 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (0 + 1)) (vtx cert.model (0 + 2)) 9450 (by decide)
  rw [this]; norm_num
theorem m_opp1 : D.model.oppLen 1 = 1890 * 7 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (1 + 1)) (vtx cert.model (1 + 2)) 13230 (by decide)
  rw [this]; norm_num
theorem m_opp2 : D.model.oppLen 2 = 1890 * 3 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (2 + 1)) (vtx cert.model (2 + 2)) 5670 (by decide)
  rw [this]; norm_num
theorem t_opp0 : D.target.oppLen 0 = 1890 * 216 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (0 + 1)) (vtx cert.target (0 + 2)) 408240 (by decide)
  rw [this]; norm_num
theorem t_opp1 : D.target.oppLen 1 = 1890 * 189 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (1 + 1)) (vtx cert.target (1 + 2)) 357210 (by decide)
  rw [this]; norm_num
theorem t_opp2 : D.target.oppLen 2 = 1890 * 135 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (2 + 1)) (vtx cert.target (2 + 2)) 255150 (by decide)
  rw [this]; norm_num

noncomputable def σm : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 0 2
theorem σm0 : σm 0 = 2 := by decide
theorem σm1 : σm 1 = 0 := by decide
theorem σm2 : σm 2 = 1 := by decide

noncomputable def α : ℝ := D.model.angleAt (σm 0)
noncomputable def β : ℝ := D.model.angleAt (σm 1)

theorem o0 : D.model.oppLen (σm 0) = 1890 * 3 := by rw [σm0]; exact m_opp2
theorem o1 : D.model.oppLen (σm 1) = 1890 * 5 := by rw [σm1]; exact m_opp0
theorem o2 : D.model.oppLen (σm 2) = 1890 * 7 := by rw [σm2]; exact m_opp1

theorem data : D.model.TwoPiThreeData α (1890 * 3) (1890 * 5) (1890 * 7) :=
  tp_data D.model σm 1890 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0 o1 o2

theorem hβ : β = Real.pi / 3 - α :=
  (tp_angles D.model σm 1890 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0 o1 o2).2

theorem cos_α : Real.cos α = 13 / 14 := by
  unfold α
  rw [cos_s0 D.model σm (by rw [o1]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num

theorem cos_β : Real.cos β = 11 / 14 := by
  unfold β
  rw [cos_s1 D.model σm (by rw [o0]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num

theorem α_irr : IrrPi α :=
  irrPi_of_cos α (13 / 14) (by rw [cos_α]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem t_cos1 : Real.cos (D.target.angleAt 1) = 1 / 2 := by
  have := cos_s1 D.target 1 (by simp [t_opp0]) (by simp [t_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, t_opp0, t_opp1, t_opp2]; norm_num

theorem t_angle1 : D.target.angleAt 1 = Real.pi / 3 := by
  have hpi := Real.pi_pos
  exact Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _)
    ⟨by positivity, by linarith⟩ (t_cos1.trans Real.cos_pi_div_three.symm)

theorem t_cos2 : Real.cos (D.target.angleAt 2) = 11 / 14 := by
  have := cos_s2 D.target 1 (by simp [t_opp0]) (by simp [t_opp1])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, t_opp0, t_opp1, t_opp2]; norm_num

theorem f1_shape : F1Shape D α := by
  have h2 : D.target.angleAt 2 = Real.pi / 3 - α := by
    rw [← hβ]; exact angle_eq_of_cos 2 (σm 1) (t_cos2.trans cos_β.symm)
  refine Or.inr ⟨Equiv.swap 0 2, ?_, ?_, ?_⟩
  · rw [Equiv.swap_apply_left]; exact h2
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), t_angle1]; ring
  · rw [Equiv.swap_apply_right]
    have hs := D.target.angleAt_sum
    linarith [t_angle1]

/-- **C8 control (F1' shape)**: every non-arithmetic premise of `F1FreeStatement` holds on the real
1944-tiling. -/
theorem f1_premises :
    IrrPi α ∧ D.model.TwoPiThreeData α (1890 * 3) (1890 * 5) (1890 * 7) ∧ F1Shape D α :=
  ⟨α_irr, data, f1_shape⟩

/-- The prime-free variant of C8 is REFUTED by the real 1944-tiling. -/
theorem f1Free_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), IrrPi α →
        D.model.TwoPiThreeData α a b c → F1Shape D α → False) := by
  intro h
  exact h _ D α _ _ _ α_irr data f1_shape

end Erdos634.Draft.G3CF1pControl

#print axioms Erdos634.Draft.G3CF1pControl.f1Free_primeFree_refuted
