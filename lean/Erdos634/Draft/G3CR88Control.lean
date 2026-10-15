-- No sorry, no native_decide, no axioms.
-- Control for `R8ReductionStatement` (F2-F4' targets with a 2pi/3 tile): the certified 88-tiling
-- `R88TilingBridge.dissection` (target (21,55,56)*98, tile (3,5,7)*98) satisfies every non-arithmetic
-- premise: IrrPi alpha, TwoPiThreeData, and the target is F4 = (alpha, 2beta, 2alpha+beta).
-- So the prime-free variant is refuted at N = 88 = (a+b)(2a+b) (k = 1), the composite N0.
import Erdos634.R88TilingBridge
import Erdos634.Draft.FluxPaperWitness
import Erdos634.Draft.FluxWitness
import Erdos634.Draft.TheoremPConditional

open scoped Classical

namespace Erdos634.Draft.G3CR88Control

open Erdos634.Geometry Erdos634.Z3Real Erdos634.TilePlacement
open Erdos634.Draft.FluxPaperWitness (cos_cornerAngle' cornerAngle_mem' ne_of_dist')
open Erdos634.Draft.TheoremPConditional
open Erdos634.R88TilingBridge (pieceTri headI_mem_tiles vertexOf targetTri toZPt dist2_eq_zdist2)

noncomputable abbrev D := Erdos634.R88TilingBridge.dissection

theorem d_model : D.model = pieceTri headI_mem_tiles := rfl
theorem d_target : D.target = targetTri := rfl

theorem m_d01 : dist (D.model.pts 0) (D.model.pts 1) = 686 := by
  have e : R88Tiling.dist2 (vertexOf R88Tiling.tiles.headI 0) (vertexOf R88Tiling.tiles.headI 1)
      = ((470596:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.R88TilingBridge.pieceTri_dist_sq _ _ 0 1, e]; simp [toR]; norm_num)

theorem m_d12 : dist (D.model.pts 1) (D.model.pts 2) = 294 := by
  have e : R88Tiling.dist2 (vertexOf R88Tiling.tiles.headI 1) (vertexOf R88Tiling.tiles.headI 2)
      = ((86436:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.R88TilingBridge.pieceTri_dist_sq _ _ 1 2, e]; simp [toR]; norm_num)

theorem m_d20 : dist (D.model.pts 2) (D.model.pts 0) = 490 := by
  have e : R88Tiling.dist2 (vertexOf R88Tiling.tiles.headI 2) (vertexOf R88Tiling.tiles.headI 0)
      = ((240100:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.R88TilingBridge.pieceTri_dist_sq _ _ 2 0, e]; simp [toR]; norm_num)

theorem t_d01 : dist (D.target.pts 0) (D.target.pts 1) = 2058 := by
  have h := Erdos634.R88TilingBridge.targetTri_sides.1
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [d_target, h]; norm_num)

theorem t_d12 : dist (D.target.pts 1) (D.target.pts 2) = 5488 := by
  have h := Erdos634.R88TilingBridge.targetTri_sides.2.1
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [d_target, h]; norm_num)

theorem t_d20 : dist (D.target.pts 2) (D.target.pts 0) = 5390 := by
  have h := Erdos634.R88TilingBridge.targetTri_sides.2.2
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [d_target, h]; norm_num)

theorem t_d10 : dist (D.target.pts 1) (D.target.pts 0) = 2058 := by rw [dist_comm]; exact t_d01
theorem t_d21 : dist (D.target.pts 2) (D.target.pts 1) = 5488 := by rw [dist_comm]; exact t_d12
theorem t_d02 : dist (D.target.pts 0) (D.target.pts 2) = 5390 := by rw [dist_comm]; exact t_d20

/-- alpha := the model's angle at vertex 0 (opposite the side 294 = 98*3). -/
noncomputable def α : ℝ := D.model.angleAt 0

theorem cos_α : Real.cos α = 13 / 14 := by
  unfold α Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
  rw [cos_cornerAngle' (ne_of_dist' m_d01 (by norm_num)).symm (ne_of_dist' m_d20 (by norm_num)),
    dist_comm (D.model.pts 1) (D.model.pts 0), m_d01, m_d20, m_d12]
  norm_num

theorem α_irr : IrrPi α := by
  intro hr
  have hmem := niven hr ⟨13 / 14, by rw [cos_α]; norm_num⟩
  rw [cos_α] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h <;> norm_num at h

theorem model_angle2 : D.model.angleAt 2 = 2 * Real.pi / 3 := by
  have hcos : Real.cos (D.model.angleAt 2) = -1 / 2 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle' (ne_of_dist' m_d20 (by norm_num)).symm (ne_of_dist' m_d12 (by norm_num)),
      dist_comm (D.model.pts 0) (D.model.pts 2), m_d20, m_d12, m_d01]
    norm_num
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  have hpi := Real.pi_pos
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩ (hcos.trans hc.symm)

theorem model_angle1 : D.model.angleAt 1 = Real.pi / 3 - α := by
  have h := D.model.angleAt_sum
  rw [model_angle2] at h
  unfold α
  linarith

theorem model_opp : D.model.oppLen 0 = 294 ∧ D.model.oppLen 1 = 490 ∧ D.model.oppLen 2 = 686 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨m_d12, m_d20, m_d01⟩

theorem data88 : D.model.TwoPiThreeData α 294 490 686 :=
  ⟨Equiv.refl _, rfl, model_opp.1, model_angle1, model_opp.2.1, model_angle2, model_opp.2.2⟩

theorem sin_α : Real.sin α = 3 * Real.sqrt 3 / 14 := by
  have hα : 0 ≤ α ∧ α ≤ Real.pi := cornerAngle_mem' _ _ _
  have h0 : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα.1 hα.2
  have hs : Real.sin α ^ 2 = (3 * Real.sqrt 3 / 14) ^ 2 := by
    have := Real.sin_sq_add_cos_sq α
    rw [cos_α] at this
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [h3]
  have hp : 0 ≤ 3 * Real.sqrt 3 / 14 := by positivity
  exact (pow_left_inj₀ h0 hp two_ne_zero).mp hs

theorem target_angle2 : D.target.angleAt 2 = α := by
  have hcos : Real.cos (D.target.angleAt 2) = 13 / 14 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle' (ne_of_dist' t_d02 (by norm_num)) (ne_of_dist' t_d12 (by norm_num))]
    simp only [t_d02, t_d12, t_d01]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) (cornerAngle_mem' _ _ _) (hcos.trans cos_α.symm)

theorem target_angle0 : D.target.angleAt 0 = Real.pi / 3 + α := by
  have hcos : Real.cos (D.target.angleAt 0) = 1 / 7 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle' (ne_of_dist' t_d10 (by norm_num)) (ne_of_dist' t_d20 (by norm_num))]
    simp only [t_d10, t_d20, t_d12]
    norm_num
  have hc : Real.cos (Real.pi / 3 + α) = 1 / 7 := by
    rw [Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three, cos_α, sin_α]
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [h3]
  have hα : 0 ≤ α ∧ α ≤ Real.pi := cornerAngle_mem' _ _ _
  have hle : α ≤ Real.pi / 2 := by
    by_contra hh
    rw [not_le] at hh
    have := Real.cos_neg_of_pi_div_two_lt_of_lt hh (by linarith [hα.2, Real.pi_pos])
    rw [cos_α] at this; norm_num at this
  have hpi := Real.pi_pos
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by linarith [hα.1], by linarith⟩ (hcos.trans hc.symm)

theorem target_angle1 : D.target.angleAt 1 = 2 * (Real.pi / 3 - α) := by
  have h := D.target.angleAt_sum
  rw [target_angle0, target_angle2] at h
  linarith

/-- **F4 shape**: the target of the real 88-tiling is `(α, 2β, 2α+β)`, `β = π/3 − α`. -/
theorem f4_shape : F2to4Shape D α := by
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
  refine ⟨Equiv.swap 0 2, ?_, ?_, ?_⟩
  · rw [Equiv.swap_apply_left]; exact target_angle2
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact target_angle1
  · rw [Equiv.swap_apply_right]; rw [target_angle0]; ring

/-- **C9 control**: every non-arithmetic premise of `R8ReductionStatement` holds on the real 88-tiling. -/
theorem r8_premises_88 :
    IrrPi α ∧ D.model.TwoPiThreeData α 294 490 686 ∧ F2to4Shape D α :=
  ⟨α_irr, data88, f4_shape⟩

/-- The prime-free variant of C9 (binders `N.Prime`, `N % 4 = 3`, `3 < N` dropped) is REFUTED by the
certified 88-tiling: C9 rests on primality (here N = 88 = N0 composite, k = 1). -/
theorem r8_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), IrrPi α →
        D.model.TwoPiThreeData α a b c → F2to4Shape D α → False) := by
  intro h
  exact h _ D α 294 490 686 α_irr data88 f4_shape

end Erdos634.Draft.G3CR88Control

#print axioms Erdos634.Draft.G3CR88Control.r8_primeFree_refuted
