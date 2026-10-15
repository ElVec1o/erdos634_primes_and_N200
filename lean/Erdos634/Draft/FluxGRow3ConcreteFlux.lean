-- Draft/FluxGRow3ConcreteFlux.lean — the target-side flux computation on the concrete target
-- `target = mkTri (-3) 0 3 0 0 sq7 _`, at the angle `α456` (`cos α456 = 3/4`) and `lam := 4`.
-- Imported directly by All.lean.
--
-- Main statement: `target_flux_gauss`. For every `X : ℤ`,
--   `target.flux (gaussWeight α456 θ₀ X)
--      = I^j * ( (if k = X then 2*4*cos α456 else 0) - (if k-1=X then 4 else 0)
--                 - (if k+1=X then 4 else 0) )`,
-- where `k := gridK α456 θ₀ (target.leftUnit 0).angle` and `j := gridJ α456 θ₀ (target.leftUnit 0).angle`
-- (concretely `k = j = 0`, since `θ₀ = (target.leftUnit 0).angle`). It has no open hypotheses: the
-- irrationality of `α456/π` is `α456_div_pi_irr`, and the grid membership of the three edge directions
-- comes from `FluxGRow3SharedGrid`.
--
-- The side lengths of `target` agree with those of `targetIso α456 4` (`target_dist01`, `target_dist12`,
-- `target_dist20`), but the two are different `Tri` terms (`sssTri` places `pts 0 = (0,0)`, `target`
-- places `pts 0 = (-3,0)`), so `targetIso_flux_gauss` cannot be instantiated directly; its proof is
-- redone on the coordinates of `target`, using `gaussWeightA_shift`, `gridK_add_shift`, `gridJ_add_shift`.
--
-- No formal Laurent polynomial or `z`-substitution is introduced. The tile-side flux computation and
-- the assembly on `dissection'` are in `FluxGRow3Step3N2Final`.
--
-- All of `3`, `4`, `√7` here are the side data of the `3-√7-4` right triangle; `(e, f) = (3, 4)` is not
-- a parameter pair.
import Erdos634.Draft.FluxGRow3SharedGrid
import Erdos634.Draft.FluxGRow3AngleWitness

open scoped Classical

namespace Erdos634.Draft.FluxGRow3ConcreteFlux

open Erdos634.Geometry Erdos634.CertCoord Complex
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxRow4Witness
open Erdos634.Geometry.Row3

/-! ## §1 `target`'s three side lengths, matching `targetIso α456 4`'s `(2λcosα, λ, λ)` shape -/

theorem target_dist01 : dist (target.pts 0) (target.pts 1) = 2 * 4 * Real.cos α456 := by
  rw [target_pts]
  have h := dist_sq_mkPt (-3) 0 3 0
  have hc := cos_α456
  have heq : dist (mkPt (-3:ℝ) 0) (mkPt 3 0) ^ 2 = (2 * 4 * Real.cos α456) ^ 2 := by
    rw [h, hc]; norm_num
  have hnn : (0:ℝ) ≤ 2 * 4 * Real.cos α456 := by rw [hc]; norm_num
  exact (pow_left_inj₀ dist_nonneg hnn two_ne_zero).mp heq

theorem target_dist12 : dist (target.pts 1) (target.pts 2) = 4 := by
  rw [target_pts]
  have h := dist_sq_mkPt (3:ℝ) 0 0 sq7
  have h7 := sq7_sq
  have heq : dist (mkPt (3:ℝ) 0) (mkPt 0 sq7) ^ 2 = (4:ℝ) ^ 2 := by
    rw [h]; nlinarith
  exact (pow_left_inj₀ dist_nonneg (by norm_num) two_ne_zero).mp heq

theorem target_dist20 : dist (target.pts 2) (target.pts 0) = 4 := by
  rw [dist_comm]
  rw [target_pts]
  exact tile0_dist_AB

/-! ## §2 The concrete-target flux, per grid degree

Exactly `FluxGRow3Step5.targetIso_flux_gauss`'s proof, replayed on `target`'s own coordinate/angle
facts (`FluxGRow3SharedGrid.lean`) instead of the symbolic `targetIso`'s. `hairr` and `hgridBC` are
both DISCHARGED (not carried as hypotheses): `hairr` by `α456_div_pi_irr`
(`FluxGRow3AngleWitness.lean`), `hgridBC` by `θ₀_isGridA` transported along
`θ₀_coe_eq_target_leftUnit0_angle` (`FluxGRow3SharedGrid.lean`). -/

theorem hgridBC_target : IsGridA α456 θ₀ (target.leftUnit 0).angle :=
  θ₀_coe_eq_target_leftUnit0_angle ▸ θ₀_isGridA

theorem target_flux_gauss (X : ℤ) :
    target.flux (gaussWeight α456 θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α456 θ₀ (target.leftUnit 0).angle) *
        ((if gridK α456 θ₀ (target.leftUnit 0).angle = X
            then (2 * 4 * Real.cos α456 : ℂ) else 0)
          - (if gridK α456 θ₀ (target.leftUnit 0).angle - 1 = X then (4 : ℂ) else 0)
          - (if gridK α456 θ₀ (target.leftUnit 0).angle + 1 = X then (4 : ℂ) else 0)) := by
  have hairr : Irrational (α456 / Real.pi) := α456_div_pi_irr
  have hgridBC : IsGridA α456 θ₀ (target.leftUnit 0).angle := hgridBC_target
  set k := gridK α456 θ₀ (target.leftUnit 0).angle with hk_def
  set j := gridJ α456 θ₀ (target.leftUnit 0).angle with hj_def
  -- The two turn steps, in shift form, from `FluxGRow3SharedGrid`'s absolute angle computations.
  have hturnCA : (target.leftUnit 1).angle
      = (target.leftUnit 0).angle + (((-1:ℤ):ℝ) * α456 + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    rw [target_leftUnit1_angle, target_leftUnit0_angle, ← Real.Angle.coe_add]
    congr 1; push_cast; ring
  have hturnAB : (target.leftUnit 2).angle
      = (target.leftUnit 0).angle + (((1:ℤ):ℝ) * α456 + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    rw [target_leftUnit2_angle, target_leftUnit0_angle, ← Real.Angle.coe_add]
    congr 1; push_cast; ring
  -- The three edge weights, exactly as `targetIso_flux_gauss` reads them off.
  have hgw0 : gaussWeight α456 θ₀ X (target.leftUnit 0) = if k = X then (Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight gaussWeightA
    rw [dif_pos hgridBC]
  have hgw1 : gaussWeight α456 θ₀ X (target.leftUnit 1)
      = if k - 1 = X then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hairr hgridBC (-1) 2 X
    rw [hturnCA, hshift]
    unfold gaussWeightA
    rw [dif_pos hgridBC]
    by_cases hX : k = X - (-1)
    · rw [if_pos hX, if_pos (by omega : k - 1 = X)]
      have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]; simp [Complex.I_sq]
      rw [hI2]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k - 1 = X), mul_zero]
  have hgw2 : gaussWeight α456 θ₀ X (target.leftUnit 2)
      = if k + 1 = X then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hairr hgridBC 1 2 X
    rw [hturnAB, hshift]
    unfold gaussWeightA
    rw [dif_pos hgridBC]
    by_cases hX : k = X - 1
    · rw [if_pos hX, if_pos (by omega : k + 1 = X)]
      have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]; simp [Complex.I_sq]
      rw [hI2]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k + 1 = X), mul_zero]
  -- Unfold `Tri.flux` over the three edges, using `target`'s own side lengths.
  have hflux : target.flux (gaussWeight α456 θ₀ X)
      = (dist (target.pts 0) (target.pts 1) : ℝ) • gaussWeight α456 θ₀ X (target.leftUnit 0)
        + (dist (target.pts 1) (target.pts 2) : ℝ) • gaussWeight α456 θ₀ X (target.leftUnit 1)
        + (dist (target.pts 2) (target.pts 0) : ℝ) • gaussWeight α456 θ₀ X (target.leftUnit 2) := by
    unfold Tri.flux
    rw [Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl]
  rw [hflux, target_dist01, target_dist12, target_dist20, hgw0, hgw1, hgw2,
    Complex.real_smul, Complex.real_smul, Complex.real_smul]
  by_cases h1 : k = X
  · have h2 : ¬ k - 1 = X := by omega
    have h3 : ¬ k + 1 = X := by omega
    simp only [if_pos h1, if_neg h2, if_neg h3]
    push_cast
    ring
  · by_cases h2 : k - 1 = X
    · have h3 : ¬ k + 1 = X := by omega
      simp only [if_neg h1, if_pos h2, if_neg h3]
      push_cast
      ring
    · by_cases h3 : k + 1 = X
      · simp only [if_neg h1, if_neg h2, if_pos h3]
        push_cast
        ring
      · simp only [if_neg h1, if_neg h2, if_neg h3]
        push_cast
        ring

end Erdos634.Draft.FluxGRow3ConcreteFlux

#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_dist01
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_dist12
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_dist20
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.hgridBC_target
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_flux_gauss
