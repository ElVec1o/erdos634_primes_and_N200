-- Draft/FluxGRow3WitnessFinal.lean — instantiation of `FluxGRow3Step1.congruentDissection_row3_lemmaA`
-- on `FluxGRow3WitnessBridge.dissection'`, the reordered `CongruentDissection 2`. All hypotheses
-- (`hα'`, `hβ'`, `hγ'`, the nine disequalities, `hirr`, `hαpos`) are discharged at `α := α456`,
-- `β := π/2 − α456`, `γ := π/2`.
--
-- Geometry: `model' = tile0' = (B, A, M)` with side lengths `BM = 3`, `MA = √7`, `BA = 4`, and
-- `3² + (√7)² = 16 = 4²`, so the right angle is at `M`.
--   `hα'` (`model'_angleAt0`): the angle at `B` is `α456`.
--   `hβ'`: the angle at `A` is `π/2 − α456`: `cos_of_sides` at `(M, A, B)` gives
--     `cos(∠A) = (MA² + BA² − MB²)/(2·MA·BA) = 14/(8√7) = √7/4`, and `sin α456 = √7/4` from
--     `sin²α456 = 1 − 9/16` and `sin α456 > 0`.
--   `hγ'`: the angle at `M` is `π/2`: `cos(∠M) = (BM² + AM² − BA²)/(2·BM·AM) = (9+7−16)/(6√7) = 0`.
--
-- The nine disequalities (`hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0`) and `hirr`/`hαpos` follow from
-- order facts about `α456` (`α456_pos`, `α456_lt_pi_div_two`, `α456_div_pi_irr`, `Real.pi_pos`,
-- `Real.pi_ne_zero`), except `hαβ` (`α456 ≠ π/4`), which uses `cos α456 = 3/4 ≠ √2/2 = cos(π/4)`,
-- proved by squaring.
--
-- Result: `row3_lemmaA_final`, a theorem without hypotheses giving the full case-split conclusion of
-- `congruentDissection_row3_lemmaA` for the concrete `CongruentDissection 2` `dissection'`.
import Erdos634.Draft.FluxGRow3WitnessBridge

namespace Erdos634.Draft.FluxGRow3WitnessFinal

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AreaDet Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection
open Erdos634.Draft.FluxGRow3WitnessBridge

/-! ## §1 `sin α456`, needed for `hβ'` -/

theorem α456_sin : Real.sin Erdos634.Draft.FluxRow4Witness.α456 = sq7 / 4 := by
  have hcos := Erdos634.Draft.FluxRow4Witness.cos_α456
  have hpyth := Real.sin_sq_add_cos_sq Erdos634.Draft.FluxRow4Witness.α456
  have hsinpos : 0 < Real.sin Erdos634.Draft.FluxRow4Witness.α456 :=
    Real.sin_pos_of_pos_of_lt_pi Erdos634.Geometry.Row3.α456_pos
      (by linarith [Erdos634.Geometry.Row3.α456_lt_pi_div_two, Real.pi_pos])
  have h7 := sq7_sq
  have hb7 : (0:ℝ) < sq7 / 4 := by have := sq7_pos; linarith
  have hsq : Real.sin Erdos634.Draft.FluxRow4Witness.α456 ^ 2 = (sq7 / 4) ^ 2 := by
    nlinarith [hpyth, hcos, h7]
  have hfactor : (Real.sin Erdos634.Draft.FluxRow4Witness.α456 - sq7 / 4)
      * (Real.sin Erdos634.Draft.FluxRow4Witness.α456 + sq7 / 4) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · exfalso; linarith [hsinpos, hb7]

/-! ## §2 `hβ'` and `hγ'`, matching `model'_angleAt0`'s technique with permuted arguments -/

/-- **`hγ'` for `dissection'`**: angle at index 2 (`M`) equals `π/2`, the right angle. -/
theorem model'_angleAt2 :
    cornerAngle (model'.pts 0) (model'.pts 2) (model'.pts 1) = Real.pi / 2 := by
  show cornerAngle (mkPt (-3:ℝ) 0) (mkPt 0 0) (mkPt 0 sq7) = Real.pi / 2
  have hs := sq7_pos
  have h7 := sq7_sq
  have hBM : dist (mkPt (-3:ℝ) 0) (mkPt (0:ℝ) 0) = 3 := by
    rw [dist_comm]; exact model'_dMB
  have hAM : dist (mkPt (0:ℝ) sq7) (mkPt (0:ℝ) 0) = sq7 := model'_dAM
  have hBA : dist (mkPt (-3:ℝ) 0) (mkPt (0:ℝ) sq7) = 4 := model'_dBA
  have hcos : Real.cos (cornerAngle (mkPt (-3:ℝ) 0) (mkPt (0:ℝ) 0) (mkPt (0:ℝ) sq7)) = 0 := by
    rw [cos_of_sides (mkPt (-3:ℝ) 0) (mkPt (0:ℝ) 0) (mkPt (0:ℝ) sq7) (by rw [hBM]; norm_num)
      (by rw [hAM]; positivity)]
    rw [hBM, hAM, hBA]
    rw [show ((3:ℝ)^2 + sq7^2 - 4^2) = 0 by rw [h7]; ring]
    norm_num
  have hmem : cornerAngle (mkPt (-3:ℝ) 0) (mkPt (0:ℝ) 0) (mkPt (0:ℝ) sq7) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos] at hres
  rw [← hres, Real.arccos_zero]

/-- **`hβ'` for `dissection'`**: angle at index 1 (`A`) equals `π/2 − α456`. -/
theorem model'_angleAt1 :
    cornerAngle (model'.pts 2) (model'.pts 1) (model'.pts 0)
      = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 := by
  show cornerAngle (mkPt (0:ℝ) 0) (mkPt 0 sq7) (mkPt (-3:ℝ) 0) = Real.pi / 2 -
    Erdos634.Draft.FluxRow4Witness.α456
  have hs := sq7_pos
  have h7 := sq7_sq
  have hMA : dist (mkPt (0:ℝ) 0) (mkPt (0:ℝ) sq7) = sq7 := by
    rw [dist_comm]; exact model'_dAM
  have hBA : dist (mkPt (-3:ℝ) 0) (mkPt (0:ℝ) sq7) = 4 := model'_dBA
  have hMB : dist (mkPt (0:ℝ) 0) (mkPt (-3:ℝ) 0) = 3 := model'_dMB
  have hcos : Real.cos (cornerAngle (mkPt (0:ℝ) 0) (mkPt (0:ℝ) sq7) (mkPt (-3:ℝ) 0))
      = sq7 / 4 := by
    rw [cos_of_sides (mkPt (0:ℝ) 0) (mkPt (0:ℝ) sq7) (mkPt (-3:ℝ) 0) (by rw [hMA]; positivity)
      (by rw [hBA]; norm_num)]
    rw [hMA, hBA, hMB]
    have hb : (2 * sq7 * 4 : ℝ) ≠ 0 := by intro h; nlinarith [hs]
    rw [div_eq_div_iff hb (by norm_num : (4:ℝ) ≠ 0)]
    nlinarith [h7]
  have hmem : cornerAngle (mkPt (0:ℝ) 0) (mkPt (0:ℝ) sq7) (mkPt (-3:ℝ) 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos] at hres
  have hsin := α456_sin
  have htarget : Real.cos (Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456) = sq7 / 4 := by
    rw [Real.cos_pi_div_two_sub, hsin]
  have hmem2 : Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∈ Set.Icc 0 Real.pi :=
    ⟨by linarith [Erdos634.Geometry.Row3.α456_lt_pi_div_two],
     by linarith [Erdos634.Geometry.Row3.α456_pos, Real.pi_pos]⟩
  have hres2 := Real.arccos_cos hmem2.1 hmem2.2
  rw [htarget] at hres2
  rw [← hres, ← hres2]

/-! ## §3 The disequalities and `hαpos`/`hirr`, at `α := α456`, `β := π/2 − α456`, `γ := π/2` -/

theorem α456_ne_pi_div_four : Erdos634.Draft.FluxRow4Witness.α456 ≠ Real.pi / 4 := by
  intro h
  have hc := Erdos634.Draft.FluxRow4Witness.cos_α456
  rw [h, Real.cos_pi_div_four] at hc
  have h2 : Real.sqrt 2 = 3 / 2 := by linarith
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h2] at hsq2
  norm_num at hsq2

theorem hαβ_final : Erdos634.Draft.FluxRow4Witness.α456
    ≠ Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 := by
  intro h
  apply α456_ne_pi_div_four
  linarith

theorem hαγ_final : Erdos634.Draft.FluxRow4Witness.α456 ≠ Real.pi / 2 := by
  linarith [Erdos634.Geometry.Row3.α456_lt_pi_div_two]

theorem hαπ_final : Erdos634.Draft.FluxRow4Witness.α456 ≠ Real.pi := by
  intro h
  linarith [Erdos634.Geometry.Row3.α456_lt_pi_div_two, Real.pi_pos, h]

theorem hα0_final : Erdos634.Draft.FluxRow4Witness.α456 ≠ 0 :=
  ne_of_gt Erdos634.Geometry.Row3.α456_pos

theorem hβγ_final : Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ≠ Real.pi / 2 := by
  intro h
  exact Erdos634.Geometry.Row3.α456_pos.ne' (by linarith)

theorem hβπ_final : Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ≠ Real.pi := by
  intro h
  linarith [Erdos634.Geometry.Row3.α456_pos, Real.pi_pos]

theorem hβ0_final : Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ≠ 0 := by
  intro h
  exact (ne_of_gt Erdos634.Geometry.Row3.α456_lt_pi_div_two) (by linarith)

theorem hγπ_final : (Real.pi / 2 : ℝ) ≠ Real.pi := by
  intro h; linarith [Real.pi_pos]

theorem hγ0_final : (Real.pi / 2 : ℝ) ≠ 0 := by
  intro h; linarith [Real.pi_pos]

theorem hπ0_final : Real.pi ≠ 0 := Real.pi_ne_zero

theorem hαpos_final : (0:ℝ) < Erdos634.Draft.FluxRow4Witness.α456 :=
  Erdos634.Geometry.Row3.α456_pos

theorem hirr_final : Irrational (Erdos634.Draft.FluxRow4Witness.α456 / Real.pi) :=
  Erdos634.Geometry.Row3.α456_div_pi_irr

/-! ## §4 The capstone: full instantiation of `congruentDissection_row3_lemmaA` on `dissection'` -/

/-- **The capstone.** `FluxGRow3Step1.congruentDissection_row3_lemmaA`, fully instantiated on the
real `CongruentDissection 2` `dissection'` (P106/P107), at `α := α456`, `β := π/2 − α456`,
`γ := π/2`, with every one of the theorem's ten hypothesis groups discharged by a concrete witness:
`hα'` = `model'_angleAt0` (P107), `hβ'` = `model'_angleAt1` (§2), `hγ'` = `model'_angleAt2` (§2),
the nine disequalities and `hαpos`/`hirr` all from §3. This is ONE fully unconditional theorem. -/
theorem row3_lemmaA_final :
    ∃ p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℕ,
    (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = 2 * (Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456) ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = 2 * (Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456) ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = 2 * (Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456) ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Real.pi / 2 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Real.pi / 2 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = 2 * Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Real.pi / 2 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Real.pi / 2 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = 2 * Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Real.pi / 2 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Real.pi / 2 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = Erdos634.Draft.FluxRow4Witness.α456) ∨
      (Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p0 q0 r0
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p2 q2 r2
        = Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456 ∧
      Erdos634.Geometry.Row3.cornerAngle Erdos634.Draft.FluxRow4Witness.α456 p1 q1 r1
        = 2 * Erdos634.Draft.FluxRow4Witness.α456) := by
  exact Erdos634.Row3Step1.congruentDissection_row3_lemmaA dissection'
    Erdos634.Draft.FluxRow4Witness.α456 (Real.pi / 2 - Erdos634.Draft.FluxRow4Witness.α456)
    (Real.pi / 2)
    hαβ_final hαγ_final hαπ_final hα0_final hβγ_final hβπ_final hβ0_final hγπ_final hγ0_final
    hπ0_final rfl rfl hαpos_final hirr_final model'_angleAt0 model'_angleAt1 model'_angleAt2

end Erdos634.Draft.FluxGRow3WitnessFinal

#print axioms Erdos634.Draft.FluxGRow3WitnessFinal.model'_angleAt1
#print axioms Erdos634.Draft.FluxGRow3WitnessFinal.model'_angleAt2
#print axioms Erdos634.Draft.FluxGRow3WitnessFinal.row3_lemmaA_final
