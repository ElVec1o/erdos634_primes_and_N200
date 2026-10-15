/-
Draft/W13.lean: the member `(1, 3)`: the base-β target `T_M(1, 3)` (legs `27 M`, base `26 M`, tile `(3, 8, 9)`) has a
tiling at every scale `M ≥ 3`.

    theorem w13_scale4 : ∃ D : CongruentDissection 272, HasSides D.target 108 96 68 ∧ HasSides D.model 9 3 8
    theorem w13_scale5 : ∃ D : CongruentDissection 425, HasSides D.target 135 120 85 ∧ HasSides D.model 9 3 8
    theorem wClosed_3_ge : ∀ M, 3 ≤ M → WClosed 3 _ M
    theorem betaTilable_1_3_ge : ∀ M, 3 ≤ M → BetaTilable 1 3 M
    theorem tileCount_26_sq / tileCount_17_sq : 26 M² and 17 M² are tile counts for M ≥ 3

`Draft.WClosedBase.betaTilable_ge` needs the triangle `W` at the scales `4` and `5`.  These two tilings (272 and 425
tiles, coordinates in `ℤ[√35]/18`) are kernel-checked certificates `R272Tiling`, `R425Tiling`.

The tilings are due to D. Paliy: they are the seed at scale 3 with one and two exterior collars, transcribed from his
note "A six-block cap for every primitive W and beta tile" (unrefereed), and verified exactly.
That note states the existence at every scale `≥ 3`.  What is added here is the kernel check of the two tilings and a Lean proof for all `M ≥ 3`
(by the addition of W-triangles, not by the collar).  With the exclusions at `M = 1, 2` this gives the threshold
statement of the member `(1, 3)` (`UniformThresholdCert.threshold_1_3`).
No sorry, no native_decide.
-/
import Erdos634.R272TilingBridge
import Erdos634.R425TilingBridge
import Erdos634.Draft.WClosedBase
import Erdos634.Realizable

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.W13
open Erdos634.Draft.WAddF Erdos634.Draft.WClosedBase Erdos634.Draft.TileCountFamilies
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.UniformThreshold (BetaTilable hasSides_congr)

theorem eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 < c) (h : d ^ 2 = c ^ 2) : d = c := by
  have h2 : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · linarith

open Erdos634.Realizable in
/-- A dissection whose six squared side lengths are known at scale `σ` gives, after the homothety of ratio `1/σ`, a
dissection with the side lengths themselves. -/
theorem hasSides_of_sq {N : ℕ} (D : CongruentDissection N) (σ t01 t12 t20 m01 m12 m20 : ℝ) (hσ : 0 < σ)
    (h1 : 0 < t01) (h2 : 0 < t12) (h3 : 0 < t20) (h4 : 0 < m01) (h5 : 0 < m12) (h6 : 0 < m20)
    (T1 : dist (D.target.pts 0) (D.target.pts 1) ^ 2 = (σ * t01) ^ 2)
    (T2 : dist (D.target.pts 1) (D.target.pts 2) ^ 2 = (σ * t12) ^ 2)
    (T3 : dist (D.target.pts 2) (D.target.pts 0) ^ 2 = (σ * t20) ^ 2)
    (M1 : dist (D.model.pts 0) (D.model.pts 1) ^ 2 = (σ * m01) ^ 2)
    (M2 : dist (D.model.pts 1) (D.model.pts 2) ^ 2 = (σ * m12) ^ 2)
    (M3 : dist (D.model.pts 2) (D.model.pts 0) ^ 2 = (σ * m20) ^ 2) :
    ∃ D' : CongruentDissection N, HasSides D'.target t12 t20 t01 ∧ HasSides D'.model m12 m20 m01 := by
  have hν : (0 : ℝ) < 1 / σ := by positivity
  have hc : ∀ x : ℝ, 1 / σ * (σ * x) = x := fun x => by field_simp
  set Ds := scaleDissection (D.model.pts 0) (1 / σ) hν.ne' D with hDs
  have htd : ∀ i j : Fin 3,
      dist (Ds.target.pts i) (Ds.target.pts j) = 1 / σ * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hDs, scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, abs_of_pos hν]
  have hmd : ∀ i j : Fin 3,
      dist (Ds.model.pts i) (Ds.model.pts j) = 1 / σ * dist (D.model.pts i) (D.model.pts j) := by
    intro i j
    rw [hDs, scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, abs_of_pos hν]
  have t01' := eq_of_sq dist_nonneg (mul_pos hσ h1) T1
  have t12' := eq_of_sq dist_nonneg (mul_pos hσ h2) T2
  have t20' := eq_of_sq dist_nonneg (mul_pos hσ h3) T3
  have m01' := eq_of_sq dist_nonneg (mul_pos hσ h4) M1
  have m12' := eq_of_sq dist_nonneg (mul_pos hσ h5) M2
  have m20' := eq_of_sq dist_nonneg (mul_pos hσ h6) M3
  refine ⟨Ds, ⟨Equiv.refl _, ?_, ?_, ?_⟩, ⟨Equiv.refl _, ?_, ?_, ?_⟩⟩
  · simp only [Equiv.refl_apply]; rw [htd, t12', hc]
  · simp only [Equiv.refl_apply]; rw [htd, t20', hc]
  · simp only [Equiv.refl_apply]; rw [htd, t01', hc]
  · simp only [Equiv.refl_apply]; rw [hmd, m12', hc]
  · simp only [Equiv.refl_apply]; rw [hmd, m20', hc]
  · simp only [Equiv.refl_apply]; rw [hmd, m01', hc]

/-- **`W` of the member `(1, 3)` at scale `4`**: the triangle `(68, 108, 96)` is cut into `272` copies of `(3, 8, 9)`. -/
theorem w13_scale4 : ∃ D : CongruentDissection 272, HasSides D.target 108 96 68 ∧ HasSides D.model 9 3 8 := by
  obtain ⟨D, t1, t2, t3, m1, m2, m3⟩ := Erdos634.R272TilingBridge.r272_dissection_shape
  exact hasSides_of_sq D 18 68 108 96 8 9 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [t1]; norm_num) (by rw [t2]; norm_num) (by rw [t3]; norm_num)
    (by rw [m1]; norm_num) (by rw [m2]; norm_num) (by rw [m3]; norm_num)

/-- **`W` of the member `(1, 3)` at scale `5`**: the triangle `(85, 135, 120)` is cut into `425` copies of `(3, 8, 9)`. -/
theorem w13_scale5 : ∃ D : CongruentDissection 425, HasSides D.target 135 120 85 ∧ HasSides D.model 9 3 8 := by
  obtain ⟨D, t1, t2, t3, m1, m2, m3⟩ := Erdos634.R425TilingBridge.r425_dissection_shape
  exact hasSides_of_sq D 18 85 135 120 8 9 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [t1]; norm_num) (by rw [t2]; norm_num) (by rw [t3]; norm_num)
    (by rw [m1]; norm_num) (by rw [m2]; norm_num) (by rw [m3]; norm_num)

theorem hf3 : 2 ≤ 3 := by norm_num

theorem wClosed_3_4 : WClosed 3 hf3 4 := by
  obtain ⟨D, hT, hM⟩ := w13_scale4
  exact WClosed_of_dissection 3 hf3 4 (by norm_num) D
    (hasSides_congr (hasSides_swap hT) (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr (hasSides_swap hM) (by norm_num) (by norm_num) (by norm_num))

theorem wClosed_3_5 : WClosed 3 hf3 5 := by
  obtain ⟨D, hT, hM⟩ := w13_scale5
  exact WClosed_of_dissection 3 hf3 5 (by norm_num) D
    (hasSides_congr (hasSides_swap hT) (by norm_num) (by norm_num) (by norm_num))
    (hasSides_congr (hasSides_swap hM) (by norm_num) (by norm_num) (by norm_num))

theorem base3 : ∀ r, 1 ≤ r → r < 3 → WClosed 3 hf3 (3 + r) := by
  intro r h1 h2
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact wClosed_3_4
  · exact wClosed_3_5

/-- **`W` of the member `(1, 3)` at every scale `M ≥ 3`.** -/
theorem wClosed_3_ge : ∀ M, 3 ≤ M → WClosed 3 hf3 M := WClosed_ge 3 hf3 base3

/-- **The base-β target of the member `(1, 3)` has a tiling at every scale `M ≥ 3`.** -/
theorem betaTilable_1_3_ge : ∀ M, 3 ≤ M → BetaTilable 1 3 M := betaTilable_ge 3 hf3 base3

/-- `26 M²` is a tile count for every `M ≥ 3` (base-β target of `(1, 3)` at scale `M`). -/
theorem tileCount_26_sq {M : ℕ} (hM : 3 ≤ M) : TileCount (26 * M ^ 2) := by
  obtain ⟨D, -, -⟩ := Erdos634.Draft.WtoDeltaF.delta_cd_of_W 3 hf3 M (by omega) (wClosed_3_ge M hM)
  exact ⟨D⟩

/-- `17 M²` is a tile count for every `M ≥ 3` (the triangle `W` of `(1, 3)` at scale `M`). -/
theorem tileCount_17_sq {M : ℕ} (hM : 3 ≤ M) : TileCount (17 * M ^ 2) := by
  obtain ⟨R⟩ := wClosed_3_ge M hM
  have hF1 := Erdos634.Draft.WPgramF.hF 3 hf3
  have hm0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hu := mul_pos (Erdos634.Draft.WGridF.A_pos 3 hf3) hm0
  have hv := mul_pos (Erdos634.Draft.WGridF.B_pos 3 hf3) hm0
  have hc : (WTriR ((3 : ℕ) : ℝ) hF1 _ _ hu hv).carrier = _ :=
    (carrier_WTriR _ hF1 _ _ hu hv).trans (congrArg _ (Erdos634.Draft.WtoDeltaF.WS_eq _ _ _ hm0))
  exact ⟨Erdos634.Draft.RegionTiling.toCD (T := WTriR ((3 : ℕ) : ℝ) hF1 _ _ hu hv)
    (Erdos634.Draft.CollarParam.RTiling.cast hc.symm R)⟩

end Erdos634.Draft.W13

#print axioms Erdos634.Draft.W13.w13_scale4
#print axioms Erdos634.Draft.W13.w13_scale5
#print axioms Erdos634.Draft.W13.wClosed_3_ge
#print axioms Erdos634.Draft.W13.betaTilable_1_3_ge
#print axioms Erdos634.Draft.W13.tileCount_26_sq
#print axioms Erdos634.Draft.W13.tileCount_17_sq
