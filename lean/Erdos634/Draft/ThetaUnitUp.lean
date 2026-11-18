-- Draft/ThetaUnitUp.lean -- up-set, family theorem, instances and controls for the UNIT THETA STEP.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Consequences of `ThetaUnitStep.thetaTiled_step`:

* `thetaTiled_upset`   : `ThetaTiled e f b n`, `e <= (f-e) n`, `n <= M`  ==>  `ThetaTiled e f b M`.
* `thetaTiled_of_theta_exists` / `theta_exists_of_thetaTiled` : `ThetaTiled e f b (j (b + f f))` is EXACTLY the conclusion of
  `ThetaCompose.theta_exists` (same target sides, same model sides, same count): the statement-match lemma.
* `thetaTiled_thin_family` : for a thin coprime row (`e f < b`, `f f = e e + b`): `ThetaTiled e f b t` for EVERY `t >= b + f f = 2 f^2 - e^2`;
  hence `TileCount (b t^2)` for all such `t`.
* instances at `(e,f) = (3,8)`, `b = 55`, seed `t = 119` (`ThetaCompose.tileCount_778855`): `TileCount` of
  `805255 = 55*121^2`, `832095 = 55*123^2`, `873180 = 55*126^2`, `915255 = 55*129^2`.
* controls: hypothesis satisfiable (the seed `(3,8,119)` satisfies `e <= (f-e) n` and `ThetaTiled`); known NO values: via
  `ThetaKill.theta_thick`, `theta_{4}(2,3)` is not tiled, and the step then forces `theta_3(2,3)` not tiled (consistent with
  ThetaKill: `3 < 5`); the hypothesis `e <= (f-e) n` fails at `(2,3), n = 1`.

CREDIT: Paliy (annulus / band steps on a seed, 2026-10-08: prior art for the method; +e, +f annuli), Zhang (the families),
Beeson-Rosu (frame, `W`), this project (`ThetaCompose`, `ThetaKill`).  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaUnitStep
import Erdos634.Draft.ThetaKill

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaUnit
noncomputable section
open Erdos634.Draft.TileCountFamilies (TileCount)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

/-- **Up-set.** -/
theorem thetaTiled_upset (e f b n : ℕ) (he : 1 ≤ e) (hef : e < f) (hb : f * f = e * e + b)
    (hg : e ≤ (f - e) * n) (h : ThetaTiled e f b n) : ∀ M, n ≤ M → ThetaTiled e f b M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => exact h
  | succ m hm ih =>
    exact thetaTiled_step e f b m he hef hb (le_trans hg (Nat.mul_le_mul_left _ hm)) ih

/-- **Statement match, direction 1**: the conclusion of `ThetaCompose.theta_exists` is `ThetaTiled e f b (j (b + f f))`. -/
theorem thetaTiled_of_theta_exists (e f b j : ℕ) (he : 1 ≤ e) (hco : Nat.Coprime e f) (hb : f * f = e * e + b)
    (hq : e * f < b) (hj : 1 ≤ j) (hjb : f ≤ j * b) : ThetaTiled e f b (j * (b + f * f)) := by
  obtain ⟨D, hDt, hDm⟩ := Erdos634.Draft.ThetaCompose.theta_exists e f b j he hco hb hq hj hjb
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  refine ⟨D, ?_, hDm⟩
  refine Erdos634.Draft.UniformThreshold.hasSides_congr hDt ?_ ?_ ?_ <;> (push_cast; rw [hbR]; ring)

/-- **Statement match, direction 2**: `ThetaTiled e f b (j (b + f f))` is the conclusion of `theta_exists` verbatim. -/
theorem theta_exists_of_thetaTiled (e f b j : ℕ) (hb : f * f = e * e + b)
    (h : ThetaTiled e f b (j * (b + f * f))) :
    ∃ D : CongruentDissection (b * (j * (b + f * f)) * (j * (b + f * f))),
      HasSides D.target ((j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        ((j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        ((j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ∧
      HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  obtain ⟨D, hDt, hDm⟩ := h
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  refine ⟨D, ?_, hDm⟩
  refine Erdos634.Draft.UniformThreshold.hasSides_congr hDt ?_ ?_ ?_ <;> (push_cast; rw [hbR]; ring)

/-- **The thin family.**  For a thin coprime row, `theta_t(e,f)` is tiled for every `t >= 2 f^2 - e^2 = b + f f`. -/
theorem thetaTiled_thin_family (e f b : ℕ) (he : 1 ≤ e) (hco : Nat.Coprime e f) (hb : f * f = e * e + b)
    (hq : e * f < b) : ∀ t, b + f * f ≤ t → ThetaTiled e f b t := by
  have hef : e < f := Erdos634.Draft.G2Param.lt_of_thin e f b hb hq
  have hfb : f ≤ 1 * b := by nlinarith
  have h0 := thetaTiled_of_theta_exists e f b 1 he hco hb hq le_rfl hfb
  rw [one_mul] at h0
  have hg : e ≤ (f - e) * (b + f * f) := by
    have h1 : 1 ≤ f - e := by omega
    calc e ≤ f * f := by nlinarith
      _ ≤ b + f * f := Nat.le_add_left _ _
      _ = 1 * (b + f * f) := (one_mul _).symm
      _ ≤ (f - e) * (b + f * f) := Nat.mul_le_mul_right _ h1
  exact thetaTiled_upset e f b (b + f * f) he hef hb hg h0

/-- the family as tile counts -/
theorem tileCount_thin_family (e f b : ℕ) (he : 1 ≤ e) (hco : Nat.Coprime e f) (hb : f * f = e * e + b)
    (hq : e * f < b) (t : ℕ) (ht : b + f * f ≤ t) : TileCount (b * t * t) := by
  obtain ⟨D, -, -⟩ := thetaTiled_thin_family e f b he hco hb hq t ht
  exact ⟨D⟩

/-! ### Instances at `(e, f) = (3, 8)`, `b = 55` (seed `t = 119`, `ThetaCompose.tileCount_778855`) -/

theorem tileCount_805255 : TileCount 805255 :=
  tileCount_thin_family 3 8 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 121 (by norm_num)
theorem tileCount_832095 : TileCount 832095 :=
  tileCount_thin_family 3 8 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 123 (by norm_num)
theorem tileCount_873180 : TileCount 873180 :=
  tileCount_thin_family 3 8 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 126 (by norm_num)
theorem tileCount_915255 : TileCount 915255 :=
  tileCount_thin_family 3 8 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 129 (by norm_num)

/-! ### Witness and controls -/

/-- **Witness.**  The hypotheses of the step are satisfied by a real instance: the seed `theta_119(3,8)` is tiled and
`3 <= (8-3) * 119`; so the step is applied non-vacuously (it produces `theta_120(3,8)`). -/
theorem witness_seed_3_8 : ThetaTiled 3 8 55 119 ∧ 3 ≤ (8 - 3) * 119 ∧ ThetaTiled 3 8 55 120 := by
  have h := thetaTiled_thin_family 3 8 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 119 (by norm_num)
  refine ⟨h, by norm_num, ?_⟩
  exact thetaTiled_step 3 8 55 119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

/-- **Negative control 1.**  `theta_4(2,3)` is not tiled (`ThetaKill.theta_thick`, thick member `e = f - 1`: `t >= f + 2 = 5`). -/
theorem not_thetaTiled_2_3_t4 : ¬ ThetaTiled 2 3 5 4 := by
  rintro ⟨D, hT, hM⟩
  have := Erdos634.Draft.ThetaKill.theta_thick (N := 5 * 4 * 4) D (t := 4) (f := 3) (by norm_num) (by norm_num)
    (by
      refine Erdos634.Draft.UniformThreshold.hasSides_congr hT ?_ ?_ ?_ <;> (push_cast; norm_num))
    (by
      refine Erdos634.Draft.UniformThreshold.hasSides_congr hM ?_ ?_ ?_ <;> (push_cast; norm_num))
  omega

/-- **Negative control 2 (the step cannot be run at a known NO value).**  The hypothesis `2 <= (3-2) * 3` holds, and
`theta_4(2,3)` is not tiled, so by the step `theta_3(2,3)` is not tiled either: the step is consistent with `ThetaKill`
(`3 < f + 2 = 5`), it propagates NO downwards and never produces a tiling there. -/
theorem not_thetaTiled_2_3_t3 : ¬ ThetaTiled 2 3 5 3 := fun h =>
  not_thetaTiled_2_3_t4 (thetaTiled_step 2 3 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h)

/-- **Negative control 3.**  The hypothesis `e <= (f-e) n` is not trivial: it fails at `(e,f,n) = (2,3,1)`. -/
theorem hyp_fails_2_3_1 : ¬ (2 ≤ (3 - 2) * 1) := by norm_num

end

end Erdos634.Draft.ThetaUnit
