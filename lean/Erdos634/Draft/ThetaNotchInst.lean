-- Draft/ThetaNotchInst.lean -- instances, the e = 1 family, TileCount values and controls of the notch seed (case rho = 0).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
STAGE 2 / STAGE 3 (YES half) for the rows with `e M = f n`:
* `ThetaTiled 1 2 3 4` (48 tiles), `ThetaTiled 1 3 8 6` (288), `ThetaTiled 1 6 35 12` (5040): `NP` witnesses `m = j = 1`, `s = f + 1`.
* `thetaTiled_e1 : ThetaTiled 1 f (f^2-1) t` for all `f >= 2`, `t >= 2 f` (Corollary N1, YES half), with the up-set of `ThetaUnitUp`.
* `TileCount 48, 288, 5040, 5915, 6860, 7875` (and `35 t^2` for every `t >= 12` at `f = 6`).
* controls: the hypotheses of `NP` are satisfiable (the witnesses), and at `(e,f) = (2,3)` no `NP` has `t < 9` (so the case rho = 0
  does not reach `t = 7`, which needs rho = 2: not covered here); the existing NO `not_thetaTiled_2_3_t4` is not contradicted.
CREDIT: Paliy (annulus / band steps on a seed), Beeson (48 seed), Laczkovich, Zhang.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchMain
import Erdos634.Draft.ThetaUnitUp

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled thetaTiled_upset)
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- the parameter set of the `e = 1` seed: `m = j = 1`, `s = f + 1` -/
def npE1 (f : ℕ) (hf : 2 ≤ f) : NP where
  e := 1
  f := f
  g := f - 1
  b := f * f - 1
  m := 1
  j := 1
  s := f + 1
  he := le_rfl
  hg := by omega
  hfg := by omega
  hb := by have : 1 ≤ f * f := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
  hm := le_rfl
  hj := le_rfl
  hks := by omega
  hst := by omega
  hB := by
    have : 4 ≤ f * f := by nlinarith
    omega
  hC := by nlinarith
  hD := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
    have : (k + 2 - 1) = k + 1 := by omega
    rw [this]; nlinarith

/-- **Seed at `e = 1`**: `theta_{2f}(1,f)` is tiled (`4 f^2 (f^2-1)` tiles), every `f >= 2`. -/
theorem thetaTiled_e1_seed (f : ℕ) (hf : 2 ≤ f) : ThetaTiled 1 f (f * f - 1) (f * (1 + 1)) :=
  thetaTiled_notch0 (npE1 f hf)

/-- **Corollary N1, YES half.**  For `e = 1` and every `f >= 2`: `theta_t(1,f)` is tiled for every `t >= 2 f`
(the NO half is `ThetaKill.theta_e1`). -/
theorem thetaTiled_e1 (f : ℕ) (hf : 2 ≤ f) : ∀ t, 2 * f ≤ t → ThetaTiled 1 f (f * f - 1) t := by
  have h0 := thetaTiled_e1_seed f hf
  have hb : f * f = 1 * 1 + (f * f - 1) := by have : 1 ≤ f * f := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
  have hg : 1 ≤ (f - 1) * (f * (1 + 1)) := by
    have : 1 ≤ f - 1 := by omega
    nlinarith
  intro t ht
  exact thetaTiled_upset 1 f (f * f - 1) (f * (1 + 1)) le_rfl (by omega) hb hg h0 t (by omega)

theorem tileCount_e1 (f : ℕ) (hf : 2 ≤ f) (t : ℕ) (ht : 2 * f ≤ t) : TileCount ((f * f - 1) * t * t) := by
  obtain ⟨D, -, -⟩ := thetaTiled_e1 f hf t ht
  exact ⟨D⟩

/-! ### the three seeds and their `TileCount` values -/

theorem thetaTiled_1_2_3_4 : ThetaTiled 1 2 3 4 := thetaTiled_e1_seed 2 le_rfl
theorem thetaTiled_1_3_8_6 : ThetaTiled 1 3 8 6 := thetaTiled_e1_seed 3 (by norm_num)
theorem thetaTiled_1_6_35_12 : ThetaTiled 1 6 35 12 := thetaTiled_e1_seed 6 (by norm_num)

theorem tileCount_48 : TileCount 48 := by obtain ⟨D, -, -⟩ := thetaTiled_1_2_3_4; exact ⟨D⟩
theorem tileCount_288 : TileCount 288 := by obtain ⟨D, -, -⟩ := thetaTiled_1_3_8_6; exact ⟨D⟩
theorem tileCount_5040 : TileCount 5040 := by obtain ⟨D, -, -⟩ := thetaTiled_1_6_35_12; exact ⟨D⟩
theorem tileCount_5915 : TileCount 5915 := tileCount_e1 6 (by norm_num) 13 (by norm_num)
theorem tileCount_6860 : TileCount 6860 := tileCount_e1 6 (by norm_num) 14 (by norm_num)
theorem tileCount_7875 : TileCount 7875 := tileCount_e1 6 (by norm_num) 15 (by norm_num)

/-! ### controls -/

/-- **Witness**: the hypotheses of `NP` are satisfiable, at the three rows above (instances of `npE1`). -/
theorem np_witnesses : (npE1 2 le_rfl).s = 3 ∧ (npE1 3 (by norm_num)).s = 4 ∧ (npE1 6 (by norm_num)).s = 7 := ⟨rfl, rfl, rfl⟩

/-- **Negative control (hypothesis boundary)**: at `(e,f) = (2,3)` no parameter set of the case `rho = 0` has `t < 9`
(it would need `s >= 5` from (d) and `s <= 4` from (c) at `t = 6`); so this file does not reach `theta_7(2,3)`, which needs `rho = 2`. -/
theorem np_boundary_2_3 (P : NP) (he : P.e = 2) (hf : P.f = 3) : 9 ≤ P.f * (P.m + P.j) := by
  have h1 := P.hm; have h2 := P.hj; have h3 := P.hC; have h4 := P.hD; have h5 := P.hst; have h6 := P.hfg; have h7 := P.hks
  have h8 := P.hg
  simp only [he, hf] at h3 h4 h5 h6 h7
  rw [hf]
  have hg1 : P.g = 1 := by omega
  rw [hg1] at h4
  omega

/-- **Negative control (boundary at `(1,2)`)**: the smallest `t` of a parameter set at `(1,2)` is `4`; `t = 3` is not reached
(and `theta_3(1,2)` is not tiled by `ThetaKill`). -/
theorem np_boundary_1_2 (P : NP) (he : P.e = 1) (hf : P.f = 2) : 4 ≤ P.f * (P.m + P.j) := by
  have h1 := P.hm; have h2 := P.hj
  rw [hf]; omega

/-- consistency with the existing NO `ThetaUnitUp.not_thetaTiled_2_3_t4`: no parameter set at `(2,3)` has `t = 4`. -/
theorem np_consistent_2_3_t4 (P : NP) (he : P.e = 2) (hf : P.f = 3) : P.f * (P.m + P.j) ≠ 4 := by
  have := np_boundary_2_3 P he hf; omega

end

end Erdos634.Draft.ThetaNotch
