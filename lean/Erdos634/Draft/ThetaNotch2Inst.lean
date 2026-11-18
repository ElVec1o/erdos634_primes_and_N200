-- Draft/ThetaNotch2Inst.lean -- instances and controls of the notch seed with rho > 0 (n1 = n, strict (b), (c)).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
* `ThetaTiled 2 3 5 7` (245 tiles, `NP2` witness `(j,M,n,s,rho) = (1,4,2,5,2)`), `ThetaTiled 3 8 55 11` (`(1,3,1,9,1)`), with the up-set.
* `TileCount 245`, `6655 = 55 * 11^2`, `7920 = 55 * 12^2`.
* controls: the hypotheses of `NP2` are witnessed (the two `def`s); at `(e,f) = (2,3)` no `NP2` has `t <= 6` (consistent with the
  proved NO `ThetaUnitUp.not_thetaTiled_2_3_t4`, `_t3`); `t = 6` at `(2,3)` is not reached by this file (and stays open).
CREDIT: Paliy (annulus / band steps on a seed), Beeson (48 seed), Laczkovich, Zhang.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch2Main
import Erdos634.Draft.ThetaUnitUp

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled thetaTiled_upset)
open Erdos634.Draft.TileCountFamilies (TileCount)

namespace NP2
theorem hnM (P : NP2) : P.n ≤ P.M := by
  have h := P.hrho
  have h1 : P.e < P.f := P.hef
  have h2 := P.hn
  by_contra hc; push_neg at hc
  nlinarith [Nat.mul_le_mul_left P.e hc.le, Nat.mul_le_mul_right P.n h1.le]

/-- the up-set of the seed: `theta_t` for every `t >= M + j f` -/
theorem thetaTiled_up (P : NP2) : ∀ t, P.M + P.j * P.f ≤ t → ThetaTiled P.e P.f P.b t := by
  intro t ht
  have hg : P.e ≤ (P.f - P.e) * (P.M + P.j * P.f) := by
    have h1 : P.f - P.e = P.g := by have := P.hfg; omega
    rw [h1]
    exact le_trans P.hgn (Nat.mul_le_mul_left _ (le_trans P.hnM (Nat.le_add_right _ _)))
  exact thetaTiled_upset P.e P.f P.b _ P.he P.hef P.hb hg (thetaTiled_notch1 P) t ht
end NP2

def np2_2_3 : NP2 where
  e := 2
  f := 3
  g := 1
  b := 5
  M := 4
  n := 2
  j := 1
  s := 5
  rho := 2
  he := by norm_num
  hg := by norm_num
  hfg := by norm_num
  hb := by norm_num
  hn := by norm_num
  hgn := by norm_num
  hrho := by norm_num
  hr1 := by norm_num
  hrf := by norm_num
  hj := by norm_num
  hks := by norm_num
  hst := by norm_num
  hB := by norm_num
  hC := by norm_num
  hD := by norm_num

def np2_3_8 : NP2 where
  e := 3
  f := 8
  g := 5
  b := 55
  M := 3
  n := 1
  j := 1
  s := 9
  rho := 1
  he := by norm_num
  hg := by norm_num
  hfg := by norm_num
  hb := by norm_num
  hn := by norm_num
  hgn := by norm_num
  hrho := by norm_num
  hr1 := by norm_num
  hrf := by norm_num
  hj := by norm_num
  hks := by norm_num
  hst := by norm_num
  hB := by norm_num
  hC := by norm_num
  hD := by norm_num

/-- **Stage 1b instance**: `theta_7(2,3)`, 245 tiles of `(6,5,9)`. -/
theorem thetaTiled_2_3_5_7 : ThetaTiled 2 3 5 7 := thetaTiled_notch1 np2_2_3
/-- **Stage 1b instance**: `theta_11(3,8)`, 6655 tiles of `(24,55,64)`. -/
theorem thetaTiled_3_8_55_11 : ThetaTiled 3 8 55 11 := thetaTiled_notch1 np2_3_8

theorem thetaTiled_2_3_up : ∀ t, 7 ≤ t → ThetaTiled 2 3 5 t := NP2.thetaTiled_up np2_2_3
theorem thetaTiled_3_8_up : ∀ t, 11 ≤ t → ThetaTiled 3 8 55 t := NP2.thetaTiled_up np2_3_8

theorem tileCount_245 : TileCount 245 := by obtain ⟨D, -, -⟩ := thetaTiled_2_3_5_7; exact ⟨D⟩
theorem tileCount_6655 : TileCount 6655 := by obtain ⟨D, -, -⟩ := thetaTiled_3_8_55_11; exact ⟨D⟩
theorem tileCount_7920 : TileCount 7920 := by obtain ⟨D, -, -⟩ := thetaTiled_3_8_up 12 (by norm_num); exact ⟨D⟩

/-! ### controls -/

/-- **Witness**: the hypotheses of `NP2` are satisfiable (the two instances above). -/
theorem np2_witnesses : np2_2_3.rho = 2 ∧ np2_3_8.rho = 1 ∧ np2_2_3.e * np2_2_3.M = np2_2_3.f * np2_2_3.n + np2_2_3.rho := ⟨rfl, rfl, rfl⟩

/-- **Negative control (hypothesis boundary)**: at `(e,f) = (2,3)` no `NP2` parameter set has `t <= 6`. -/
theorem np2_boundary_2_3 (P : NP2) (he : P.e = 2) (hf : P.f = 3) : 7 ≤ P.M + P.j * P.f := by
  have h1 := P.hrho; have h2 := P.hB; have h3 := P.hC; have h4 := P.hD; have h5 := P.hst; have h6 := P.hfg; have h7 := P.hks
  have h8 := P.hb; have h9 := P.hgn; have h10 := P.hrf; have h11 := P.hr1; have h12 := P.hn; have h13 := P.hj
  simp only [he, hf] at *
  have hg1 : P.g = 1 := by omega
  have hb5 : P.b = 5 := by omega
  rw [hg1] at h4 h9
  rw [hb5] at h2
  omega

/-- consistency with the proved NO `ThetaUnitUp.not_thetaTiled_2_3_t4`: no `NP2` at `(2,3)` has `t = 4` (nor `t = 3`). -/
theorem np2_consistent_2_3 (P : NP2) (he : P.e = 2) (hf : P.f = 3) : P.M + P.j * P.f ≠ 4 ∧ P.M + P.j * P.f ≠ 3 := by
  have := np2_boundary_2_3 P he hf; omega

end

end Erdos634.Draft.ThetaNotch
