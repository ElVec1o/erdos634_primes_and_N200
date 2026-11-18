-- Draft/ThetaNotch4E1.lean -- G2 (e = 1 side conditions of `thetaTiled_general_rho0`) and G3 (equality branches of `NP3cond` witnessed).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
G2: for `f >= 2`: `n0f 1 f = 1`, `j0f 1 f = 1`, `M0f 1 f = f`, `rho0f 1 f = 0` (so `rho0f 1 f = 0` for EVERY `f >= 2`, not only for `f = 2, 3, 6`), and all the side hypotheses of
`ThetaNotch.thetaTiled_general_rho0` at `e = 1` (`n1 = n0`, strict (b), strict (c)) hold, so `thetaTiled_general_rho0 1 f` applies for every `f >= 2`
(`thetaTiled_general_rho0_e1`); `thetaTiled_e1` (ThetaNotchInst) gives the same statement directly.
G3: the equality branches of `NP3cond` (b) `e n <= j b` and (c) `e n + s f <= (M + j f) f` are witnessed by `decide`:
 * (c) equality (C2 absent): `(e,f,M,n,n1,j,s,rho) = (1,2,5,2,2,1,6,1)`: `e n + s f = 14 = (M + j f) f`, (b) strict `2 < 3`;
 * (b) equality (C1 absent): `(1,2,7,3,3,1,5,1)`: `e n = 3 = j b`, (c) strict `13 < 18`.
The audit's `eqwit_out.txt` lists only (c)-equality rows (6981); the (b)-equality witness above was found by hand (`b = 3`, `n = 3`, `j = 1`).
CREDIT: as ThetaNotch3*.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch4Rho

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled)
open Erdos634.Draft.TileCountFamilies (TileCount)

theorem n0f_one (f : ℕ) (hf : 2 ≤ f) : n0f 1 f = 1 := by
  unfold n0f
  have : 1 + (f - 1) - 1 = f - 1 := by omega
  rw [this]
  exact Nat.div_self (by omega)

theorem j0f_one (f : ℕ) (hf : 2 ≤ f) : j0f 1 f = 1 := by
  have hb : 0 < f * f - 1 * 1 := by
    have : 4 ≤ f * f := by nlinarith
    omega
  unfold j0f
  rw [n0f_one f hf]
  have : 1 * 1 + (f * f - 1 * 1) - 1 = f * f - 1 * 1 := by omega
  rw [this]
  exact Nat.div_self hb

theorem M0f_one (f : ℕ) (hf : 2 ≤ f) : M0f 1 f = f := by
  unfold M0f
  rw [n0f_one f hf]
  have t2 : 1 + (1 * 1 + f - 1) / f = 2 := by
    have : (1 * 1 + f - 1) / f = 1 := by
      have : 1 * 1 + f - 1 = f := by omega
      rw [this]; exact Nat.div_self (by omega)
    omega
  have t1 : (f * 1 + 1 - 1) / 1 = f := by simp
  rw [t1, t2]
  exact max_eq_left hf

theorem rho0f_one (f : ℕ) (hf : 2 ≤ f) : rho0f 1 f = 0 := by
  unfold rho0f
  rw [M0f_one f hf]; simp

/-- G2: the three side hypotheses of `thetaTiled_general_rho0` at `e = 1`, for every `f >= 2`. -/
theorem thetaTiled_general_rho0_e1 (f : ℕ) (hf : 2 ≤ f) : ∀ t, t0f 1 f ≤ t → ThetaTiled 1 f (f * f - 1 * 1) t := by
  have hn := n0f_one f hf
  have hj := j0f_one f hf
  have hM := M0f_one f hf
  have h4 : 4 ≤ f * f := by nlinarith
  refine thetaTiled_general_rho0 1 f (le_refl 1) (by omega) (Nat.coprime_one_left f) (rho0f_one f hf) ?_ ?_ ?_
  · rw [hn, hM]; simp; exact Nat.div_self (by omega)
  · rw [hn, hj]; omega
  · rw [hn, hj, hM]; nlinarith

/-! ### G3: the equality branches of `NP3cond` -/

/-- (c) equality, (b) strict: `theta_t(1,2)` for `t >= 5 + 2 = 7`, via `NP3cond 1 2 5 2 2 1 6 1`. -/
theorem np3cond_eq_c : NP3cond 1 2 5 2 2 1 6 1 := by decide
theorem np3cond_eq_c_equalities : 1 * 2 + 6 * 2 = (5 + 1 * 2) * 2 ∧ 1 * 2 < 1 * (2 * 2 - 1 * 1) := by decide
theorem thetaTiled_eq_c : ∀ t, 5 + 1 * 2 ≤ t → ThetaTiled 1 2 (2 * 2 - 1 * 1) t :=
  thetaTiled_of_cond 1 2 5 2 2 1 6 1 np3cond_eq_c

/-- (b) equality, (c) strict: `theta_t(1,2)` for `t >= 7 + 2 = 9`, via `NP3cond 1 2 7 3 3 1 5 1`. -/
theorem np3cond_eq_b : NP3cond 1 2 7 3 3 1 5 1 := by decide
theorem np3cond_eq_b_equalities : 1 * 3 = 1 * (2 * 2 - 1 * 1) ∧ 1 * 3 + 5 * 2 < (7 + 1 * 2) * 2 := by decide
theorem thetaTiled_eq_b : ∀ t, 7 + 1 * 2 ≤ t → ThetaTiled 1 2 (2 * 2 - 1 * 1) t :=
  thetaTiled_of_cond 1 2 7 3 3 1 5 1 np3cond_eq_b

theorem tileCount_eq_c : TileCount (3 * 7 * 7) := by obtain ⟨D, -, -⟩ := thetaTiled_eq_c 7 (by norm_num); exact ⟨D⟩
theorem tileCount_eq_b : TileCount (3 * 9 * 9) := by obtain ⟨D, -, -⟩ := thetaTiled_eq_b 9 (by norm_num); exact ⟨D⟩

end
end Erdos634.Draft.ThetaNotch
