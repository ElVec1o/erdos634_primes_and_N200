-- Draft/ThetaNotch3Rho0.lean -- STAGE 2 (case rho = 0): the general statement through the OLD `NP` (n1 = n, strict (b), (c)), with explicit hypotheses.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
For `rho0f e f = 0` the pieces `rho-tau`, `rho-par` are absent; the old structure `NP` of `ThetaNotchNP` (`M = f m`, `n = e m`, `n1 = n`, strict (b), (c))
applies.  The statement below takes its three side conditions as HYPOTHESES (`e M0 / f = n0`, strict (b), strict (c)); they are decidable and hold for
every `e < f <= 700` with `rho = 0` (4000 rows, awk) -- the arithmetic proof that they always hold is NOT in Lean.
Superseded 2026-11-14: for e = 1 by `ThetaNotch4E1.rho0f_one` / `thetaTiled_general_rho0_e1`, for coprime e >= 2 `rho0f e f != 0` by `ThetaNotch4Rho.rho0f_ne_zero`; the closed statement is `ThetaNotch4Rho.thetaTiled_all`.
CREDIT: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch3Gen

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled thetaTiled_upset)

theorem thetaTiled_general_rho0 (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hr : rho0f e f = 0)
    (hn1 : e * M0f e f / f = n0f e f)
    (hB : e * n0f e f < j0f e f * (f * f - e * e))
    (hC : e * n0f e f + (j0f e f * f + n0f e f) * f < (M0f e f + j0f e f * f) * f) :
    ∀ t, t0f e f ≤ t → ThetaTiled e f (f * f - e * e) t := by
  intro t ht
  have hfpos : 0 < f := by omega
  have hepos : 0 < e := by omega
  have hdvd : f ∣ e * M0f e f := Nat.dvd_of_mod_eq_zero hr
  have hfM : f ∣ M0f e f := (Nat.Coprime.symm hco).dvd_of_dvd_mul_left hdvd
  obtain ⟨m, hm⟩ := hfM
  have hdiv : e * M0f e f / f = e * m := by
    rw [hm]; rw [show e * (f * m) = f * (e * m) by ring]; exact Nat.mul_div_cancel_left _ hfpos
  have hn0 : n0f e f = e * m := by rw [← hn1, hdiv]
  -- the old parameter set
  have hg : 0 < f - e := by omega
  have hbpos : e * e < f * f := Nat.mul_self_lt_mul_self hef
  have hn0e : e ≤ (f - e) * n0f e f := by unfold n0f; exact (ceil_facts e (f - e) hg).1
  have hn0p : 1 ≤ n0f e f := by
    by_contra hc
    have h0 : n0f e f = 0 := by omega
    rw [h0] at hn0e; simp at hn0e; omega
  have hmp : 1 ≤ m := by
    by_contra hc
    have : m = 0 := by omega
    rw [this] at hn0; simp at hn0; omega
  have hj0e : n0f e f * e ≤ (f * f - e * e) * j0f e f := by unfold j0f; exact (ceil_facts (n0f e f * e) (f * f - e * e) (by omega)).1
  have hj0 : 1 ≤ j0f e f := by
    have hne : 1 ≤ n0f e f * e := Nat.mul_pos hn0p hepos
    by_contra hc
    have h0 : j0f e f = 0 := by omega
    rw [h0] at hj0e; simp at hj0e; omega
  let P : NP :=
    { e := e, f := f, g := f - e, b := f * f - e * e, m := m, j := j0f e f, s := j0f e f * f + n0f e f
      he := he, hg := hg, hfg := by omega, hb := by omega, hm := hmp, hj := hj0
      hks := by omega, hst := by rw [hn0, hm] at *; nlinarith [hmp]
      hB := by rw [hn0] at hB; exact hB
      hC := by rw [hn0, hm] at hC; nlinarith [hC]
      hD := by
        have h5 : e + (f - e) * (j0f e f * f) ≤ (f - e) * (j0f e f * f + n0f e f) := by
          rw [Nat.mul_add]; unfold n0f at *; omega
        exact h5 }
  have h0 := thetaTiled_notch0 P
  have hg1 : e ≤ (f - e) * (f * (m + j0f e f)) := by
    have : e ≤ (f - e) * n0f e f := by unfold n0f; exact (ceil_facts e (f - e) hg).1
    have h2 : n0f e f ≤ f * (m + j0f e f) := by
      rw [hn0]; nlinarith [hmp, Nat.mul_le_mul_left e (Nat.le_mul_of_pos_left m hfpos)]
    exact le_trans this (Nat.mul_le_mul_left _ h2)
  have ht' : f * (m + j0f e f) ≤ t := by
    unfold t0f at ht; rw [hm] at ht; nlinarith [ht]
  exact thetaTiled_upset e f (f * f - e * e) _ he hef (by omega) hg1 h0 t ht'

end

end Erdos634.Draft.ThetaNotch
