-- Draft/ThetaNotch3NP.lean -- STAGE 1c: parameters of the notch seed with n1 >= n (mirrored T1 strips between theta_{n1}' and theta_n').
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy (band steps on a seed), Beeson (48-tile seed), Laczkovich (Lemma 2.2), Zhang, Beeson-Rosu (skew frame); the project.
Hand proof `internal working notes` 2.1; generator `rust/audit_notch_20261114` (`t2_region` at M with `n1 = floor(eM/f)`,
then the strips `theta_ms'' minus theta_{ms-1}''` for `ms = n+1..n1`, notch and Rh with the SMALLER `n`).
`RHU` = what the U-pieces (scale `n1`) need; `RHR` = what the R/N pieces (scale `n`) need.  `NP3` is the natural-number bundle (here `rho >= 1`).
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch2Inst

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section

/-- natural-number parameter set of the notch seed with strips (`rho >= 1`, `n <= n1`, `e M = f n1 + rho`) -/
structure NP3 where
  e : ℕ
  f : ℕ
  g : ℕ
  b : ℕ
  M : ℕ
  n : ℕ
  n1 : ℕ
  j : ℕ
  s : ℕ
  rho : ℕ
  he : 1 ≤ e
  hg : 1 ≤ g
  hfg : f = e + g
  hb : f * f = e * e + b
  hn : 1 ≤ n
  hnn : n ≤ n1
  hgn : e ≤ g * n
  hrho : e * M = f * n1 + rho
  hr1 : 1 ≤ rho
  hrf : rho < f
  hj : 1 ≤ j
  hks : j * f < s
  hst : s < M + j * f
  hB : e * n ≤ j * b
  hC : e * n + s * f ≤ (M + j * f) * f
  hD : e + g * (j * f) ≤ g * s

namespace NP3
variable (P : NP3)

theorem hef : P.e < P.f := by have := P.hfg; have := P.hg; omega
theorem he0 : 0 < P.e := P.he
theorem hEF : (P.e : ℝ) < P.f := by exact_mod_cast P.hef
theorem hbR : (P.b : ℝ) = (P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2 := by
  have : ((P.f * P.f : ℕ) : ℝ) = ((P.e * P.e + P.b : ℕ) : ℝ) := by rw [P.hb]
  push_cast at this; nlinarith
theorem hgR : (P.g : ℝ) = (P.f : ℝ) - P.e := by
  have : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  linarith
theorem rhoR : (P.rho : ℝ) = P.e * P.M - P.f * P.n1 := by
  have : ((P.e * P.M : ℕ) : ℝ) = ((P.f * P.n1 + P.rho : ℕ) : ℝ) := by rw [P.hrho]
  push_cast at this; linarith

theorem rhU : RHU (P.e : ℝ) P.f P.M P.n1 P.j := by
  have he : (1 : ℝ) ≤ P.e := by exact_mod_cast P.he
  have hg : (1 : ℝ) ≤ P.g := by exact_mod_cast P.hg
  have hn : (1 : ℝ) ≤ P.n := by exact_mod_cast P.hn
  have hnn : (P.n : ℝ) ≤ P.n1 := by exact_mod_cast P.hnn
  have hj : (1 : ℝ) ≤ P.j := by exact_mod_cast P.hj
  have hfg : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  have hgn : (P.e : ℝ) ≤ P.g * P.n := by exact_mod_cast P.hgn
  have hr1 : (1 : ℝ) ≤ P.rho := by exact_mod_cast P.hr1
  have hrf : (P.rho : ℝ) < P.f := by exact_mod_cast P.hrf
  have hbR := P.hbR
  have hgR := P.hgR
  have hrR := P.rhoR
  refine ⟨by linarith, P.hEF, ?_, by linarith, hj, by linarith, ?_, by linarith, by linarith⟩
  · rw [← hbR]; nlinarith
  · rw [← hgR]; nlinarith

theorem rhR : RHR (P.e : ℝ) P.f P.M P.n P.j P.s := by
  have he : (1 : ℝ) ≤ P.e := by exact_mod_cast P.he
  have hg : (1 : ℝ) ≤ P.g := by exact_mod_cast P.hg
  have hn : (1 : ℝ) ≤ P.n := by exact_mod_cast P.hn
  have hnn : (P.n : ℝ) ≤ P.n1 := by exact_mod_cast P.hnn
  have hj : (1 : ℝ) ≤ P.j := by exact_mod_cast P.hj
  have hfg : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  have hgn : (P.e : ℝ) ≤ P.g * P.n := by exact_mod_cast P.hgn
  have hr1 : (1 : ℝ) ≤ P.rho := by exact_mod_cast P.hr1
  have hks : (P.j : ℝ) * P.f < P.s := by exact_mod_cast P.hks
  have hst : (P.s : ℝ) < P.M + P.j * P.f := by exact_mod_cast P.hst
  have hB : (P.e : ℝ) * P.n ≤ P.j * P.b := by exact_mod_cast P.hB
  have hC : (P.e : ℝ) * P.n + P.s * P.f ≤ (P.M + P.j * P.f) * P.f := by exact_mod_cast P.hC
  have hD : (P.e : ℝ) + P.g * (P.j * P.f) ≤ P.g * P.s := by exact_mod_cast P.hD
  have hbR := P.hbR
  have hgR := P.hgR
  have hrR := P.rhoR
  have hF : (0 : ℝ) < P.f := by linarith
  refine ⟨by linarith, P.hEF, ?_, hn, hj, by linarith, ?_, ?_, ?_, ?_, ?_, hks, hst⟩
  · rw [← hbR]; nlinarith
  · rw [← hgR]; exact hgn
  · nlinarith [mul_le_mul_of_nonneg_left hnn hF.le]
  · rw [← hbR]; exact hB
  · nlinarith
  · rw [← hgR]; nlinarith

end NP3

end

end Erdos634.Draft.ThetaNotch
