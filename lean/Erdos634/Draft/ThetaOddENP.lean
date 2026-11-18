-- Draft/ThetaOddENP.lean -- ODD-E formalization, module 1: parameters `NP4` of the generalised notch seed (k : N, not a multiple of f).
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
**Generalised notch (GN) parameters.**  `NP4` is `ThetaNotch.NP3` with the natural number `j` (which forced `k = j f`) replaced by
a natural number `k` (the height of the base strip) and the REAL `j := k / f` used in the (already real-parametric) regions
`slReg`, `su2Reg`, `sgReg`, `rReg2`, `n2Reg` of `ThetaNotch`.  Hypotheses (b) (c) (d) become the integer versions
  (b') `e n f <= k b`,  (c) `e n + s f <= (M + k) f`,  (d) `e + g k <= g s`.
The notch construction is the project's (Bonfioli); the first instance `theta_13(3,4)` was found by computer search on 2026-11-15
and the family proof is `internal working notes` (GN = section 5.1).  Credit as in `ThetaNotch3NP`:
Paliy (band steps on a seed), Beeson (48-tile seed), Laczkovich, Zhang, Beeson-Rosu (skew frame).
INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEPos

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section

/-- natural-number parameter set of the generalised notch seed: `t = M + k`, `e M = f n1 + rho`, strips `n .. n1 - 1` -/
structure NP4 where
  e : ℕ
  f : ℕ
  g : ℕ
  b : ℕ
  M : ℕ
  n : ℕ
  n1 : ℕ
  k : ℕ
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
  hk : 0 < k
  hks : k < s
  hst : s < M + k
  hB : e * n * f ≤ k * b
  hC : e * n + s * f ≤ (M + k) * f
  hD : e + g * k ≤ g * s

namespace NP4
variable (P : NP4)

/-- the real parameter `j = k / f` of the regions -/
def jR : ℝ := (P.k : ℝ) / P.f

theorem hef : P.e < P.f := by have := P.hfg; have := P.hg; omega
theorem he0 : 0 < P.e := P.he
theorem hEF : (P.e : ℝ) < P.f := by exact_mod_cast P.hef
theorem hF0 : (0 : ℝ) < P.f := by have : (0 : ℝ) < P.e := by exact_mod_cast P.he0
                                  linarith [P.hEF]
theorem hbR : (P.b : ℝ) = (P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2 := by
  have : ((P.f * P.f : ℕ) : ℝ) = ((P.e * P.e + P.b : ℕ) : ℝ) := by rw [P.hb]
  push_cast at this; nlinarith
theorem hgR : (P.g : ℝ) = (P.f : ℝ) - P.e := by
  have : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  linarith
theorem rhoR : (P.rho : ℝ) = P.e * P.M - P.f * P.n1 := by
  have : ((P.e * P.M : ℕ) : ℝ) = ((P.f * P.n1 + P.rho : ℕ) : ℝ) := by rw [P.hrho]
  push_cast at this; linarith
/-- `j f = k` -/
theorem jRf : P.jR * P.f = P.k := by
  unfold jR; field_simp [P.hF0.ne']
theorem jR_pos : (0 : ℝ) < P.jR := by
  unfold jR; exact div_pos (by exact_mod_cast P.hk) P.hF0

theorem rhU : RHUB (P.e : ℝ) P.f P.M P.n1 P.jR := by
  have he : (1 : ℝ) ≤ P.e := by exact_mod_cast P.he
  have hg : (1 : ℝ) ≤ P.g := by exact_mod_cast P.hg
  have hn : (1 : ℝ) ≤ P.n := by exact_mod_cast P.hn
  have hnn : (P.n : ℝ) ≤ P.n1 := by exact_mod_cast P.hnn
  have hfg : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  have hgn : (P.e : ℝ) ≤ P.g * P.n := by exact_mod_cast P.hgn
  have hr1 : (1 : ℝ) ≤ P.rho := by exact_mod_cast P.hr1
  have hrf : (P.rho : ℝ) < P.f := by exact_mod_cast P.hrf
  have hbR := P.hbR
  have hgR := P.hgR
  have hrR := P.rhoR
  refine ⟨by linarith, P.hEF, ?_, by linarith, P.jR_pos, by linarith, ?_, by linarith, by linarith⟩
  · rw [← hbR]; nlinarith
  · rw [← hgR]; nlinarith

theorem rhR : RHRB (P.e : ℝ) P.f P.M P.n P.jR P.s := by
  have he : (1 : ℝ) ≤ P.e := by exact_mod_cast P.he
  have hg : (1 : ℝ) ≤ P.g := by exact_mod_cast P.hg
  have hn : (1 : ℝ) ≤ P.n := by exact_mod_cast P.hn
  have hnn : (P.n : ℝ) ≤ P.n1 := by exact_mod_cast P.hnn
  have hfg : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  have hgn : (P.e : ℝ) ≤ P.g * P.n := by exact_mod_cast P.hgn
  have hr1 : (1 : ℝ) ≤ P.rho := by exact_mod_cast P.hr1
  have hks : (P.k : ℝ) < P.s := by exact_mod_cast P.hks
  have hst : (P.s : ℝ) < P.M + P.k := by exact_mod_cast P.hst
  have hB : (P.e : ℝ) * P.n * P.f ≤ P.k * P.b := by exact_mod_cast P.hB
  have hC : (P.e : ℝ) * P.n + P.s * P.f ≤ (P.M + P.k) * P.f := by exact_mod_cast P.hC
  have hD : (P.e : ℝ) + P.g * P.k ≤ P.g * P.s := by exact_mod_cast P.hD
  have hbR := P.hbR
  have hgR := P.hgR
  have hrR := P.rhoR
  have hF : (0 : ℝ) < P.f := P.hF0
  have hj := P.jRf
  refine ⟨by linarith, P.hEF, ?_, by linarith, P.jR_pos, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hbR]; nlinarith
  · rw [← hgR]; exact hgn
  · nlinarith [mul_le_mul_of_nonneg_left hnn hF.le]
  · -- e n <= j b  <=>  e n f <= k b
    rw [← hbR]
    have : (P.e : ℝ) * P.n * P.f ≤ (P.jR * P.b) * P.f := by
      have : (P.jR * P.b) * P.f = P.k * P.b := by rw [mul_right_comm, hj]
      linarith
    exact le_of_mul_le_mul_right this hF
  · rw [hj]
    have : ((P.e : ℝ) * P.n) * P.f ≤ ((P.M + P.k - P.s) * P.f) * P.f := by nlinarith
    exact le_of_mul_le_mul_right this hF
  · rw [← hgR, hj]; nlinarith
  · rw [hj]; exact hks
  · rw [hj]; exact hst

/-- the strip hypotheses (`RHB`) for index `i` between `n` and `n1` -/
theorem rhB (i : ℕ) (hi : P.n ≤ i) (hi1 : i ≤ P.n1) : RHBB (P.e : ℝ) P.f P.M i P.jR := by
  have H := P.rhR
  have hiR : (P.n : ℝ) ≤ i := by exact_mod_cast hi
  have hiR1 : (i : ℝ) ≤ P.n1 := by exact_mod_cast hi1
  have hg : (0 : ℝ) < (P.f : ℝ) - P.e := by linarith [H.hg1]
  have hr1 : (1 : ℝ) ≤ P.rho := by exact_mod_cast P.hr1
  have hrR := P.rhoR
  have hF : (0 : ℝ) < P.f := P.hF0
  refine ⟨H.hE, H.hEF, H.hBE, by linarith [H.hn], H.hj, H.hg1, ?_, ?_⟩
  · nlinarith [H.hgn, mul_le_mul_of_nonneg_left hiR hg.le]
  · nlinarith [mul_le_mul_of_nonneg_left hiR1 hF.le]

end NP4

end

end Erdos634.Draft.ThetaNotch
