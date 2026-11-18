-- Draft/ThetaNotch2NP.lean -- STAGE 1b: parameters of the notch seed with rho = e M - f n > 0 (n1 = n), real and natural level.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy (band steps on a seed), Beeson (48-tile seed), Laczkovich (Lemma 2.2), Zhang, Beeson-Rosu (skew frame); the project.
Hand proof: `internal working notes` 2.1; generator `rust/audit_notch_20261114` (`t2_region`, case rho > 0, n1 = n).
Notation: `E F` = e f, `B = F^2-E^2`, `k = j F`, `t = M + k`, `rho = E M - F n`, `v = F M - E n - E`.
Apex data (apex unit frame): D=(0,k), V1=(v/F,k), V2=(0,k+F v/B); X5=(M-n,k), W=(M-E n/F,k), U5=(M-n,k+F n/(E+F));
Qv=(rho/E, t-rho/E), Vt=(0,t); Z=(M+E n F/B, k-E n F/B).  Pieces: v-tau (D,V1,V2); pi5 (X5,W,U5); pi4 = Par(Qv,w1,w2; F, g n);
rho-tau (Qv,Qp,Vt) with Qp = Qv + (0,-E rho/B); rho-par = Par(Vt,w1,w2; F-rho, rho); C1, C2, C3 (Rh minus (en)tau); notch (Qv,W,Z).
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchMain

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section

/-- real-level hypotheses (case `rho > 0`, `n1 = n`).  `hB, hC, hD` are the conditions (b), (c) (strict), (d) of the hand theorem. -/
structure RH2 (E F M n j s : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hn : 1 ≤ n
  hj : 1 ≤ j
  hg1 : 1 ≤ F - E
  hgn : E ≤ (F - E) * n
  hr0 : 0 < E * M - F * n
  hrF : E * M - F * n < F
  hB : E * n ≤ j * (F ^ 2 - E ^ 2)
  hC : E * n ≤ (M + j * F - s) * F
  hD : E ≤ (F - E) * (s - j * F)
  hks : j * F < s
  hst : s < M + j * F

def vv (E F M n : ℝ) : ℝ := F * M - E * n - E
def c0f (E F M n j : ℝ) : ℝ := F ^ 2 * M + (F ^ 2 - E ^ 2) * (j * F) - E * F * n
def laf (E F M n j : ℝ) : ℝ := (F ^ 2 - E ^ 2) * (j * F) + F * vv E F M n
def c5f (E F M n j : ℝ) : ℝ := F ^ 2 * M - E * F * n + (2 * F ^ 2 - E ^ 2) * (j * F)
def rho2 (E F M n : ℝ) : ℝ := E * M - F * n

structure RHU (E F M n j : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hn : 1 ≤ n
  hj : 1 ≤ j
  hg1 : 1 ≤ F - E
  hgn : E ≤ (F - E) * n
  hr0 : 0 < E * M - F * n
  hrF : E * M - F * n < F

structure RHR (E F M n j s : ℝ) : Prop where
  hE : 0 < E
  hEF : E < F
  hBE : E < F ^ 2 - E ^ 2
  hn : 1 ≤ n
  hj : 1 ≤ j
  hg1 : 1 ≤ F - E
  hgn : E ≤ (F - E) * n
  hr0 : 0 < E * M - F * n
  hB : E * n ≤ j * (F ^ 2 - E ^ 2)
  hC : E * n ≤ (M + j * F - s) * F
  hD : E ≤ (F - E) * (s - j * F)
  hks : j * F < s
  hst : s < M + j * F

theorem pos_core {E F M n j : ℝ} (hE : 0 < E) (hEF : E < F) (hBE : E < F ^ 2 - E ^ 2) (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hgn : E ≤ (F - E) * n) (hr0 : 0 < E * M - F * n) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < n ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M n ∧ 0 < E * (E * n) := by
  have hF : 0 < F := by linarith
  have hB : 0 < F ^ 2 - E ^ 2 := by linarith
  have hn0 : 0 < n := by linarith
  have hM : 0 < M := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg hE.le (neg_nonneg.2 h), mul_pos hF hn0]
  have h1 : E * (F + E) ≤ (F ^ 2 - E ^ 2) * n := by nlinarith [mul_le_mul_of_nonneg_left hgn (by linarith : (0 : ℝ) ≤ F + E)]
  have h2 : 0 < E * vv E F M n := by
    unfold vv; nlinarith [mul_pos hF hr0, mul_pos hE hE]
  have hv : 0 < vv E F M n := by
    by_contra hc; push_neg at hc; nlinarith [mul_nonneg hE.le (neg_nonneg.2 hc)]
  exact ⟨hF, hB, by linarith, hn0, hM, by linarith, hv, by positivity⟩

theorem RHU.pos {E F M n j : ℝ} (H : RHU E F M n j) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < n ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M n ∧ 0 < E * (E * n) :=
  pos_core H.hE H.hEF H.hBE H.hn H.hj H.hgn H.hr0

theorem RHR.pos {E F M n j s : ℝ} (H : RHR E F M n j s) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < n ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M n ∧ 0 < E * (E * n) :=
  pos_core H.hE H.hEF H.hBE H.hn H.hj H.hgn H.hr0

theorem RH2.toU {E F M n j s : ℝ} (H : RH2 E F M n j s) : RHU E F M n j :=
  ⟨H.hE, H.hEF, H.hBE, H.hn, H.hj, H.hg1, H.hgn, H.hr0, H.hrF⟩

theorem RH2.toR {E F M n j s : ℝ} (H : RH2 E F M n j s) : RHR E F M n j s :=
  ⟨H.hE, H.hEF, H.hBE, H.hn, H.hj, H.hg1, H.hgn, H.hr0, H.hB, H.hC, H.hD, H.hks, H.hst⟩

theorem RH2.pos {E F M n j s : ℝ} (H : RH2 E F M n j s) :
    0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 < E + F ∧ 0 < n ∧ 0 < M ∧ 0 ≤ j ∧ 0 < vv E F M n ∧ 0 < E * (E * n) := by
  obtain ⟨hE, hEF, hBE, hn, hj, hg1, hgn, hr0, hrF, -⟩ := H
  have hF : 0 < F := by linarith
  have hB : 0 < F ^ 2 - E ^ 2 := by linarith
  have hn0 : 0 < n := by linarith
  have hM : 0 < M := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg hE.le (neg_nonneg.2 h), mul_pos hF hn0]
  -- E v = B n + F rho - E^2 > 0
  have h1 : E * (F + E) ≤ (F ^ 2 - E ^ 2) * n := by nlinarith [mul_le_mul_of_nonneg_left hgn (by linarith : (0 : ℝ) ≤ F + E)]
  have h2 : 0 < E * vv E F M n := by
    unfold vv; nlinarith [mul_pos hF hr0, mul_pos hE hE]
  have hv : 0 < vv E F M n := by
    by_contra hc; push_neg at hc; nlinarith [mul_nonneg hE.le (neg_nonneg.2 hc)]
  exact ⟨hF, hB, by linarith, hn0, hM, by linarith, hv, by positivity⟩

/-- natural-number parameter set -/
structure NP2 where
  e : ℕ
  f : ℕ
  g : ℕ
  b : ℕ
  M : ℕ
  n : ℕ
  j : ℕ
  s : ℕ
  rho : ℕ
  he : 1 ≤ e
  hg : 1 ≤ g
  hfg : f = e + g
  hb : f * f = e * e + b
  hn : 1 ≤ n
  hgn : e ≤ g * n
  hrho : e * M = f * n + rho
  hr1 : 1 ≤ rho
  hrf : rho < f
  hj : 1 ≤ j
  hks : j * f < s
  hst : s < M + j * f
  hB : e * n ≤ j * b
  hC : e * n + s * f ≤ (M + j * f) * f
  hD : e + g * (j * f) ≤ g * s

namespace NP2
variable (P : NP2)

theorem hef : P.e < P.f := by have := P.hfg; have := P.hg; omega
theorem he0 : 0 < P.e := P.he
theorem hEF : (P.e : ℝ) < P.f := by exact_mod_cast P.hef
theorem hbR : (P.b : ℝ) = (P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2 := by
  have : ((P.f * P.f : ℕ) : ℝ) = ((P.e * P.e + P.b : ℕ) : ℝ) := by rw [P.hb]
  push_cast at this; nlinarith
theorem hgR : (P.g : ℝ) = (P.f : ℝ) - P.e := by
  have : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  linarith
theorem rhoR : (P.rho : ℝ) = P.e * P.M - P.f * P.n := by
  have : ((P.e * P.M : ℕ) : ℝ) = ((P.f * P.n + P.rho : ℕ) : ℝ) := by rw [P.hrho]
  push_cast at this; linarith

theorem rh : RH2 (P.e : ℝ) P.f P.M P.n P.j P.s := by
  have he : (1 : ℝ) ≤ P.e := by exact_mod_cast P.he
  have hg : (1 : ℝ) ≤ P.g := by exact_mod_cast P.hg
  have hn : (1 : ℝ) ≤ P.n := by exact_mod_cast P.hn
  have hj : (1 : ℝ) ≤ P.j := by exact_mod_cast P.hj
  have hfg : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  have hgn : (P.e : ℝ) ≤ P.g * P.n := by exact_mod_cast P.hgn
  have hr1 : (1 : ℝ) ≤ P.rho := by exact_mod_cast P.hr1
  have hrf : (P.rho : ℝ) < P.f := by exact_mod_cast P.hrf
  have hks : (P.j : ℝ) * P.f < P.s := by exact_mod_cast P.hks
  have hst : (P.s : ℝ) < P.M + P.j * P.f := by exact_mod_cast P.hst
  have hB : (P.e : ℝ) * P.n ≤ P.j * P.b := by exact_mod_cast P.hB
  have hC : (P.e : ℝ) * P.n + P.s * P.f ≤ (P.M + P.j * P.f) * P.f := by exact_mod_cast P.hC
  have hD : (P.e : ℝ) + P.g * (P.j * P.f) ≤ P.g * P.s := by exact_mod_cast P.hD
  have hbR := P.hbR
  have hgR := P.hgR
  have hrR := P.rhoR
  refine ⟨by linarith, by linarith, ?_, hn, hj, by linarith, ?_, by linarith, by linarith, ?_, ?_, ?_, hks, hst⟩
  · rw [← hbR]; nlinarith
  · rw [← hgR]; exact hgn
  · rw [← hbR]; exact hB
  · nlinarith
  · rw [← hgR]; nlinarith

end NP2

end

end Erdos634.Draft.ThetaNotch
