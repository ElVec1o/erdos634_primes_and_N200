-- Draft/ThetaNotchNP.lean -- natural-number parameter set of the notch lemma (case rho = 0) and its real-level shadow.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchPR

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section

/-- **Parameters of the notch seed, case `rho = 0` (`e M = f n`, so `M = f m`, `n = e m`).**
Tile `(e f, b, f^2)`, `b = f^2 - e^2`, `g = f - e`, `k = j f`, `t = f (m + j)`.  The hypotheses are (a)-(d) of
`internal notes` 2.1 with (b), (c) STRICT (the hand theorem has `<=`; equality makes `Rh` pieces degenerate, not treated here):
 (b) `e n < j b`,  (c) `e n < (t - s) f` (stated as `e n + s f < t f`),  (d) `g (s - k) >= e` (stated additively), `k < s < t`. -/
structure NP where
  e : ℕ
  f : ℕ
  g : ℕ
  b : ℕ
  m : ℕ
  j : ℕ
  s : ℕ
  he : 1 ≤ e
  hg : 1 ≤ g
  hfg : f = e + g
  hb : f * f = e * e + b
  hm : 1 ≤ m
  hj : 1 ≤ j
  hks : j * f < s
  hst : s < f * (m + j)
  hB : e * (e * m) < j * b
  hC : e * (e * m) + s * f < f * (m + j) * f
  hD : e + g * (j * f) ≤ g * s

namespace NP
variable (P : NP)

/-- the real-level hypotheses follow -/
theorem rh : RH (P.e : ℝ) (P.f : ℝ) (P.m : ℝ) (P.j : ℝ) (P.s : ℝ) := by
  have he : (1 : ℝ) ≤ P.e := by exact_mod_cast P.he
  have hg : (1 : ℝ) ≤ P.g := by exact_mod_cast P.hg
  have hfg : (P.f : ℝ) = P.e + P.g := by exact_mod_cast P.hfg
  have hb : (P.f : ℝ) * P.f = P.e * P.e + P.b := by exact_mod_cast P.hb
  have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast P.hm
  have hj : (1 : ℝ) ≤ P.j := by exact_mod_cast P.hj
  have hks : (P.j : ℝ) * P.f < P.s := by exact_mod_cast P.hks
  have hst : (P.s : ℝ) < P.f * (P.m + P.j) := by exact_mod_cast P.hst
  have hB : (P.e : ℝ) * (P.e * P.m) < P.j * P.b := by exact_mod_cast P.hB
  have hC : (P.e : ℝ) * (P.e * P.m) + P.s * P.f < P.f * (P.m + P.j) * P.f := by exact_mod_cast P.hC
  have hD : (P.e : ℝ) + P.g * (P.j * P.f) ≤ P.g * P.s := by exact_mod_cast P.hD
  have hbR : (P.b : ℝ) = (P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2 := by nlinarith
  refine ⟨by linarith, by linarith, ?_, hm, hj, ?_, ?_, ?_, hks, hst, by linarith⟩
  · rw [← hbR]; nlinarith
  · rw [← hbR]; exact hB
  · nlinarith
  · nlinarith

end NP

end

end Erdos634.Draft.ThetaNotch
