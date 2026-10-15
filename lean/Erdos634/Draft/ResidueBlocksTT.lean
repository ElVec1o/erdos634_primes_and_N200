/-
Draft/ResidueBlocksTT.lean -- generated file; do not edit by hand.

Residue seed of the member `(u, v)` at the scale `v + t` (see `Draft.ResidueBlocksDefs`): three inequalities put a point in the target `O A C`.
Each bound at a vertex is certified by a polynomial with nonnegative coefficients.

The construction is due to D. Paliy, "unrestricted all-scale positive theorem for W and beta" (2026, unrefereed).  No sorry, no native_decide.
-/
import Erdos634.Draft.ResidueBlocksDefs

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.Residue
open Erdos634.Draft.S2L (hull_le hull_ge mem_hull3')
open Erdos634.Draft.CollarE1 (Pg)

section real
variable {t r e : ℝ} (ht : 0 < t) (hr : 0 < r) (he : 0 < e)
include ht hr he
/-- a point with `X ≤ c u m`, `v Y − u X ≥ 0` and `v³ X − u Q Y ≥ −a b c m` lies in the target -/
theorem mem_TT (q : ℝ × ℝ) (h1 : 1 * q.1 + 0 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t))
    (h2 : 0 ≤ (-(t + r)) * q.1 + (t + r + e) * q.2)
    (h3 : -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2) : q ∈ TT t r e := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have hD : (0 : ℝ) < 4 * t ^ 7 * e + 26 * t ^ 6 * r * e + 28 * t ^ 6 * e ^ 2 + 72 * t ^ 5 * r ^ 2 * e + 155 * t ^ 5 * r * e ^ 2 + 69 * t ^ 5 * e ^ 3 + 110 * t ^ 4 * r ^ 3 * e + 355 * t ^ 4 * r ^ 2 * e ^ 2 + 317 * t ^ 4 * r * e ^ 3 + 82 * t ^ 4 * e ^ 4 + 100 * t ^ 3 * r ^ 4 * e + 430 * t ^ 3 * r ^ 3 * e ^ 2 + 578 * t ^ 3 * r ^ 2 * e ^ 3 + 301 * t ^ 3 * r * e ^ 4 + 51 * t ^ 3 * e ^ 5 + 54 * t ^ 2 * r ^ 5 * e + 290 * t ^ 2 * r ^ 4 * e ^ 2 + 522 * t ^ 2 * r ^ 3 * e ^ 3 + 411 * t ^ 2 * r ^ 2 * e ^ 4 + 141 * t ^ 2 * r * e ^ 5 + 16 * t ^ 2 * e ^ 6 + 16 * t * r ^ 6 * e + 103 * t * r ^ 5 * e ^ 2 + 233 * t * r ^ 4 * e ^ 3 + 247 * t * r ^ 3 * e ^ 4 + 129 * t * r ^ 2 * e ^ 5 + 30 * t * r * e ^ 6 + 2 * t * e ^ 7 + 2 * r ^ 7 * e + 15 * r ^ 6 * e ^ 2 + 41 * r ^ 5 * e ^ 3 + 55 * r ^ 4 * e ^ 4 + 39 * r ^ 3 * e ^ 5 + 14 * r ^ 2 * e ^ 6 + 2 * r * e ^ 7 := by positivity
  have hQ : (0 : ℝ) < t ^ 2 + 2 * t * r + 4 * t * e + r ^ 2 + 4 * r * e + 2 * e ^ 2 := by positivity
  have hBp : (0 : ℝ) < e * (2 * t + 2 * r + e) := by positivity
  have e1 : ((t + r + e) ^ 2 - (t + r) ^ 2) = e * (2 * t + 2 * r + e) := by ring
  have e2 : 2 * (t + r + e) ^ 2 - (t + r) ^ 2 = t ^ 2 + 2 * t * r + 4 * t * e + r ^ 2 + 4 * r * e + 2 * e ^ 2 := by ring
  unfold TT
  refine mem_hull3' (4 * t ^ 7 * e + 26 * t ^ 6 * r * e + 28 * t ^ 6 * e ^ 2 + 72 * t ^ 5 * r ^ 2 * e + 155 * t ^ 5 * r * e ^ 2 + 69 * t ^ 5 * e ^ 3 + 110 * t ^ 4 * r ^ 3 * e + 355 * t ^ 4 * r ^ 2 * e ^ 2 + 317 * t ^ 4 * r * e ^ 3 + 82 * t ^ 4 * e ^ 4 + 100 * t ^ 3 * r ^ 4 * e + 430 * t ^ 3 * r ^ 3 * e ^ 2 + 578 * t ^ 3 * r ^ 2 * e ^ 3 + 301 * t ^ 3 * r * e ^ 4 + 51 * t ^ 3 * e ^ 5 + 54 * t ^ 2 * r ^ 5 * e + 290 * t ^ 2 * r ^ 4 * e ^ 2 + 522 * t ^ 2 * r ^ 3 * e ^ 3 + 411 * t ^ 2 * r ^ 2 * e ^ 4 + 141 * t ^ 2 * r * e ^ 5 + 16 * t ^ 2 * e ^ 6 + 16 * t * r ^ 6 * e + 103 * t * r ^ 5 * e ^ 2 + 233 * t * r ^ 4 * e ^ 3 + 247 * t * r ^ 3 * e ^ 4 + 129 * t * r ^ 2 * e ^ 5 + 30 * t * r * e ^ 6 + 2 * t * e ^ 7 + 2 * r ^ 7 * e + 15 * r ^ 6 * e ^ 2 + 41 * r ^ 5 * e ^ 3 + 55 * r ^ 4 * e ^ 4 + 39 * r ^ 3 * e ^ 5 + 14 * r ^ 2 * e ^ 6 + 2 * r * e ^ 7) ((e * (2 * t + 2 * r + e)) ^ 2 * ((t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - q.1))
    ((t + r + e) * ((t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 - (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)))))
    ((t + r) * (t ^ 2 + 2 * t * r + 4 * t * e + r ^ 2 + 4 * r * e + 2 * e ^ 2) * ((-(t + r)) * q.1 + (t + r + e) * q.2)) hD
    (mul_nonneg (by positivity) (by linarith)) (mul_nonneg (by positivity) (by linarith))
    (mul_nonneg (by positivity) h2) ?_ q ?_ ?_
  · ring
  · simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  · simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring

end real

end Erdos634.Draft.Residue
