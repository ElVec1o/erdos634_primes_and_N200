/-
Draft/ResidueBlocksB3.lean -- generated file; do not edit by hand.

Residue seed of the member `(u, v)` at the scale `v + t` (see `Draft.ResidueBlocksDefs`): the linear bounds on block 3.
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
set_option maxHeartbeats 1000000 in
theorem B3_N_abw_ge : ∀ q ∈ B3 t r e, ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) ≤ (-(t + r)) * q.1 + (t + r + e) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (-(t + r)) * (pV t r e).1 + (t + r + e) * (pV t r e).2 - ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : (-(t + r)) * (pR0 t r e).1 + (t + r + e) * (pR0 t r e).2 - ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (-(t + r)) * (pC t r e).1 + (t + r + e) * (pC t r e).2 - ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) = (6 * t ^ 3 * e ^ 2 + 16 * t ^ 2 * r * e ^ 2 + 11 * t ^ 2 * e ^ 3 + 14 * t * r ^ 2 * e ^ 2 + 19 * t * r * e ^ 3 + 6 * t * e ^ 4 + 4 * r ^ 3 * e ^ 2 + 8 * r ^ 2 * e ^ 3 + 5 * r * e ^ 4 + e ^ 5) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (6 * t ^ 3 * e ^ 2 + 16 * t ^ 2 * r * e ^ 2 + 11 * t ^ 2 * e ^ 3 + 14 * t * r ^ 2 * e ^ 2 + 19 * t * r * e ^ 3 + 6 * t * e ^ 4 + 4 * r ^ 3 * e ^ 2 + 8 * r ^ 2 * e ^ 3 + 5 * r * e ^ 4 + e ^ 5) := by positivity
  unfold B3
  refine hull_ge ((-(t + r))) ((t + r + e)) (((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B3_L_zero_le : ∀ q ∈ B3 t r e, (t + r + e) * q.1 + (-(t + r)) * q.2 ≤ 0 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : 0 - ((t + r + e) * (pV t r e).1 + (-(t + r)) * (pV t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : 0 - ((t + r + e) * (pR0 t r e).1 + (-(t + r)) * (pR0 t r e).2) = (6 * t ^ 5 * e ^ 2 + 28 * t ^ 4 * r * e ^ 2 + 17 * t ^ 4 * e ^ 3 + 52 * t ^ 3 * r ^ 2 * e ^ 2 + 63 * t ^ 3 * r * e ^ 3 + 17 * t ^ 3 * e ^ 4 + 48 * t ^ 2 * r ^ 3 * e ^ 2 + 87 * t ^ 2 * r ^ 2 * e ^ 3 + 47 * t ^ 2 * r * e ^ 4 + 7 * t ^ 2 * e ^ 5 + 22 * t * r ^ 4 * e ^ 2 + 53 * t * r ^ 3 * e ^ 3 + 43 * t * r ^ 2 * e ^ 4 + 13 * t * r * e ^ 5 + t * e ^ 6 + 4 * r ^ 5 * e ^ 2 + 12 * r ^ 4 * e ^ 3 + 13 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (6 * t ^ 5 * e ^ 2 + 28 * t ^ 4 * r * e ^ 2 + 17 * t ^ 4 * e ^ 3 + 52 * t ^ 3 * r ^ 2 * e ^ 2 + 63 * t ^ 3 * r * e ^ 3 + 17 * t ^ 3 * e ^ 4 + 48 * t ^ 2 * r ^ 3 * e ^ 2 + 87 * t ^ 2 * r ^ 2 * e ^ 3 + 47 * t ^ 2 * r * e ^ 4 + 7 * t ^ 2 * e ^ 5 + 22 * t * r ^ 4 * e ^ 2 + 53 * t * r ^ 3 * e ^ 3 + 43 * t * r ^ 2 * e ^ 4 + 13 * t * r * e ^ 5 + t * e ^ 6 + 4 * r ^ 5 * e ^ 2 + 12 * r ^ 4 * e ^ 3 + 13 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : 0 - ((t + r + e) * (pC t r e).1 + (-(t + r)) * (pC t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B3
  refine hull_le ((t + r + e)) ((-(t + r))) (0) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B3_Y_zero_ge : ∀ q ∈ B3 t r e, 0 ≤ 0 * q.1 + 1 * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : 0 * (pV t r e).1 + 1 * (pV t r e).2 - 0 = (2 * t ^ 4 + 7 * t ^ 3 * r + 4 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 10 * t ^ 2 * r * e + 2 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 8 * t * r ^ 2 * e + 3 * t * r * e ^ 2 + r ^ 4 + 2 * r ^ 3 * e + r ^ 2 * e ^ 2) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 4 + 7 * t ^ 3 * r + 4 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 10 * t ^ 2 * r * e + 2 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 8 * t * r ^ 2 * e + 3 * t * r * e ^ 2 + r ^ 4 + 2 * r ^ 3 * e + r ^ 2 * e ^ 2) := by positivity
  have k1 : 0 * (pR0 t r e).1 + 1 * (pR0 t r e).2 - 0 = (t ^ 5 * e + 4 * t ^ 4 * r * e + 3 * t ^ 4 * e ^ 2 + 6 * t ^ 3 * r ^ 2 * e + 9 * t ^ 3 * r * e ^ 2 + 3 * t ^ 3 * e ^ 3 + 4 * t ^ 2 * r ^ 3 * e + 9 * t ^ 2 * r ^ 2 * e ^ 2 + 6 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 4 * e + 3 * t * r ^ 3 * e ^ 2 + 3 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 5 * e + 4 * t ^ 4 * r * e + 3 * t ^ 4 * e ^ 2 + 6 * t ^ 3 * r ^ 2 * e + 9 * t ^ 3 * r * e ^ 2 + 3 * t ^ 3 * e ^ 3 + 4 * t ^ 2 * r ^ 3 * e + 9 * t ^ 2 * r ^ 2 * e ^ 2 + 6 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 4 * e + 3 * t * r ^ 3 * e ^ 2 + 3 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : 0 * (pC t r e).1 + 1 * (pC t r e).2 - 0 = (2 * t ^ 4 + 7 * t ^ 3 * r + 7 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 18 * t ^ 2 * r * e + 9 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 15 * t * r ^ 2 * e + 15 * t * r * e ^ 2 + 5 * t * e ^ 3 + r ^ 4 + 4 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 4 * r * e ^ 3 + e ^ 4) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 4 + 7 * t ^ 3 * r + 7 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 18 * t ^ 2 * r * e + 9 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 15 * t * r ^ 2 * e + 15 * t * r * e ^ 2 + 5 * t * e ^ 3 + r ^ 4 + 4 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 4 * r * e ^ 3 + e ^ 4) := by positivity
  unfold B3
  refine hull_ge (0) (1) (0) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B3_X_cum_le : ∀ q ∈ B3 t r e, 1 * q.1 + 0 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pV t r e).1 + 0 * (pV t r e).2) = (3 * t ^ 3 * e + 8 * t ^ 2 * r * e + 4 * t ^ 2 * e ^ 2 + 7 * t * r ^ 2 * e + 7 * t * r * e ^ 2 + t * e ^ 3 + 2 * r ^ 3 * e + 3 * r ^ 2 * e ^ 2 + r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (3 * t ^ 3 * e + 8 * t ^ 2 * r * e + 4 * t ^ 2 * e ^ 2 + 7 * t * r ^ 2 * e + 7 * t * r * e ^ 2 + t * e ^ 3 + 2 * r ^ 3 * e + 3 * r ^ 2 * e ^ 2 + r * e ^ 3) := by positivity
  have k1 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pR0 t r e).1 + 0 * (pR0 t r e).2) = (3 * t ^ 5 * e + 14 * t ^ 4 * r * e + 16 * t ^ 4 * e ^ 2 + 26 * t ^ 3 * r ^ 2 * e + 59 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 24 * t ^ 2 * r ^ 3 * e + 81 * t ^ 2 * r ^ 2 * e ^ 2 + 63 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + 11 * t * r ^ 4 * e + 49 * t * r ^ 3 * e ^ 2 + 57 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (3 * t ^ 5 * e + 14 * t ^ 4 * r * e + 16 * t ^ 4 * e ^ 2 + 26 * t ^ 3 * r ^ 2 * e + 59 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 24 * t ^ 2 * r ^ 3 * e + 81 * t ^ 2 * r ^ 2 * e ^ 2 + 63 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + 11 * t * r ^ 4 * e + 49 * t * r ^ 3 * e ^ 2 + 57 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pC t r e).1 + 0 * (pC t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B3
  refine hull_le (1) (0) ((t + r + e) ^ 2 * (t + r) * ((t + r + e) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B3_T_mabcm_ge : ∀ q ∈ B3 t r e, -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 3 * (pV t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pV t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (6 * t ^ 5 * e ^ 2 + 28 * t ^ 4 * r * e ^ 2 + 17 * t ^ 4 * e ^ 3 + 52 * t ^ 3 * r ^ 2 * e ^ 2 + 63 * t ^ 3 * r * e ^ 3 + 17 * t ^ 3 * e ^ 4 + 48 * t ^ 2 * r ^ 3 * e ^ 2 + 87 * t ^ 2 * r ^ 2 * e ^ 3 + 47 * t ^ 2 * r * e ^ 4 + 7 * t ^ 2 * e ^ 5 + 22 * t * r ^ 4 * e ^ 2 + 53 * t * r ^ 3 * e ^ 3 + 43 * t * r ^ 2 * e ^ 4 + 13 * t * r * e ^ 5 + t * e ^ 6 + 4 * r ^ 5 * e ^ 2 + 12 * r ^ 4 * e ^ 3 + 13 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (6 * t ^ 5 * e ^ 2 + 28 * t ^ 4 * r * e ^ 2 + 17 * t ^ 4 * e ^ 3 + 52 * t ^ 3 * r ^ 2 * e ^ 2 + 63 * t ^ 3 * r * e ^ 3 + 17 * t ^ 3 * e ^ 4 + 48 * t ^ 2 * r ^ 3 * e ^ 2 + 87 * t ^ 2 * r ^ 2 * e ^ 3 + 47 * t ^ 2 * r * e ^ 4 + 7 * t ^ 2 * e ^ 5 + 22 * t * r ^ 4 * e ^ 2 + 53 * t * r ^ 3 * e ^ 3 + 43 * t * r ^ 2 * e ^ 4 + 13 * t * r * e ^ 5 + t * e ^ 6 + 4 * r ^ 5 * e ^ 2 + 12 * r ^ 4 * e ^ 3 + 13 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) := by positivity
  have k1 : (t + r + e) ^ 3 * (pR0 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pR0 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (t + r + e) ^ 3 * (pC t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pC t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B3
  refine hull_ge ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

end real

end Erdos634.Draft.Residue
