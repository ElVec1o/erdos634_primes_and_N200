/-
Draft/ResidueBlocksB1a.lean -- GENERATED FILE.  Do not edit by hand.

Residue seed of the member `(u, v)` at the scale `v + t` (see `Draft.ResidueBlocksDefs`): the linear bounds on the triangle `B1a` of block 1.
Each bound at a vertex is certified by a polynomial with nonnegative coefficients.

The construction is D. Paliy's, "unrestricted all-scale positive theorem for W and beta" (9 October 2026,
unrefereed).  No sorry, no native_decide.
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
theorem B1a_Y_zero_le : ∀ q ∈ B1a t r e, 0 * q.1 + 1 * q.2 ≤ 0 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : 0 - (0 * (pQ0 t r e).1 + 1 * (pQ0 t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : 0 - (0 * (pE1 t r e).1 + 1 * (pE1 t r e).2) = (t ^ 6 + 6 * t ^ 5 * r + 4 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 20 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 40 * t ^ 3 * r ^ 2 * e + 24 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 36 * t ^ 2 * r ^ 2 * e ^ 2 + 12 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 20 * t * r ^ 4 * e + 24 * t * r ^ 3 * e ^ 2 + 12 * t * r ^ 2 * e ^ 3 + 2 * t * r * e ^ 4 + r ^ 6 + 4 * r ^ 5 * e + 6 * r ^ 4 * e ^ 2 + 4 * r ^ 3 * e ^ 3 + r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 6 + 6 * t ^ 5 * r + 4 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 20 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 40 * t ^ 3 * r ^ 2 * e + 24 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 36 * t ^ 2 * r ^ 2 * e ^ 2 + 12 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 20 * t * r ^ 4 * e + 24 * t * r ^ 3 * e ^ 2 + 12 * t * r ^ 2 * e ^ 3 + 2 * t * r * e ^ 4 + r ^ 6 + 4 * r ^ 5 * e + 6 * r ^ 4 * e ^ 2 + 4 * r ^ 3 * e ^ 3 + r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : 0 - (0 * (((0 : ℝ), (0 : ℝ))).1 + 1 * (((0 : ℝ), (0 : ℝ))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B1a
  refine hull_le (0) (1) (0) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1a_N_uab_le : ∀ q ∈ B1a t r e, (-(t + r)) * q.1 + (t + r + e) * q.2 ≤ (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) - ((-(t + r)) * (pQ0 t r e).1 + (t + r + e) * (pQ0 t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) - ((-(t + r)) * (pE1 t r e).1 + (t + r + e) * (pE1 t r e).2) = (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by positivity
  have k2 : (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) - ((-(t + r)) * (((0 : ℝ), (0 : ℝ))).1 + (t + r + e) * (((0 : ℝ), (0 : ℝ))).2) = (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by positivity
  unfold B1a
  refine hull_le ((-(t + r))) ((t + r + e)) ((t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1a_N_zero_ge : ∀ q ∈ B1a t r e, 0 ≤ (-(t + r)) * q.1 + (t + r + e) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (-(t + r)) * (pQ0 t r e).1 + (t + r + e) * (pQ0 t r e).2 - 0 = (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by positivity
  have k1 : (-(t + r)) * (pE1 t r e).1 + (t + r + e) * (pE1 t r e).2 - 0 = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (-(t + r)) * (((0 : ℝ), (0 : ℝ))).1 + (t + r + e) * (((0 : ℝ), (0 : ℝ))).2 - 0 = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B1a
  refine hull_ge ((-(t + r))) ((t + r + e)) (0) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1a_X_cum_le : ∀ q ∈ B1a t r e, 1 * q.1 + 0 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pQ0 t r e).1 + 0 * (pQ0 t r e).2) = (2 * t ^ 4 + 7 * t ^ 3 * r + 7 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 19 * t ^ 2 * r * e + 7 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 17 * t * r ^ 2 * e + 13 * t * r * e ^ 2 + 2 * t * e ^ 3 + r ^ 4 + 5 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 2 * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 4 + 7 * t ^ 3 * r + 7 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 19 * t ^ 2 * r * e + 7 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 17 * t * r ^ 2 * e + 13 * t * r * e ^ 2 + 2 * t * e ^ 3 + r ^ 4 + 5 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 2 * r * e ^ 3) := by positivity
  have k1 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pE1 t r e).1 + 0 * (pE1 t r e).2) = (t ^ 6 + 6 * t ^ 5 * r + 9 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 43 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 82 * t ^ 3 * r ^ 2 * e + 83 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 78 * t ^ 2 * r ^ 3 * e + 117 * t ^ 2 * r ^ 2 * e ^ 2 + 65 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 37 * t * r ^ 4 * e + 73 * t * r ^ 3 * e ^ 2 + 61 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + r ^ 6 + 7 * r ^ 5 * e + 17 * r ^ 4 * e ^ 2 + 19 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 6 + 6 * t ^ 5 * r + 9 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 43 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 82 * t ^ 3 * r ^ 2 * e + 83 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 78 * t ^ 2 * r ^ 3 * e + 117 * t ^ 2 * r ^ 2 * e ^ 2 + 65 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 37 * t * r ^ 4 * e + 73 * t * r ^ 3 * e ^ 2 + 61 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + r ^ 6 + 7 * r ^ 5 * e + 17 * r ^ 4 * e ^ 2 + 19 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (((0 : ℝ), (0 : ℝ))).1 + 0 * (((0 : ℝ), (0 : ℝ))).2) = (2 * t ^ 4 + 7 * t ^ 3 * r + 5 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 13 * t ^ 2 * r * e + 4 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 11 * t * r ^ 2 * e + 7 * t * r * e ^ 2 + t * e ^ 3 + r ^ 4 + 3 * r ^ 3 * e + 3 * r ^ 2 * e ^ 2 + r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 4 + 7 * t ^ 3 * r + 5 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 13 * t ^ 2 * r * e + 4 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 11 * t * r ^ 2 * e + 7 * t * r * e ^ 2 + t * e ^ 3 + r ^ 4 + 3 * r ^ 3 * e + 3 * r ^ 2 * e ^ 2 + r * e ^ 3) := by positivity
  unfold B1a
  refine hull_le (1) (0) ((t + r + e) ^ 2 * (t + r) * ((t + r + e) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1a_T_mabcm_ge : ∀ q ∈ B1a t r e, -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 3 * (pQ0 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pQ0 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 7 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 28 * t ^ 4 * r * e ^ 2 + 9 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 42 * t ^ 3 * r ^ 2 * e ^ 2 + 27 * t ^ 3 * r * e ^ 3 + 5 * t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 28 * t ^ 2 * r ^ 3 * e ^ 2 + 27 * t ^ 2 * r ^ 2 * e ^ 3 + 10 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 5 * e + 7 * t * r ^ 4 * e ^ 2 + 9 * t * r ^ 3 * e ^ 3 + 5 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 7 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 28 * t ^ 4 * r * e ^ 2 + 9 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 42 * t ^ 3 * r ^ 2 * e ^ 2 + 27 * t ^ 3 * r * e ^ 3 + 5 * t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 28 * t ^ 2 * r ^ 3 * e ^ 2 + 27 * t ^ 2 * r ^ 2 * e ^ 3 + 10 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 5 * e + 7 * t * r ^ 4 * e ^ 2 + 9 * t * r ^ 3 * e ^ 3 + 5 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by positivity
  have k1 : (t + r + e) ^ 3 * (pE1 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE1 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 3 * (((0 : ℝ), (0 : ℝ))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (((0 : ℝ), (0 : ℝ))).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (4 * t ^ 6 * e + 22 * t ^ 5 * r * e + 16 * t ^ 5 * e ^ 2 + 50 * t ^ 4 * r ^ 2 * e + 73 * t ^ 4 * r * e ^ 2 + 25 * t ^ 4 * e ^ 3 + 60 * t ^ 3 * r ^ 3 * e + 132 * t ^ 3 * r ^ 2 * e ^ 2 + 91 * t ^ 3 * r * e ^ 3 + 19 * t ^ 3 * e ^ 4 + 40 * t ^ 2 * r ^ 4 * e + 118 * t ^ 2 * r ^ 3 * e ^ 2 + 123 * t ^ 2 * r ^ 2 * e ^ 3 + 52 * t ^ 2 * r * e ^ 4 + 7 * t ^ 2 * e ^ 5 + 14 * t * r ^ 5 * e + 52 * t * r ^ 4 * e ^ 2 + 73 * t * r ^ 3 * e ^ 3 + 47 * t * r ^ 2 * e ^ 4 + 13 * t * r * e ^ 5 + t * e ^ 6 + 2 * r ^ 6 * e + 9 * r ^ 5 * e ^ 2 + 16 * r ^ 4 * e ^ 3 + 14 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (4 * t ^ 6 * e + 22 * t ^ 5 * r * e + 16 * t ^ 5 * e ^ 2 + 50 * t ^ 4 * r ^ 2 * e + 73 * t ^ 4 * r * e ^ 2 + 25 * t ^ 4 * e ^ 3 + 60 * t ^ 3 * r ^ 3 * e + 132 * t ^ 3 * r ^ 2 * e ^ 2 + 91 * t ^ 3 * r * e ^ 3 + 19 * t ^ 3 * e ^ 4 + 40 * t ^ 2 * r ^ 4 * e + 118 * t ^ 2 * r ^ 3 * e ^ 2 + 123 * t ^ 2 * r ^ 2 * e ^ 3 + 52 * t ^ 2 * r * e ^ 4 + 7 * t ^ 2 * e ^ 5 + 14 * t * r ^ 5 * e + 52 * t * r ^ 4 * e ^ 2 + 73 * t * r ^ 3 * e ^ 3 + 47 * t * r ^ 2 * e ^ 4 + 13 * t * r * e ^ 5 + t * e ^ 6 + 2 * r ^ 6 * e + 9 * r ^ 5 * e ^ 2 + 16 * r ^ 4 * e ^ 3 + 14 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) := by positivity
  unfold B1a
  refine hull_ge ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1a_T_mv3ab_ge : ∀ q ∈ B1a t r e, -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 3 * (pQ0 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pQ0 t r e).2 - -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : (t + r + e) ^ 3 * (pE1 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE1 t r e).2 - -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (t + r + e) ^ 3 * (((0 : ℝ), (0 : ℝ))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (((0 : ℝ), (0 : ℝ))).2 - -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) = (2 * t ^ 6 * e + 12 * t ^ 5 * r * e + 9 * t ^ 5 * e ^ 2 + 30 * t ^ 4 * r ^ 2 * e + 45 * t ^ 4 * r * e ^ 2 + 16 * t ^ 4 * e ^ 3 + 40 * t ^ 3 * r ^ 3 * e + 90 * t ^ 3 * r ^ 2 * e ^ 2 + 64 * t ^ 3 * r * e ^ 3 + 14 * t ^ 3 * e ^ 4 + 30 * t ^ 2 * r ^ 4 * e + 90 * t ^ 2 * r ^ 3 * e ^ 2 + 96 * t ^ 2 * r ^ 2 * e ^ 3 + 42 * t ^ 2 * r * e ^ 4 + 6 * t ^ 2 * e ^ 5 + 12 * t * r ^ 5 * e + 45 * t * r ^ 4 * e ^ 2 + 64 * t * r ^ 3 * e ^ 3 + 42 * t * r ^ 2 * e ^ 4 + 12 * t * r * e ^ 5 + t * e ^ 6 + 2 * r ^ 6 * e + 9 * r ^ 5 * e ^ 2 + 16 * r ^ 4 * e ^ 3 + 14 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 6 * e + 12 * t ^ 5 * r * e + 9 * t ^ 5 * e ^ 2 + 30 * t ^ 4 * r ^ 2 * e + 45 * t ^ 4 * r * e ^ 2 + 16 * t ^ 4 * e ^ 3 + 40 * t ^ 3 * r ^ 3 * e + 90 * t ^ 3 * r ^ 2 * e ^ 2 + 64 * t ^ 3 * r * e ^ 3 + 14 * t ^ 3 * e ^ 4 + 30 * t ^ 2 * r ^ 4 * e + 90 * t ^ 2 * r ^ 3 * e ^ 2 + 96 * t ^ 2 * r ^ 2 * e ^ 3 + 42 * t ^ 2 * r * e ^ 4 + 6 * t ^ 2 * e ^ 5 + 12 * t * r ^ 5 * e + 45 * t * r ^ 4 * e ^ 2 + 64 * t * r ^ 3 * e ^ 3 + 42 * t * r ^ 2 * e ^ 4 + 12 * t * r * e ^ 5 + t * e ^ 6 + 2 * r ^ 6 * e + 9 * r ^ 5 * e ^ 2 + 16 * r ^ 4 * e ^ 3 + 14 * r ^ 3 * e ^ 4 + 6 * r ^ 2 * e ^ 5 + r * e ^ 6) := by positivity
  unfold B1a
  refine hull_ge ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

end real

end Erdos634.Draft.Residue
