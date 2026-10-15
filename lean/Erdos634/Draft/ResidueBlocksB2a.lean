/-
Draft/ResidueBlocksB2a.lean -- generated file; do not edit by hand.

Residue seed of the member `(u, v)` at the scale `v + t` (see `Draft.ResidueBlocksDefs`): the linear bounds on the triangle `B2a` of block 2.
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
theorem B2a_N_uab_ge : ∀ q ∈ B2a t r e, (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) ≤ (-(t + r)) * q.1 + (t + r + e) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (-(t + r)) * (pQ0 t r e).1 + (t + r + e) * (pQ0 t r e).2 - (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : (-(t + r)) * (pE2 t r e).1 + (t + r + e) * (pE2 t r e).2 - (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (-(t + r)) * (pS t r e).1 + (t + r + e) * (pS t r e).2 - (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) = (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  unfold B2a
  refine hull_ge ((-(t + r))) ((t + r + e)) ((t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2a_Y_cut_le : ∀ q ∈ B2a t r e, 0 * q.1 + 1 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * t := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 2 * (t + r) * t - (0 * (pQ0 t r e).1 + 1 * (pQ0 t r e).2) = (t ^ 4 + 3 * t ^ 3 * r + 2 * t ^ 3 * e + 3 * t ^ 2 * r ^ 2 + 4 * t ^ 2 * r * e + t ^ 2 * e ^ 2 + t * r ^ 3 + 2 * t * r ^ 2 * e + t * r * e ^ 2) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (t ^ 4 + 3 * t ^ 3 * r + 2 * t ^ 3 * e + 3 * t ^ 2 * r ^ 2 + 4 * t ^ 2 * r * e + t ^ 2 * e ^ 2 + t * r ^ 3 + 2 * t * r ^ 2 * e + t * r * e ^ 2) := by positivity
  have k1 : (t + r + e) ^ 2 * (t + r) * t - (0 * (pE2 t r e).1 + 1 * (pE2 t r e).2) = (t ^ 6 + 5 * t ^ 5 * r + 4 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 16 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 24 * t ^ 3 * r ^ 2 * e + 18 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 16 * t ^ 2 * r ^ 3 * e + 18 * t ^ 2 * r ^ 2 * e ^ 2 + 8 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 5 + 4 * t * r ^ 4 * e + 6 * t * r ^ 3 * e ^ 2 + 4 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 4 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 16 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 24 * t ^ 3 * r ^ 2 * e + 18 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 16 * t ^ 2 * r ^ 3 * e + 18 * t ^ 2 * r ^ 2 * e ^ 2 + 8 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 5 + 4 * t * r ^ 4 * e + 6 * t * r ^ 3 * e ^ 2 + 4 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 2 * (t + r) * t - (0 * (pS t r e).1 + 1 * (pS t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2a
  refine hull_le (0) (1) ((t + r + e) ^ 2 * (t + r) * t) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2a_L_mvab_le : ∀ q ∈ B2a t r e, (t + r + e) * q.1 + (-(t + r)) * q.2 ≤ -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) * (pQ0 t r e).1 + (-(t + r)) * (pQ0 t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) * (pE2 t r e).1 + (-(t + r)) * (pE2 t r e).2) = (t ^ 5 + 4 * t ^ 4 * r + 2 * t ^ 4 * e + 6 * t ^ 3 * r ^ 2 + 6 * t ^ 3 * r * e + t ^ 3 * e ^ 2 + 4 * t ^ 2 * r ^ 3 + 6 * t ^ 2 * r ^ 2 * e + 2 * t ^ 2 * r * e ^ 2 + t * r ^ 4 + 2 * t * r ^ 3 * e + t * r ^ 2 * e ^ 2) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 5 + 4 * t ^ 4 * r + 2 * t ^ 4 * e + 6 * t ^ 3 * r ^ 2 + 6 * t ^ 3 * r * e + t ^ 3 * e ^ 2 + 4 * t ^ 2 * r ^ 3 + 6 * t ^ 2 * r ^ 2 * e + 2 * t ^ 2 * r * e ^ 2 + t * r ^ 4 + 2 * t * r ^ 3 * e + t * r ^ 2 * e ^ 2) := by positivity
  have k2 : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) * (pS t r e).1 + (-(t + r)) * (pS t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2a
  refine hull_le ((t + r + e)) ((-(t + r))) (-((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2a_N_abw_le : ∀ q ∈ B2a t r e, (-(t + r)) * q.1 + (t + r + e) * q.2 ≤ ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - ((-(t + r)) * (pQ0 t r e).1 + (t + r + e) * (pQ0 t r e).2) = (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  have k1 : ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - ((-(t + r)) * (pE2 t r e).1 + (t + r + e) * (pE2 t r e).2) = (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  have k2 : ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - ((-(t + r)) * (pS t r e).1 + (t + r + e) * (pS t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2a
  refine hull_le ((-(t + r))) ((t + r + e)) (((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2a_X_cum_le : ∀ q ∈ B2a t r e, 1 * q.1 + 0 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pQ0 t r e).1 + 0 * (pQ0 t r e).2) = (2 * t ^ 4 + 7 * t ^ 3 * r + 7 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 19 * t ^ 2 * r * e + 7 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 17 * t * r ^ 2 * e + 13 * t * r * e ^ 2 + 2 * t * e ^ 3 + r ^ 4 + 5 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 2 * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 4 + 7 * t ^ 3 * r + 7 * t ^ 3 * e + 9 * t ^ 2 * r ^ 2 + 19 * t ^ 2 * r * e + 7 * t ^ 2 * e ^ 2 + 5 * t * r ^ 3 + 17 * t * r ^ 2 * e + 13 * t * r * e ^ 2 + 2 * t * e ^ 3 + r ^ 4 + 5 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 2 * r * e ^ 3) := by positivity
  have k1 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pE2 t r e).1 + 0 * (pE2 t r e).2) = (t ^ 6 + 5 * t ^ 5 * r + 7 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 30 * t ^ 4 * r * e + 19 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 50 * t ^ 3 * r ^ 2 * e + 68 * t ^ 3 * r * e ^ 2 + 22 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 90 * t ^ 2 * r ^ 2 * e ^ 2 + 61 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + t * r ^ 5 + 15 * t * r ^ 4 * e + 52 * t * r ^ 3 * e ^ 2 + 56 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 7 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 30 * t ^ 4 * r * e + 19 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 50 * t ^ 3 * r ^ 2 * e + 68 * t ^ 3 * r * e ^ 2 + 22 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 90 * t ^ 2 * r ^ 2 * e ^ 2 + 61 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + t * r ^ 5 + 15 * t * r ^ 4 * e + 52 * t * r ^ 3 * e ^ 2 + 56 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pS t r e).1 + 0 * (pS t r e).2) = (t ^ 4 + 4 * t ^ 3 * r + 6 * t ^ 3 * e + 6 * t ^ 2 * r ^ 2 + 17 * t ^ 2 * r * e + 7 * t ^ 2 * e ^ 2 + 4 * t * r ^ 3 + 16 * t * r ^ 2 * e + 13 * t * r * e ^ 2 + 2 * t * e ^ 3 + r ^ 4 + 5 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 2 * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (t ^ 4 + 4 * t ^ 3 * r + 6 * t ^ 3 * e + 6 * t ^ 2 * r ^ 2 + 17 * t ^ 2 * r * e + 7 * t ^ 2 * e ^ 2 + 4 * t * r ^ 3 + 16 * t * r ^ 2 * e + 13 * t * r * e ^ 2 + 2 * t * e ^ 3 + r ^ 4 + 5 * r ^ 3 * e + 6 * r ^ 2 * e ^ 2 + 2 * r * e ^ 3) := by positivity
  unfold B2a
  refine hull_le (1) (0) ((t + r + e) ^ 2 * (t + r) * ((t + r + e) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2a_T_mabcm_ge : ∀ q ∈ B2a t r e, -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 3 * (pQ0 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pQ0 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 7 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 28 * t ^ 4 * r * e ^ 2 + 9 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 42 * t ^ 3 * r ^ 2 * e ^ 2 + 27 * t ^ 3 * r * e ^ 3 + 5 * t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 28 * t ^ 2 * r ^ 3 * e ^ 2 + 27 * t ^ 2 * r ^ 2 * e ^ 3 + 10 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 5 * e + 7 * t * r ^ 4 * e ^ 2 + 9 * t * r ^ 3 * e ^ 3 + 5 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 7 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 28 * t ^ 4 * r * e ^ 2 + 9 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 42 * t ^ 3 * r ^ 2 * e ^ 2 + 27 * t ^ 3 * r * e ^ 3 + 5 * t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 28 * t ^ 2 * r ^ 3 * e ^ 2 + 27 * t ^ 2 * r ^ 2 * e ^ 3 + 10 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 5 * e + 7 * t * r ^ 4 * e ^ 2 + 9 * t * r ^ 3 * e ^ 3 + 5 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by positivity
  have k1 : (t + r + e) ^ 3 * (pE2 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE2 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (4 * t ^ 6 * e ^ 3 + 20 * t ^ 5 * r * e ^ 3 + 12 * t ^ 5 * e ^ 4 + 40 * t ^ 4 * r ^ 2 * e ^ 3 + 48 * t ^ 4 * r * e ^ 4 + 13 * t ^ 4 * e ^ 5 + 40 * t ^ 3 * r ^ 3 * e ^ 3 + 72 * t ^ 3 * r ^ 2 * e ^ 4 + 39 * t ^ 3 * r * e ^ 5 + 6 * t ^ 3 * e ^ 6 + 20 * t ^ 2 * r ^ 4 * e ^ 3 + 48 * t ^ 2 * r ^ 3 * e ^ 4 + 39 * t ^ 2 * r ^ 2 * e ^ 5 + 12 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 5 * e ^ 3 + 12 * t * r ^ 4 * e ^ 4 + 13 * t * r ^ 3 * e ^ 5 + 6 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (4 * t ^ 6 * e ^ 3 + 20 * t ^ 5 * r * e ^ 3 + 12 * t ^ 5 * e ^ 4 + 40 * t ^ 4 * r ^ 2 * e ^ 3 + 48 * t ^ 4 * r * e ^ 4 + 13 * t ^ 4 * e ^ 5 + 40 * t ^ 3 * r ^ 3 * e ^ 3 + 72 * t ^ 3 * r ^ 2 * e ^ 4 + 39 * t ^ 3 * r * e ^ 5 + 6 * t ^ 3 * e ^ 6 + 20 * t ^ 2 * r ^ 4 * e ^ 3 + 48 * t ^ 2 * r ^ 3 * e ^ 4 + 39 * t ^ 2 * r ^ 2 * e ^ 5 + 12 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 5 * e ^ 3 + 12 * t * r ^ 4 * e ^ 4 + 13 * t * r ^ 3 * e ^ 5 + 6 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 3 * (pS t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pS t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by positivity
  unfold B2a
  refine hull_ge ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2a_T_l3s_ge : ∀ q ∈ B2a t r e, -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 3 * (pQ0 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pQ0 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) = (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 5 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 20 * t ^ 4 * r * e ^ 2 + 4 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 30 * t ^ 3 * r ^ 2 * e ^ 2 + 12 * t ^ 3 * r * e ^ 3 + t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 20 * t ^ 2 * r ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e ^ 3 + 2 * t ^ 2 * r * e ^ 4 + 2 * t * r ^ 5 * e + 5 * t * r ^ 4 * e ^ 2 + 4 * t * r ^ 3 * e ^ 3 + t * r ^ 2 * e ^ 4) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 5 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 20 * t ^ 4 * r * e ^ 2 + 4 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 30 * t ^ 3 * r ^ 2 * e ^ 2 + 12 * t ^ 3 * r * e ^ 3 + t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 20 * t ^ 2 * r ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e ^ 3 + 2 * t ^ 2 * r * e ^ 4 + 2 * t * r ^ 5 * e + 5 * t * r ^ 4 * e ^ 2 + 4 * t * r ^ 3 * e ^ 3 + t * r ^ 2 * e ^ 4) := by positivity
  have k1 : (t + r + e) ^ 3 * (pE2 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE2 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (t + r + e) ^ 3 * (pS t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pS t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2a
  refine hull_ge ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r)))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

end real

end Erdos634.Draft.Residue
