/-
Draft/ResidueBlocksB1b.lean -- generated file; do not edit by hand.

Residue seed of the member `(u, v)` at the scale `v + t` (see `Draft.ResidueBlocksDefs`): the linear bounds on the parallelogram `B1b` of block 1.
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
theorem B1b_Y_zero_le : ∀ q ∈ B1b t r e, 0 * q.1 + 1 * q.2 ≤ 0 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : 0 - (0 * (pE1 t r e).1 + 1 * (pE1 t r e).2) = (t ^ 6 + 6 * t ^ 5 * r + 4 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 20 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 40 * t ^ 3 * r ^ 2 * e + 24 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 36 * t ^ 2 * r ^ 2 * e ^ 2 + 12 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 20 * t * r ^ 4 * e + 24 * t * r ^ 3 * e ^ 2 + 12 * t * r ^ 2 * e ^ 3 + 2 * t * r * e ^ 4 + r ^ 6 + 4 * r ^ 5 * e + 6 * r ^ 4 * e ^ 2 + 4 * r ^ 3 * e ^ 3 + r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (t ^ 6 + 6 * t ^ 5 * r + 4 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 20 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 40 * t ^ 3 * r ^ 2 * e + 24 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 36 * t ^ 2 * r ^ 2 * e ^ 2 + 12 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 20 * t * r ^ 4 * e + 24 * t * r ^ 3 * e ^ 2 + 12 * t * r ^ 2 * e ^ 3 + 2 * t * r * e ^ 4 + r ^ 6 + 4 * r ^ 5 * e + 6 * r ^ 4 * e ^ 2 + 4 * r ^ 3 * e ^ 3 + r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e)) := by positivity
  have k1 : 0 - (0 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).1 + 1 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : 0 - (0 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).1 + 1 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).2) = (t ^ 6 + 5 * t ^ 5 * r + 3 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 12 * t ^ 4 * r * e + 3 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 18 * t ^ 3 * r ^ 2 * e + 9 * t ^ 3 * r * e ^ 2 + t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 12 * t ^ 2 * r ^ 3 * e + 9 * t ^ 2 * r ^ 2 * e ^ 2 + 2 * t ^ 2 * r * e ^ 3 + t * r ^ 5 + 3 * t * r ^ 4 * e + 3 * t * r ^ 3 * e ^ 2 + t * r ^ 2 * e ^ 3) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 3 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 12 * t ^ 4 * r * e + 3 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 18 * t ^ 3 * r ^ 2 * e + 9 * t ^ 3 * r * e ^ 2 + t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 12 * t ^ 2 * r ^ 3 * e + 9 * t ^ 2 * r ^ 2 * e ^ 2 + 2 * t ^ 2 * r * e ^ 3 + t * r ^ 5 + 3 * t * r ^ 4 * e + 3 * t * r ^ 3 * e ^ 2 + t * r ^ 2 * e ^ 3) / (e * (2 * t + 2 * r + e)) := by positivity
  have k3 : 0 - (0 * ((pE1 t r e + ((t + r) * t) • vE t r e)).1 + 1 * ((pE1 t r e + ((t + r) * t) • vE t r e)).2) = (2 * t ^ 6 + 11 * t ^ 5 * r + 7 * t ^ 5 * e + 25 * t ^ 4 * r ^ 2 + 32 * t ^ 4 * r * e + 9 * t ^ 4 * e ^ 2 + 30 * t ^ 3 * r ^ 3 + 58 * t ^ 3 * r ^ 2 * e + 33 * t ^ 3 * r * e ^ 2 + 5 * t ^ 3 * e ^ 3 + 20 * t ^ 2 * r ^ 4 + 52 * t ^ 2 * r ^ 3 * e + 45 * t ^ 2 * r ^ 2 * e ^ 2 + 14 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + 7 * t * r ^ 5 + 23 * t * r ^ 4 * e + 27 * t * r ^ 3 * e ^ 2 + 13 * t * r ^ 2 * e ^ 3 + 2 * t * r * e ^ 4 + r ^ 6 + 4 * r ^ 5 * e + 6 * r ^ 4 * e ^ 2 + 4 * r ^ 3 * e ^ 3 + r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (2 * t ^ 6 + 11 * t ^ 5 * r + 7 * t ^ 5 * e + 25 * t ^ 4 * r ^ 2 + 32 * t ^ 4 * r * e + 9 * t ^ 4 * e ^ 2 + 30 * t ^ 3 * r ^ 3 + 58 * t ^ 3 * r ^ 2 * e + 33 * t ^ 3 * r * e ^ 2 + 5 * t ^ 3 * e ^ 3 + 20 * t ^ 2 * r ^ 4 + 52 * t ^ 2 * r ^ 3 * e + 45 * t ^ 2 * r ^ 2 * e ^ 2 + 14 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + 7 * t * r ^ 5 + 23 * t * r ^ 4 * e + 27 * t * r ^ 3 * e ^ 2 + 13 * t * r ^ 2 * e ^ 3 + 2 * t * r * e ^ 4 + r ^ 6 + 4 * r ^ 5 * e + 6 * r ^ 4 * e ^ 2 + 4 * r ^ 3 * e ^ 3 + r ^ 2 * e ^ 4) / (e * (2 * t + 2 * r + e)) := by positivity
  unfold B1b Pg
  refine hull_le (0) (1) (0) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1b_N_uab_le : ∀ q ∈ B1b t r e, (-(t + r)) * q.1 + (t + r + e) * q.2 ≤ (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) - ((-(t + r)) * (pE1 t r e).1 + (t + r + e) * (pE1 t r e).2) = (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by positivity
  have k1 : (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) - ((-(t + r)) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).1 + (t + r + e) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) - ((-(t + r)) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).1 + (t + r + e) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  have k3 : (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) - ((-(t + r)) * ((pE1 t r e + ((t + r) * t) • vE t r e)).1 + (t + r + e) * ((pE1 t r e + ((t + r) * t) • vE t r e)).2) = (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by positivity
  unfold B1b Pg
  refine hull_le ((-(t + r))) ((t + r + e)) ((t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1b_N_zero_ge : ∀ q ∈ B1b t r e, 0 ≤ (-(t + r)) * q.1 + (t + r + e) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (-(t + r)) * (pE1 t r e).1 + (t + r + e) * (pE1 t r e).2 - 0 = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : (-(t + r)) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).1 + (t + r + e) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).2 - 0 = (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by positivity
  have k2 : (-(t + r)) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).1 + (t + r + e) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).2 - 0 = (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 8 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 12 * t ^ 2 * r ^ 2 * e + 9 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 8 * t * r ^ 3 * e + 9 * t * r ^ 2 * e ^ 2 + 2 * t * r * e ^ 3 + 2 * r ^ 4 * e + 3 * r ^ 3 * e ^ 2 + r ^ 2 * e ^ 3) := by positivity
  have k3 : (-(t + r)) * ((pE1 t r e + ((t + r) * t) • vE t r e)).1 + (t + r + e) * ((pE1 t r e + ((t + r) * t) • vE t r e)).2 - 0 = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (0) := by positivity
  unfold B1b Pg
  refine hull_ge ((-(t + r))) ((t + r + e)) (0) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1b_X_cum_le : ∀ q ∈ B1b t r e, 1 * q.1 + 0 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pE1 t r e).1 + 0 * (pE1 t r e).2) = (t ^ 6 + 6 * t ^ 5 * r + 9 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 43 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 82 * t ^ 3 * r ^ 2 * e + 83 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 78 * t ^ 2 * r ^ 3 * e + 117 * t ^ 2 * r ^ 2 * e ^ 2 + 65 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 37 * t * r ^ 4 * e + 73 * t * r ^ 3 * e ^ 2 + 61 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + r ^ 6 + 7 * r ^ 5 * e + 17 * r ^ 4 * e ^ 2 + 19 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (t ^ 6 + 6 * t ^ 5 * r + 9 * t ^ 5 * e + 15 * t ^ 4 * r ^ 2 + 43 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 3 + 82 * t ^ 3 * r ^ 2 * e + 83 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 15 * t ^ 2 * r ^ 4 + 78 * t ^ 2 * r ^ 3 * e + 117 * t ^ 2 * r ^ 2 * e ^ 2 + 65 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 6 * t * r ^ 5 + 37 * t * r ^ 4 * e + 73 * t * r ^ 3 * e ^ 2 + 61 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + r ^ 6 + 7 * r ^ 5 * e + 17 * r ^ 4 * e ^ 2 + 19 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k1 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).1 + 0 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).2) = (4 * t ^ 5 * e + 18 * t ^ 4 * r * e + 16 * t ^ 4 * e ^ 2 + 32 * t ^ 3 * r ^ 2 * e + 59 * t ^ 3 * r * e ^ 2 + 21 * t ^ 3 * e ^ 3 + 28 * t ^ 2 * r ^ 3 * e + 81 * t ^ 2 * r ^ 2 * e ^ 2 + 59 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 12 * t * r ^ 4 * e + 49 * t * r ^ 3 * e ^ 2 + 55 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (4 * t ^ 5 * e + 18 * t ^ 4 * r * e + 16 * t ^ 4 * e ^ 2 + 32 * t ^ 3 * r ^ 2 * e + 59 * t ^ 3 * r * e ^ 2 + 21 * t ^ 3 * e ^ 3 + 28 * t ^ 2 * r ^ 3 * e + 81 * t ^ 2 * r ^ 2 * e ^ 2 + 59 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 12 * t * r ^ 4 * e + 49 * t * r ^ 3 * e ^ 2 + 55 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).1 + 0 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).2) = (t ^ 6 + 5 * t ^ 5 * r + 8 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 34 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 56 * t ^ 3 * r ^ 2 * e + 77 * t ^ 3 * r * e ^ 2 + 25 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 44 * t ^ 2 * r ^ 3 * e + 99 * t ^ 2 * r ^ 2 * e ^ 2 + 67 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + t * r ^ 5 + 16 * t * r ^ 4 * e + 55 * t * r ^ 3 * e ^ 2 + 59 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 8 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 34 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 56 * t ^ 3 * r ^ 2 * e + 77 * t ^ 3 * r * e ^ 2 + 25 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 44 * t ^ 2 * r ^ 3 * e + 99 * t ^ 2 * r ^ 2 * e ^ 2 + 67 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + t * r ^ 5 + 16 * t * r ^ 4 * e + 55 * t * r ^ 3 * e ^ 2 + 59 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k3 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * ((pE1 t r e + ((t + r) * t) • vE t r e)).1 + 0 * ((pE1 t r e + ((t + r) * t) • vE t r e)).2) = (2 * t ^ 6 + 11 * t ^ 5 * r + 13 * t ^ 5 * e + 25 * t ^ 4 * r ^ 2 + 59 * t ^ 4 * r * e + 28 * t ^ 4 * e ^ 2 + 30 * t ^ 3 * r ^ 3 + 106 * t ^ 3 * r ^ 2 * e + 101 * t ^ 3 * r * e ^ 2 + 27 * t ^ 3 * e ^ 3 + 20 * t ^ 2 * r ^ 4 + 94 * t ^ 2 * r ^ 3 * e + 135 * t ^ 2 * r ^ 2 * e ^ 2 + 73 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + 7 * t * r ^ 5 + 41 * t * r ^ 4 * e + 79 * t * r ^ 3 * e ^ 2 + 65 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + r ^ 6 + 7 * r ^ 5 * e + 17 * r ^ 4 * e ^ 2 + 19 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (2 * t ^ 6 + 11 * t ^ 5 * r + 13 * t ^ 5 * e + 25 * t ^ 4 * r ^ 2 + 59 * t ^ 4 * r * e + 28 * t ^ 4 * e ^ 2 + 30 * t ^ 3 * r ^ 3 + 106 * t ^ 3 * r ^ 2 * e + 101 * t ^ 3 * r * e ^ 2 + 27 * t ^ 3 * e ^ 3 + 20 * t ^ 2 * r ^ 4 + 94 * t ^ 2 * r ^ 3 * e + 135 * t ^ 2 * r ^ 2 * e ^ 2 + 73 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + 7 * t * r ^ 5 + 41 * t * r ^ 4 * e + 79 * t * r ^ 3 * e ^ 2 + 65 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + r ^ 6 + 7 * r ^ 5 * e + 17 * r ^ 4 * e ^ 2 + 19 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  unfold B1b Pg
  refine hull_le (1) (0) ((t + r + e) ^ 2 * (t + r) * ((t + r + e) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1b_T_mabcm_ge : ∀ q ∈ B1b t r e, -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 3 * (pE1 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE1 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by positivity
  have k1 : (t + r + e) ^ 3 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 3 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  have k3 : (t + r + e) ^ 3 * ((pE1 t r e + ((t + r) * t) • vE t r e)).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE1 t r e + ((t + r) * t) • vE t r e)).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (0) := by positivity
  unfold B1b Pg
  refine hull_ge ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B1b_T_mv3ab_le : ∀ q ∈ B1b t r e, (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 ≤ -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) ^ 3 * (pE1 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE1 t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) ^ 3 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) ^ 3 * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE1 t r e + ((t + r) * (t + r + e)) • (vS t r e - vE t r e) + ((t + r) * t) • vE t r e)).2) = (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by positivity
  have k3 : -((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) ^ 3 * ((pE1 t r e + ((t + r) * t) • vE t r e)).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE1 t r e + ((t + r) * t) • vE t r e)).2) = (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (4 * t ^ 7 * e ^ 2 + 24 * t ^ 6 * r * e ^ 2 + 16 * t ^ 6 * e ^ 3 + 60 * t ^ 5 * r ^ 2 * e ^ 2 + 80 * t ^ 5 * r * e ^ 3 + 25 * t ^ 5 * e ^ 4 + 80 * t ^ 4 * r ^ 3 * e ^ 2 + 160 * t ^ 4 * r ^ 2 * e ^ 3 + 100 * t ^ 4 * r * e ^ 4 + 19 * t ^ 4 * e ^ 5 + 60 * t ^ 3 * r ^ 4 * e ^ 2 + 160 * t ^ 3 * r ^ 3 * e ^ 3 + 150 * t ^ 3 * r ^ 2 * e ^ 4 + 57 * t ^ 3 * r * e ^ 5 + 7 * t ^ 3 * e ^ 6 + 24 * t ^ 2 * r ^ 5 * e ^ 2 + 80 * t ^ 2 * r ^ 4 * e ^ 3 + 100 * t ^ 2 * r ^ 3 * e ^ 4 + 57 * t ^ 2 * r ^ 2 * e ^ 5 + 14 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 6 * e ^ 2 + 16 * t * r ^ 5 * e ^ 3 + 25 * t * r ^ 4 * e ^ 4 + 19 * t * r ^ 3 * e ^ 5 + 7 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by positivity
  unfold B1b Pg
  refine hull_le ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-((t + r + e) ^ 3 * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

end real

end Erdos634.Draft.Residue
