/-
Draft/ResidueBlocksB2b.lean -- generated file; do not edit by hand.

Residue seed of the member `(u, v)` at the scale `v + t` (see `Draft.ResidueBlocksDefs`): the linear bounds on the parallelogram `B2b` of block 2.
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
theorem B2b_N_uab_ge : ∀ q ∈ B2b t r e, (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) ≤ (-(t + r)) * q.1 + (t + r + e) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (-(t + r)) * (pE2 t r e).1 + (t + r + e) * (pE2 t r e).2 - (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : (-(t + r)) * ((pE2 t r e + (e * t) • vE2 t r e)).1 + (t + r + e) * ((pE2 t r e + (e * t) • vE2 t r e)).2 - (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (-(t + r)) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (t + r + e) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2 - (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) = (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  have k3 : (-(t + r)) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (t + r + e) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2 - (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) = (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  unfold B2b Pg
  refine hull_ge ((-(t + r))) ((t + r + e)) ((t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2b_Y_cut_le : ∀ q ∈ B2b t r e, 0 * q.1 + 1 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * t := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 2 * (t + r) * t - (0 * (pE2 t r e).1 + 1 * (pE2 t r e).2) = (t ^ 6 + 5 * t ^ 5 * r + 4 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 16 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 24 * t ^ 3 * r ^ 2 * e + 18 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 16 * t ^ 2 * r ^ 3 * e + 18 * t ^ 2 * r ^ 2 * e ^ 2 + 8 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 5 + 4 * t * r ^ 4 * e + 6 * t * r ^ 3 * e ^ 2 + 4 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 4 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 16 * t ^ 4 * r * e + 6 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 24 * t ^ 3 * r ^ 2 * e + 18 * t ^ 3 * r * e ^ 2 + 4 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 16 * t ^ 2 * r ^ 3 * e + 18 * t ^ 2 * r ^ 2 * e ^ 2 + 8 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 5 + 4 * t * r ^ 4 * e + 6 * t * r ^ 3 * e ^ 2 + 4 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by positivity
  have k1 : (t + r + e) ^ 2 * (t + r) * t - (0 * ((pE2 t r e + (e * t) • vE2 t r e)).1 + 1 * ((pE2 t r e + (e * t) • vE2 t r e)).2) = (t ^ 6 + 5 * t ^ 5 * r + 5 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 20 * t ^ 4 * r * e + 8 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 30 * t ^ 3 * r ^ 2 * e + 24 * t ^ 3 * r * e ^ 2 + 5 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 20 * t ^ 2 * r ^ 3 * e + 24 * t ^ 2 * r ^ 2 * e ^ 2 + 10 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 5 + 5 * t * r ^ 4 * e + 8 * t * r ^ 3 * e ^ 2 + 5 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 5 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 20 * t ^ 4 * r * e + 8 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 30 * t ^ 3 * r ^ 2 * e + 24 * t ^ 3 * r * e ^ 2 + 5 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 20 * t ^ 2 * r ^ 3 * e + 24 * t ^ 2 * r ^ 2 * e ^ 2 + 10 * t ^ 2 * r * e ^ 3 + t ^ 2 * e ^ 4 + t * r ^ 5 + 5 * t * r ^ 4 * e + 8 * t * r ^ 3 * e ^ 2 + 5 * t * r ^ 2 * e ^ 3 + t * r * e ^ 4) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 2 * (t + r) * t - (0 * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + 1 * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (t ^ 5 * e + 4 * t ^ 4 * r * e + 2 * t ^ 4 * e ^ 2 + 6 * t ^ 3 * r ^ 2 * e + 6 * t ^ 3 * r * e ^ 2 + t ^ 3 * e ^ 3 + 4 * t ^ 2 * r ^ 3 * e + 6 * t ^ 2 * r ^ 2 * e ^ 2 + 2 * t ^ 2 * r * e ^ 3 + t * r ^ 4 * e + 2 * t * r ^ 3 * e ^ 2 + t * r ^ 2 * e ^ 3) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (t ^ 5 * e + 4 * t ^ 4 * r * e + 2 * t ^ 4 * e ^ 2 + 6 * t ^ 3 * r ^ 2 * e + 6 * t ^ 3 * r * e ^ 2 + t ^ 3 * e ^ 3 + 4 * t ^ 2 * r ^ 3 * e + 6 * t ^ 2 * r ^ 2 * e ^ 2 + 2 * t ^ 2 * r * e ^ 3 + t * r ^ 4 * e + 2 * t * r ^ 3 * e ^ 2 + t * r ^ 2 * e ^ 3) / (e * (2 * t + 2 * r + e)) := by positivity
  have k3 : (t + r + e) ^ 2 * (t + r) * t - (0 * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + 1 * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2b Pg
  refine hull_le (0) (1) ((t + r + e) ^ 2 * (t + r) * t) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2b_L_mvab_le : ∀ q ∈ B2b t r e, (t + r + e) * q.1 + (-(t + r)) * q.2 ≤ -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) * (pE2 t r e).1 + (-(t + r)) * (pE2 t r e).2) = (t ^ 5 + 4 * t ^ 4 * r + 2 * t ^ 4 * e + 6 * t ^ 3 * r ^ 2 + 6 * t ^ 3 * r * e + t ^ 3 * e ^ 2 + 4 * t ^ 2 * r ^ 3 + 6 * t ^ 2 * r ^ 2 * e + 2 * t ^ 2 * r * e ^ 2 + t * r ^ 4 + 2 * t * r ^ 3 * e + t * r ^ 2 * e ^ 2) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (t ^ 5 + 4 * t ^ 4 * r + 2 * t ^ 4 * e + 6 * t ^ 3 * r ^ 2 + 6 * t ^ 3 * r * e + t ^ 3 * e ^ 2 + 4 * t ^ 2 * r ^ 3 + 6 * t ^ 2 * r ^ 2 * e + 2 * t ^ 2 * r * e ^ 2 + t * r ^ 4 + 2 * t * r ^ 3 * e + t * r ^ 2 * e ^ 2) := by positivity
  have k1 : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) * ((pE2 t r e + (e * t) • vE2 t r e)).1 + (-(t + r)) * ((pE2 t r e + (e * t) • vE2 t r e)).2) = (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 7 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 28 * t ^ 4 * r * e ^ 2 + 9 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 42 * t ^ 3 * r ^ 2 * e ^ 2 + 27 * t ^ 3 * r * e ^ 3 + 5 * t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 28 * t ^ 2 * r ^ 3 * e ^ 2 + 27 * t ^ 2 * r ^ 2 * e ^ 3 + 10 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 5 * e + 7 * t * r ^ 4 * e ^ 2 + 9 * t * r ^ 3 * e ^ 3 + 5 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (2 * t ^ 6 * e + 10 * t ^ 5 * r * e + 7 * t ^ 5 * e ^ 2 + 20 * t ^ 4 * r ^ 2 * e + 28 * t ^ 4 * r * e ^ 2 + 9 * t ^ 4 * e ^ 3 + 20 * t ^ 3 * r ^ 3 * e + 42 * t ^ 3 * r ^ 2 * e ^ 2 + 27 * t ^ 3 * r * e ^ 3 + 5 * t ^ 3 * e ^ 4 + 10 * t ^ 2 * r ^ 4 * e + 28 * t ^ 2 * r ^ 3 * e ^ 2 + 27 * t ^ 2 * r ^ 2 * e ^ 3 + 10 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 5 * e + 7 * t * r ^ 4 * e ^ 2 + 9 * t * r ^ 3 * e ^ 3 + 5 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (-(t + r)) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (t ^ 4 * e + 3 * t ^ 3 * r * e + 2 * t ^ 3 * e ^ 2 + 3 * t ^ 2 * r ^ 2 * e + 4 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + t * r ^ 3 * e + 2 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (t ^ 4 * e + 3 * t ^ 3 * r * e + 2 * t ^ 3 * e ^ 2 + 3 * t ^ 2 * r ^ 2 * e + 4 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + t * r ^ 3 * e + 2 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  have k3 : -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) - ((t + r + e) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (-(t + r)) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2b Pg
  refine hull_le ((t + r + e)) ((-(t + r))) (-((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2b_N_abw_le : ∀ q ∈ B2b t r e, (-(t + r)) * q.1 + (t + r + e) * q.2 ≤ ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - ((-(t + r)) * (pE2 t r e).1 + (t + r + e) * (pE2 t r e).2) = (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  have k1 : ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - ((-(t + r)) * ((pE2 t r e + (e * t) • vE2 t r e)).1 + (t + r + e) * ((pE2 t r e + (e * t) • vE2 t r e)).2) = (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (2 * t ^ 4 * e + 6 * t ^ 3 * r * e + 3 * t ^ 3 * e ^ 2 + 6 * t ^ 2 * r ^ 2 * e + 6 * t ^ 2 * r * e ^ 2 + t ^ 2 * e ^ 3 + 2 * t * r ^ 3 * e + 3 * t * r ^ 2 * e ^ 2 + t * r * e ^ 3) := by positivity
  have k2 : ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - ((-(t + r)) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (t + r + e) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  have k3 : ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - ((-(t + r)) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (t + r + e) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2b Pg
  refine hull_le ((-(t + r))) ((t + r + e)) (((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2b_X_cum_le : ∀ q ∈ B2b t r e, 1 * q.1 + 0 * q.2 ≤ (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * (pE2 t r e).1 + 0 * (pE2 t r e).2) = (t ^ 6 + 5 * t ^ 5 * r + 7 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 30 * t ^ 4 * r * e + 19 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 50 * t ^ 3 * r ^ 2 * e + 68 * t ^ 3 * r * e ^ 2 + 22 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 90 * t ^ 2 * r ^ 2 * e ^ 2 + 61 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + t * r ^ 5 + 15 * t * r ^ 4 * e + 52 * t * r ^ 3 * e ^ 2 + 56 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 7 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 30 * t ^ 4 * r * e + 19 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 50 * t ^ 3 * r ^ 2 * e + 68 * t ^ 3 * r * e ^ 2 + 22 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 40 * t ^ 2 * r ^ 3 * e + 90 * t ^ 2 * r ^ 2 * e ^ 2 + 61 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + t * r ^ 5 + 15 * t * r ^ 4 * e + 52 * t * r ^ 3 * e ^ 2 + 56 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k1 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * ((pE2 t r e + (e * t) • vE2 t r e)).1 + 0 * ((pE2 t r e + (e * t) • vE2 t r e)).2) = (t ^ 6 + 5 * t ^ 5 * r + 8 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 34 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 56 * t ^ 3 * r ^ 2 * e + 77 * t ^ 3 * r * e ^ 2 + 25 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 44 * t ^ 2 * r ^ 3 * e + 99 * t ^ 2 * r ^ 2 * e ^ 2 + 67 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + t * r ^ 5 + 16 * t * r ^ 4 * e + 55 * t * r ^ 3 * e ^ 2 + 59 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (t ^ 6 + 5 * t ^ 5 * r + 8 * t ^ 5 * e + 10 * t ^ 4 * r ^ 2 + 34 * t ^ 4 * r * e + 22 * t ^ 4 * e ^ 2 + 10 * t ^ 3 * r ^ 3 + 56 * t ^ 3 * r ^ 2 * e + 77 * t ^ 3 * r * e ^ 2 + 25 * t ^ 3 * e ^ 3 + 5 * t ^ 2 * r ^ 4 + 44 * t ^ 2 * r ^ 3 * e + 99 * t ^ 2 * r ^ 2 * e ^ 2 + 67 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + t * r ^ 5 + 16 * t * r ^ 4 * e + 55 * t * r ^ 3 * e ^ 2 + 59 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k2 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + 0 * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (3 * t ^ 5 * e + 14 * t ^ 4 * r * e + 16 * t ^ 4 * e ^ 2 + 26 * t ^ 3 * r ^ 2 * e + 59 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 24 * t ^ 2 * r ^ 3 * e + 81 * t ^ 2 * r ^ 2 * e ^ 2 + 63 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + 11 * t * r ^ 4 * e + 49 * t * r ^ 3 * e ^ 2 + 57 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (3 * t ^ 5 * e + 14 * t ^ 4 * r * e + 16 * t ^ 4 * e ^ 2 + 26 * t ^ 3 * r ^ 2 * e + 59 * t ^ 3 * r * e ^ 2 + 23 * t ^ 3 * e ^ 3 + 24 * t ^ 2 * r ^ 3 * e + 81 * t ^ 2 * r ^ 2 * e ^ 2 + 63 * t ^ 2 * r * e ^ 3 + 12 * t ^ 2 * e ^ 4 + 11 * t * r ^ 4 * e + 49 * t * r ^ 3 * e ^ 2 + 57 * t * r ^ 2 * e ^ 3 + 22 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  have k3 : (t + r + e) ^ 2 * (t + r) * ((t + r + e) + t) - (1 * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + 0 * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (2 * t ^ 5 * e + 10 * t ^ 4 * r * e + 13 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 2 * e + 50 * t ^ 3 * r * e ^ 2 + 20 * t ^ 3 * e ^ 3 + 20 * t ^ 2 * r ^ 3 * e + 72 * t ^ 2 * r ^ 2 * e ^ 2 + 57 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 10 * t * r ^ 4 * e + 46 * t * r ^ 3 * e ^ 2 + 54 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (2 * t ^ 5 * e + 10 * t ^ 4 * r * e + 13 * t ^ 4 * e ^ 2 + 20 * t ^ 3 * r ^ 2 * e + 50 * t ^ 3 * r * e ^ 2 + 20 * t ^ 3 * e ^ 3 + 20 * t ^ 2 * r ^ 3 * e + 72 * t ^ 2 * r ^ 2 * e ^ 2 + 57 * t ^ 2 * r * e ^ 3 + 11 * t ^ 2 * e ^ 4 + 10 * t * r ^ 4 * e + 46 * t * r ^ 3 * e ^ 2 + 54 * t * r ^ 2 * e ^ 3 + 21 * t * r * e ^ 4 + 2 * t * e ^ 5 + 2 * r ^ 5 * e + 11 * r ^ 4 * e ^ 2 + 17 * r ^ 3 * e ^ 3 + 10 * r ^ 2 * e ^ 4 + 2 * r * e ^ 5) / (e * (2 * t + 2 * r + e)) := by positivity
  unfold B2b Pg
  refine hull_le (1) (0) ((t + r + e) ^ 2 * (t + r) * ((t + r + e) + t)) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2b_T_mabcm_ge : ∀ q ∈ B2b t r e, -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) ≤ (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : (t + r + e) ^ 3 * (pE2 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE2 t r e).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (4 * t ^ 6 * e ^ 3 + 20 * t ^ 5 * r * e ^ 3 + 12 * t ^ 5 * e ^ 4 + 40 * t ^ 4 * r ^ 2 * e ^ 3 + 48 * t ^ 4 * r * e ^ 4 + 13 * t ^ 4 * e ^ 5 + 40 * t ^ 3 * r ^ 3 * e ^ 3 + 72 * t ^ 3 * r ^ 2 * e ^ 4 + 39 * t ^ 3 * r * e ^ 5 + 6 * t ^ 3 * e ^ 6 + 20 * t ^ 2 * r ^ 4 * e ^ 3 + 48 * t ^ 2 * r ^ 3 * e ^ 4 + 39 * t ^ 2 * r ^ 2 * e ^ 5 + 12 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 5 * e ^ 3 + 12 * t * r ^ 4 * e ^ 4 + 13 * t * r ^ 3 * e ^ 5 + 6 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (4 * t ^ 6 * e ^ 3 + 20 * t ^ 5 * r * e ^ 3 + 12 * t ^ 5 * e ^ 4 + 40 * t ^ 4 * r ^ 2 * e ^ 3 + 48 * t ^ 4 * r * e ^ 4 + 13 * t ^ 4 * e ^ 5 + 40 * t ^ 3 * r ^ 3 * e ^ 3 + 72 * t ^ 3 * r ^ 2 * e ^ 4 + 39 * t ^ 3 * r * e ^ 5 + 6 * t ^ 3 * e ^ 6 + 20 * t ^ 2 * r ^ 4 * e ^ 3 + 48 * t ^ 2 * r ^ 3 * e ^ 4 + 39 * t ^ 2 * r ^ 2 * e ^ 5 + 12 * t ^ 2 * r * e ^ 6 + t ^ 2 * e ^ 7 + 4 * t * r ^ 5 * e ^ 3 + 12 * t * r ^ 4 * e ^ 4 + 13 * t * r ^ 3 * e ^ 5 + 6 * t * r ^ 2 * e ^ 6 + t * r * e ^ 7) / (e * (2 * t + 2 * r + e)) := by positivity
  have k1 : (t + r + e) ^ 3 * ((pE2 t r e + (e * t) • vE2 t r e)).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE2 t r e + (e * t) • vE2 t r e)).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (0) := by positivity
  have k2 : (t + r + e) ^ 3 * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (0) := by positivity
  have k3 : (t + r + e) ^ 3 * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2 - -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t)) = (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by positivity
  unfold B2b Pg
  refine hull_ge ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) ^ 2 * ((t + r + e) + t))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
theorem B2b_T_l3s_le : ∀ q ∈ B2b t r e, (t + r + e) ^ 3 * q.1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * q.2 ≤ -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) := by
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have k0 : -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) - ((t + r + e) ^ 3 * (pE2 t r e).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * (pE2 t r e).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n0 : (0 : ℝ) ≤ (0) := by positivity
  have k1 : -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) - ((t + r + e) ^ 3 * ((pE2 t r e + (e * t) • vE2 t r e)).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE2 t r e + (e * t) • vE2 t r e)).2) = (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n1 : (0 : ℝ) ≤ (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by positivity
  have k2 : -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) - ((t + r + e) ^ 3 * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE2 t r e + (e * t) • vE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n2 : (0 : ℝ) ≤ (2 * t ^ 5 * e ^ 2 + 8 * t ^ 4 * r * e ^ 2 + 5 * t ^ 4 * e ^ 3 + 12 * t ^ 3 * r ^ 2 * e ^ 2 + 15 * t ^ 3 * r * e ^ 3 + 4 * t ^ 3 * e ^ 4 + 8 * t ^ 2 * r ^ 3 * e ^ 2 + 15 * t ^ 2 * r ^ 2 * e ^ 3 + 8 * t ^ 2 * r * e ^ 4 + t ^ 2 * e ^ 5 + 2 * t * r ^ 4 * e ^ 2 + 5 * t * r ^ 3 * e ^ 3 + 4 * t * r ^ 2 * e ^ 4 + t * r * e ^ 5) := by positivity
  have k3 : -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r))) - ((t + r + e) ^ 3 * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).1 + (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) * ((pE2 t r e + ((t + r) * t) • (vS2 t r e - vE2 t r e))).2) = (0) := by
    simp only [pQ0, pS, pP0, pR0, pV, pO, pA, pC, pE1, pE2, vS, vE, vS2, vE2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have n3 : (0 : ℝ) ≤ (0) := by positivity
  unfold B2b Pg
  refine hull_le ((t + r + e) ^ 3) ((-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2)))) (-(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * (t + r + e) * ((t + r + e) ^ 2 + t * (t + r)))) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith

end real

end Erdos634.Draft.Residue
