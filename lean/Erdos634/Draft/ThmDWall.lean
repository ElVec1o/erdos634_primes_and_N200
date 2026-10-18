import Mathlib.Tactic
import Erdos634.Draft.ThmDHalfNear
import Erdos634.WallChain
import Erdos634.RunPartition

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4), layer 1: a straight point covered on one side by a single tile  

`WestCover D Φ P` : there is a tile `tC` whose interior contains every point `y` of a small ball around `P` with `Φ y < Φ P`, and
`tC` lies in `Φ ≤ Φ P`.  This is the "wall" hypothesis of Lemma 33' for an interior start: the ray `UP` continues beyond `P` as a
wall because `P` is interior to an edge of a tile on its west side.  It replaces `west_outside` (west of `P` is outside the target)
of the corner case.

* `east_vertex`   : a tile with a vertex at `P` lies in `Φ ≥ Φ P`;
* `no_straddle`   : no tile edge meets `]P', P[` for `P'` close to `P` on the west side (the clamp used by `next_tile`, `run_partition`).
-/

open scoped Classical
open Metric
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.RunPartition Set

variable {N : ℕ}

theorem lineMap_lin (F : Plane →ₗ[ℝ] ℝ) (p q : Plane) (t : ℝ) :
    F (AffineMap.lineMap p q t) = F p + t * (F q - F p) := by
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul]
  ring

/-- tile edges are walls -/
theorem seg_wall' (D : Dissection N) {t : Fin N} {k m : Fin 3} (hkm : k ≠ m) {y : Plane}
    (hy : y ∈ segment ℝ ((D.tile t).pts k) ((D.tile t).pts m)) :
    ∀ i, y ∉ interior (D.tile i).carrier := by
  obtain ⟨k₀, hk₀⟩ := (D.tile t).pair_eq_edge hkm
  intro i
  exact D.edge_point_not_interior (j := t) (k := k₀) (by rw [← hk₀]; exact hy) i

/-- the west side of `P` near `P` is covered by the interior of one tile lying west of the line -/
def WestCover (D : Dissection N) (Φ : Plane →ₗ[ℝ] ℝ) (P : Plane) : Prop :=
  ∃ (tC : Fin N) (δ : ℝ), 0 < δ ∧
    (∀ y, dist y P < δ → Φ y < Φ P → y ∈ interior (D.tile tC).carrier) ∧
    (∀ y ∈ (D.tile tC).carrier, Φ y ≤ Φ P)

/-- a tile with a vertex at `P` lies on the east side -/
theorem WestCover.east_vertex {D : Dissection N} {Φ : Plane →ₗ[ℝ] ℝ} {P : Plane} (h : WestCover D Φ P)
    {τ : Fin N} {k : Fin 3} (hk : (D.tile τ).pts k = P) (i : Fin 3) : Φ P ≤ Φ ((D.tile τ).pts i) := by
  obtain ⟨tC, δ, hδ, hcov, -⟩ := h
  by_contra hlt
  push_neg at hlt
  set R := (D.tile τ).pts i with hR
  have hik : i ≠ k := by
    rintro rfl; rw [hk] at hR; rw [hR] at hlt; exact lt_irrefl _ hlt
  have hdpos : 0 < dist R P := by
    rw [dist_pos]; intro hRP; rw [hRP] at hlt; exact lt_irrefl _ hlt
  set d := dist R P with hd
  set s : ℝ := min 1 (δ / (2 * d)) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos hδ (by positivity))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsd : s * d < δ := by
    have h1 : s ≤ δ / (2 * d) := min_le_right _ _
    have h2 : s * d ≤ δ / (2 * d) * d := mul_le_mul_of_nonneg_right h1 hdpos.le
    have h3 : δ / (2 * d) * d = δ / 2 := by field_simp
    linarith
  set y : Plane := AffineMap.lineMap P R s with hy
  have hdy : dist y P = s * d := by
    rw [hy, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hs0, dist_comm]
  have hΦy : Φ y < Φ P := by
    rw [hy, lineMap_lin]
    nlinarith
  have hint := hcov y (by rw [hdy]; exact hsd) hΦy
  have hseg : y ∈ segment ℝ ((D.tile τ).pts k) ((D.tile τ).pts i) := by
    rw [hk, segment_eq_image_lineMap]
    exact ⟨s, ⟨hs0.le, hs1⟩, rfl⟩
  exact seg_wall' D hik.symm hseg _ hint


/-- the clamp: no tile edge meets `]P', P[` for `P'` close to `P` on the west side -/
theorem WestCover.no_straddle {D : Dissection N} {Φ : Plane →ₗ[ℝ] ℝ} {P : Plane} (h : WestCover D Φ P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (P' Q : Plane), dist P' P < δ → Φ P' < Φ P →
      ∀ (i : Fin N) (k : Fin 3), ¬ Straddles ((D.tile i).edge k) P' P Q := by
  obtain ⟨tC, δ, hδ, hcov, -⟩ := h
  refine ⟨δ, hδ, fun P' Q hd hΦ i k => ?_⟩
  rintro ⟨⟨y, hyE, hyP⟩, -⟩
  rw [openSegment_eq_image_lineMap] at hyP
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hyP
  have hΦy : Φ (AffineMap.lineMap P' P τ) < Φ P := by
    rw [lineMap_lin]; nlinarith
  have hdy : dist (AffineMap.lineMap P' P τ) P < δ := by
    rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith [dist_nonneg (x := P') (y := P)]
  exact D.edge_point_not_interior hyE tC (hcov _ hdy hΦy)

#print axioms WestCover.east_vertex
#print axioms WestCover.no_straddle
end Erdos634.Draft.ThmDRun
