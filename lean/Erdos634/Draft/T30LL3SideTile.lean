import Mathlib.Tactic
import Erdos634.Draft.T30LL3Side

/-!
# The second tile on a side, with all its vertices and its angle at the far end of its side edge

`SideTileLen D X u x`: a tile with a `π/3` vertex at `X` and an edge along the ray `ℝ≥0 u` of length `x` (the one-length refinement of `SideTile`).
`side_tile_full`: if `‖u‖, ‖q‖` are `(a,b)` or `(b,a)`, `angle u q = π/3`, `g u = 0`, `g q < 0`, `g ≤ g X` on the target, and `SideTileLen D X u ‖u‖`, then there is a tile `K` with
`K.pts m = X + u` and `{K.pts (m+1), K.pts (m+2)} = {X, X + q}` (either order), and if `‖q‖ = b` (and `a ≠ b`) its local angle at `X + u` is `β`.
`openSegment_halves`, `pair_edge`: a chord of doubled length splits into the two tile edges.
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6

def SideTileLen {N : ℕ} (D : CongruentDissection N) (P u : Plane) (x : ℝ) : Prop :=
  ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = P ∧ (D.tile K).angleAt l = Real.pi / 3 ∧
    ((SameRay ℝ u ((D.tile K).pts (l + 1) - P) ∧ dist P ((D.tile K).pts (l + 1)) = x) ∨
      (SameRay ℝ u ((D.tile K).pts (l + 2) - P) ∧ dist P ((D.tile K).pts (l + 2)) = x))

theorem sideTile_of_len {N : ℕ} {D : CongruentDissection N} {P u : Plane} {a b x : ℝ}
    (h : SideTileLen D P u x) (hx : x = a ∨ x = b) : SideTile D P u a b := by
  obtain ⟨K, l, hl, hang, hc⟩ := h
  refine ⟨K, l, hl, hang, ?_⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, by rw [h2]; exact hx⟩
  · exact Or.inr ⟨h1, by rw [h2]; exact hx⟩

theorem side_tile_full {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b)
    {X u q : Plane} (hu : u ≠ 0) (hxy : (‖u‖ = a ∧ ‖q‖ = b) ∨ (‖u‖ = b ∧ ‖q‖ = a))
    (hangq : InnerProductGeometry.angle u q = Real.pi / 3)
    (g : Plane →ₗ[ℝ] ℝ) (hgu : g u = 0) (hgq : g q < 0)
    (hgmax : ∀ y ∈ D.target.carrier, g y ≤ g X) (hT : SideTileLen D X u ‖u‖) :
    ∃ (K : Fin N) (m : Fin 3), (D.tile K).pts m = X + u ∧
      (((D.tile K).pts (m + 1) = X ∧ (D.tile K).pts (m + 2) = X + q) ∨
        ((D.tile K).pts (m + 1) = X + q ∧ (D.tile K).pts (m + 2) = X)) ∧
      (‖q‖ = b → (D.tile K).localAngle (X + u) = 2 * Real.pi / 3 - α) := by
  obtain ⟨K, l, hl, hang, hcase⟩ := hT
  have hpair := pi3_edges_pair D hirr hS hac hbc K l hang
  rw [hl] at hpair
  have hmem : ∀ t : Fin 3, g ((D.tile K).pts t) ≤ g X := fun t =>
    hgmax _ (Erdos634.BaseSelection.tile_subset_target D.toDissection K (subset_convexHull ℝ _ ⟨t, rfl⟩))
  have hopp := opp_c_of_pi3 hirr (tile_sixty D hS K) l hang
  have hor := tri_two_orient (tile_sixty D hS K) hac hbc l hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  have hang_of : ∀ s : Fin 3, (D.tile K).localAngle ((D.tile K).pts s) = (D.tile K).angleAt s :=
    fun s => Tri.localAngle_vertex _ _
  rcases hcase with ⟨hray, hlen⟩ | ⟨hray, hlen⟩
  · -- the side edge is `l + 1`
    have hqt : dist X ((D.tile K).pts (l + 2)) = ‖q‖ := by
      rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hxy with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
        first | linarith | exact absurd (by linarith : a = b) hab
    obtain ⟨h1, h2⟩ := side_vertices (D.tile K) l (l + 1) (l + 2) (Or.inl ⟨rfl, rfl⟩) hang hl hu hray hlen hqt
      hangq g hgu hgq (hmem _)
    refine ⟨K, l + 1, h1, Or.inr ⟨by rw [e3, h2], by rw [e6, hl]⟩, ?_⟩
    intro hqb
    rw [← h1, hang_of]
    have hd : dist ((D.tile K).pts (l + 2)) ((D.tile K).pts l) = b := by
      rw [dist_comm, hl, hqt, hqb]
    rcases hor with ⟨o1, -, -, -⟩ | ⟨-, o2, -, -⟩
    · exact absurd (by rw [← o1, hd]) hab.symm
    · exact o2
  · -- the side edge is `l + 2`
    have hqt : dist X ((D.tile K).pts (l + 1)) = ‖q‖ := by
      rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hxy with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
        first | linarith | exact absurd (by linarith : a = b) hab
    obtain ⟨h1, h2⟩ := side_vertices (D.tile K) l (l + 2) (l + 1) (Or.inr ⟨rfl, rfl⟩) hang hl hu hray hlen hqt
      hangq g hgu hgq (hmem _)
    refine ⟨K, l + 2, h1, Or.inl ⟨by rw [e4, hl], by rw [e5, h2]⟩, ?_⟩
    intro hqb
    rw [← h1, hang_of]
    have hd : dist ((D.tile K).pts l) ((D.tile K).pts (l + 1)) = b := by
      rw [hl, hqt, hqb]
    rcases hor with ⟨-, -, o1, o2⟩ | ⟨-, -, o1, -⟩
    · exact o2
    · exact absurd (by rw [← o1, hd]) hab.symm

theorem openSegment_halves (P Q : Plane) :
    openSegment ℝ P Q ⊆ segment ℝ P (midpoint ℝ P Q) ∪ segment ℝ (midpoint ℝ P Q) Q := by
  intro y hy
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
  by_cases h : t ≤ 1 / 2
  · left
    refine ⟨s - t, 2 * t, by linarith, by linarith, by linarith, ?_⟩
    rw [midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module
  · right
    push_neg at h
    refine ⟨2 * s, t - s, by linarith, by linarith, by linarith, ?_⟩
    rw [midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module

theorem pair_edge (U : Tri) (a b : Fin 3) (hab : a ≠ b) :
    ∃ k : Fin 3, U.edge k = segment ℝ (U.pts a) (U.pts b) := by
  have h : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide
  rcases h a b hab with rfl | rfl
  · exact ⟨a, rfl⟩
  · exact ⟨b, by unfold Tri.edge; exact segment_symm ℝ _ _⟩

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.side_tile_full
#print axioms Erdos634.C2Forward.openSegment_halves
#print axioms Erdos634.C2Forward.pair_edge
