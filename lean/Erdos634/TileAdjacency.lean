import Erdos634.Dissection

/-!
# The tile-placement layer: the adjacent tile at an edge point

At a non-vertex point interior to the target, meeting some tile's edge, exactly two tiles meet it
(`Dissection.two_tiles_at_edge_point`).  This file extracts the second tile as a function,
`otherTile`, with its defining properties: it differs from `i`, it also has the point on its edge,
and `otherTile` is an involution.
-/

open Erdos634.Geometry Erdos634.Geometry.Dissection

namespace Erdos634.TileAdjacency

/-- **The unique other tile at an interior edge point.** At a point `x`, interior to the target,
not a vertex of any tile, where at least one tile meets `x` on the relative interior of an edge,
`Dissection.two_tiles_at_edge_point` says exactly two do. This extracts the *other* one, given
one of them. -/
theorem exists_unique_other_tile {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (i : Fin N) (hi : OnEdge D x i) :
    ∃! j : Fin N, j ≠ i ∧ OnEdge D x j := by
  classical
  have hEne : (Finset.univ.filter (fun k => OnEdge D x k)).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨hcard, -⟩ := D.two_tiles_at_edge_point hN hxv hR hRt hEne
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  have hi_mem : i ∈ ({a, b} : Finset (Fin N)) :=
    hset ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem
  rcases hi_mem with hia | hib
  · subst hia
    refine ⟨b, ⟨Ne.symm hab, ?_⟩, ?_⟩
    · have : b ∈ ({i, b} : Finset (Fin N)) := by simp
      have := hset ▸ this
      exact (Finset.mem_filter.mp this).2
    · rintro j ⟨hji, hjE⟩
      have hjmem : j ∈ ({i, b} : Finset (Fin N)) :=
        hset ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjE⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
      rcases hjmem with hji' | hjb
      · exact absurd hji' hji
      · exact hjb
  · subst hib
    refine ⟨a, ⟨hab, ?_⟩, ?_⟩
    · have : a ∈ ({a, i} : Finset (Fin N)) := by simp
      have := hset ▸ this
      exact (Finset.mem_filter.mp this).2
    · rintro j ⟨hji, hjE⟩
      have hjmem : j ∈ ({a, i} : Finset (Fin N)) :=
        hset ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjE⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
      rcases hjmem with hja | hji'
      · exact hja
      · exact absurd hji' hji

/-- **The adjacent tile, as a function.** Given a real witness ball and edge-point membership,
this picks out the other tile at `x` -- the dual-graph's edge map, at one point. -/
noncomputable def otherTile {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (i : Fin N) (hi : OnEdge D x i) : Fin N :=
  (exists_unique_other_tile D hN hxv hR hRt i hi).choose

theorem otherTile_ne {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (i : Fin N) (hi : OnEdge D x i) : otherTile D hN hxv hR hRt i hi ≠ i :=
  (exists_unique_other_tile D hN hxv hR hRt i hi).choose_spec.1.1

theorem otherTile_onEdge {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (i : Fin N) (hi : OnEdge D x i) : OnEdge D x (otherTile D hN hxv hR hRt i hi) :=
  (exists_unique_other_tile D hN hxv hR hRt i hi).choose_spec.1.2

theorem otherTile_otherTile {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (i : Fin N) (hi : OnEdge D x i) :
    otherTile D hN hxv hR hRt (otherTile D hN hxv hR hRt i hi) (otherTile_onEdge D hN hxv hR hRt i hi) = i := by
  have h1 := otherTile_ne D hN hxv hR hRt i hi
  have h2 := otherTile_onEdge D hN hxv hR hRt i hi
  have huniq := (exists_unique_other_tile D hN hxv hR hRt (otherTile D hN hxv hR hRt i hi) h2).choose_spec.2
  exact (huniq i ⟨Ne.symm h1, hi⟩).symm

end Erdos634.TileAdjacency
