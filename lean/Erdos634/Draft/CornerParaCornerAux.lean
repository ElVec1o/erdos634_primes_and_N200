/-
The corner chord, part 2 of 2: the hand-off of the corner chord to the chord-reflection stage.  The files below are not
imported, to keep the import cone small.

Adapted from:
  Draft/GLCCorner.lean                aux_reflection_2a tail: `clamps` + `exists_supporting (D.tile i) (j + 1)`
                                      -> CornerChord.clamp, CornerChord.line, corner_chord_clamps
  Draft/T30LPi3F6Corner.lean          Pi3F6.aux_reflection tail (same hand-off, pi/3)
Imported and applied:
  Draft/CornerParaCorner.lean         CornerChord, corner_chord_data
  Draft/CornerParaClamp.lean          clamps', side_pt_mem_frontier, far_edge_b, fin3_cover
  WallChain.lean                      Dissection.edge_point_not_interior, Dissection.mem_lineChain
  TileAt.lean                         congruentDissection_apex_counts (for corner_chord_iff)
-/
import Erdos634.Draft.CornerParaClamp
import Erdos634.Draft.CornerParaCorner

/-!
# The corner chord, part 2 of 2: companion lemmas of `CornerChord` and the packaged clamp data

Part 1 is `Draft/CornerParaCorner.lean` (the structure and `corner_chord_data`).  Adapts `GLCCorner` (γ = 2α) and
`T30LPi3F6Corner` (π/3) to the base-β tile.

Contents.
* `CornerChord.{ne_PQ, ne_PA, ne_QA}`, `chordEdge`, `edge_AP`, `edge_AQ` (the three edges of `T_A`), `range_pts`,
  `carrier_eq`, `A_mem_tile`, `P_mem_tile`, `Q_mem_tile`, `P_frontier`, `Q_frontier`, `sides_edge` (`P`, `Q` lie on the two
  distinct target sides at `A`), `sides_strict` (`r < 1` once `Q` is known not to be a target vertex);
* `CornerChord.wall` (the chord is a tile edge, hence a wall), `CornerChord.clamp` (`clamps'` applied to the
  barycentric data), `CornerChord.line` (the supporting line `φ ≤ c0` of `T_A` along its `b`-edge, with the near
  chain membership), and the packaged `corner_chord_clamps`, whose output plugs into `CornerParaClamp.far_edge_b`
  (checked by `corner_chord_far_edge`);
* `corner_chord_iff`: a corner chord exists at `k` iff the corner angle at `k` is `β` (so there is none at the apex:
  the field `angA` is load-bearing).

`corner_chord_data` / `corner_chord_clamps` / `corner_chord_far_edge` / `corner_chord_iff` are instantiated at the N = 44 tiling
`D44` (corners `0, 1`, and the apex `2` where there is no chord) by the modules `Draft/CornerParaWitnessAux`
(`D44_corner0_chord`, `D44_corner1_chord`) and `Draft/CornerParaWitness` (`D44_no_chord_at_apex`, which uses `corner_chord_iff`).
This also witnesses the hypotheses of `far_chain_single_b` / `far_edge_b` jointly at a real tiling.
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

/-! ## 1. Companion lemmas of `CornerChord` -/

namespace CornerChord

variable {N : ℕ} {D : CongruentDissection N} {α β γ : ℝ} {k : Fin 3} {iA : Fin N} {P Q : Plane}

/-- `P ≠ Q` (the chord is nondegenerate): its length is the model side `b > 0`. -/
theorem ne_PQ (hC : CornerChord D α β γ k iA P Q) : P ≠ Q := by
  intro h
  have h1 := hC.lenPQ
  rw [h, dist_self] at h1
  exact (sideOpp_pos' D.model 1).ne h1

/-- `P ≠ A`. -/
theorem ne_PA (hC : CornerChord D α β γ k iA P Q) : P ≠ D.target.pts k := by
  intro h
  have h1 := hC.lenAP
  rw [h, dist_self] at h1
  exact (sideOpp_pos' D.model 0).ne h1

/-- `Q ≠ A`. -/
theorem ne_QA (hC : CornerChord D α β γ k iA P Q) : Q ≠ D.target.pts k := by
  intro h
  have h1 := hC.lenAQ
  rw [h, dist_self] at h1
  exact (sideOpp_pos' D.model 2).ne h1

/-- **The chord is an edge of `T_A`** (its `b`-edge). -/
theorem chordEdge (hC : CornerChord D α β γ k iA P Q) :
    ∃ e : Fin 3, (D.tile iA).edge e = segment ℝ P Q := by
  obtain ⟨j, -, hvert⟩ := hC.vertex
  have e11 : j + 1 + 1 = j + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) j
  refine ⟨j + 1, ?_⟩
  rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · show segment ℝ ((D.tile iA).pts (j + 1)) ((D.tile iA).pts (j + 1 + 1)) = _
    rw [e11, hP, hQ]
  · show segment ℝ ((D.tile iA).pts (j + 1)) ((D.tile iA).pts (j + 1 + 1)) = _
    rw [e11, hP, hQ, segment_symm]

/-- The flank edge `[A, P]` of `T_A` (the `a`-edge) is an edge of the tile. -/
theorem edge_AP (hC : CornerChord D α β γ k iA P Q) :
    ∃ e : Fin 3, (D.tile iA).edge e = segment ℝ (D.target.pts k) P := by
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  rcases hvert with ⟨hP, -⟩ | ⟨hP, -⟩
  · obtain ⟨e, he⟩ := Tri.pair_eq_edge (D.tile iA) (p := j) (q := j + 1)
      ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)
    exact ⟨e, by rw [← he, hjA, hP]⟩
  · obtain ⟨e, he⟩ := Tri.pair_eq_edge (D.tile iA) (p := j) (q := j + 2)
      ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)
    exact ⟨e, by rw [← he, hjA, hP]⟩

/-- The flank edge `[A, Q]` of `T_A` (the `c`-edge) is an edge of the tile. -/
theorem edge_AQ (hC : CornerChord D α β γ k iA P Q) :
    ∃ e : Fin 3, (D.tile iA).edge e = segment ℝ (D.target.pts k) Q := by
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  rcases hvert with ⟨-, hQ⟩ | ⟨-, hQ⟩
  · obtain ⟨e, he⟩ := Tri.pair_eq_edge (D.tile iA) (p := j) (q := j + 2)
      ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)
    exact ⟨e, by rw [← he, hjA, hQ]⟩
  · obtain ⟨e, he⟩ := Tri.pair_eq_edge (D.tile iA) (p := j) (q := j + 1)
      ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)
    exact ⟨e, by rw [← he, hjA, hQ]⟩

/-- The vertex set of `T_A` is `{A, P, Q}`. -/
theorem range_pts (hC : CornerChord D α β γ k iA P Q) :
    Set.range (D.tile iA).pts = {D.target.pts k, P, Q} := by
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, rfl⟩
    rcases fin3_cover j m with rfl | rfl | rfl
    · exact Or.inl hjA.symm
    · rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · exact Or.inr (Or.inl hP.symm)
      · exact Or.inr (Or.inr hQ.symm)
    · rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · exact Or.inr (Or.inr hQ.symm)
      · exact Or.inr (Or.inl hP.symm)
  · rintro (h | h | h)
    · exact ⟨j, h ▸ hjA.symm⟩
    · rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · exact ⟨j + 1, h ▸ hP.symm⟩
      · exact ⟨j + 2, h ▸ hP.symm⟩
    · rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · exact ⟨j + 2, h ▸ hQ.symm⟩
      · exact ⟨j + 1, h ▸ hQ.symm⟩

/-- `T_A = hull {A, P, Q}`. -/
theorem carrier_eq (hC : CornerChord D α β γ k iA P Q) :
    (D.tile iA).carrier = convexHull ℝ {D.target.pts k, P, Q} := by
  show convexHull ℝ (Set.range (D.tile iA).pts) = _
  rw [hC.range_pts]

/-- `A ∈ T_A`. -/
theorem A_mem_tile (hC : CornerChord D α β γ k iA P Q) : D.target.pts k ∈ (D.tile iA).carrier := by
  rw [hC.carrier_eq]; exact subset_convexHull ℝ _ (by simp)

/-- `P ∈ T_A`. -/
theorem P_mem_tile (hC : CornerChord D α β γ k iA P Q) : P ∈ (D.tile iA).carrier := by
  rw [hC.carrier_eq]; exact subset_convexHull ℝ _ (by simp)

/-- `Q ∈ T_A`. -/
theorem Q_mem_tile (hC : CornerChord D α β γ k iA P Q) : Q ∈ (D.tile iA).carrier := by
  rw [hC.carrier_eq]; exact subset_convexHull ℝ _ (by simp)

/-- `P` lies in the frontier of the target (it is on a target side). -/
theorem P_frontier (hC : CornerChord D α β γ k iA P Q) : P ∈ frontier D.target.carrier := by
  obtain ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, hr1, hP, hQ⟩ := hC.sides
  rw [hP]
  exact side_pt_mem_frontier D.target hkw.symm hp0.le hp1.le

/-- `Q` lies in the frontier of the target (it is on a target side; possibly the far vertex). -/
theorem Q_frontier (hC : CornerChord D α β γ k iA P Q) : Q ∈ frontier D.target.carrier := by
  obtain ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, hr1, hP, hQ⟩ := hC.sides
  rw [hQ]
  exact side_pt_mem_frontier D.target hkz.symm hr0.le hr1

/-- **`P` and `Q` are on the two distinct target sides at `A`**, in the form of plan §2.2: the sides at `A` are
`D.target.edge k` (from `pts k` to `pts (k+1)`) and `D.target.edge (k+2)` (from `pts (k+2)` to `pts k`). -/
theorem sides_edge (hC : CornerChord D α β γ k iA P Q) :
    (P ∈ D.target.edge k ∧ Q ∈ D.target.edge (k + 2)) ∨
      (P ∈ D.target.edge (k + 2) ∧ Q ∈ D.target.edge k) := by
  obtain ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, hr1, hP, hQ⟩ := hC.sides
  have hmemP : (1 - p) • D.target.pts k + p • D.target.pts w ∈
      segment ℝ (D.target.pts k) (D.target.pts w) := ⟨1 - p, p, by linarith, hp0.le, by ring, rfl⟩
  have hmemQ : (1 - r) • D.target.pts k + r • D.target.pts z ∈
      segment ℝ (D.target.pts k) (D.target.pts z) := ⟨1 - r, r, by linarith, hr0.le, by ring, rfl⟩
  rw [← hP] at hmemP
  rw [← hQ] at hmemQ
  have hcases : ∀ k w z : Fin 3, w ≠ k → z ≠ k → w ≠ z →
      (w = k + 1 ∧ z = k + 2) ∨ (w = k + 2 ∧ z = k + 1) := by decide
  have e3 : k + 2 + 1 = k := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) k
  rcases hcases k w z hkw hkz hwz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    refine ⟨hmemP, ?_⟩
    show Q ∈ segment ℝ (D.target.pts (k + 2)) (D.target.pts (k + 2 + 1))
    rw [e3, segment_symm]; exact hmemQ
  · right
    refine ⟨?_, hmemQ⟩
    show P ∈ segment ℝ (D.target.pts (k + 2)) (D.target.pts (k + 2 + 1))
    rw [e3, segment_symm]; exact hmemP

/-- **`r < 1` once `Q` is known not to be a target vertex** (CP-3: the partner tile presents `γ` at `Q`): the barycentric
data of `sides` with `Q` strictly inside its side. -/
theorem sides_strict (hC : CornerChord D α β γ k iA P Q) (hQ : Q ∉ Set.range D.target.pts) :
    ∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧ ∃ p r : ℝ, 0 < p ∧ p < 1 ∧ 0 < r ∧ r < 1 ∧
      P = (1 - p) • D.target.pts k + p • D.target.pts w ∧
      Q = (1 - r) • D.target.pts k + r • D.target.pts z := by
  obtain ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, hr1, hP, hQ'⟩ := hC.sides
  refine ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, lt_of_le_of_ne hr1 ?_, hP, hQ'⟩
  rintro rfl
  exact hQ ⟨z, by rw [hQ']; simp⟩

/-! ## 2. B1 / B2: the chord is a wall, clamped by the two sides, on a supporting line of `T_A` -/

/-- **The chord is a wall**: it lies in an edge of `T_A`, so no tile interior meets its open segment
(`Dissection.edge_point_not_interior`). -/
theorem wall (hC : CornerChord D α β γ k iA P Q) :
    ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier := by
  obtain ⟨e, he⟩ := hC.chordEdge
  intro y hy
  have hy' : y ∈ (D.tile iA).edge e := by
    rw [he]; exact openSegment_subset_segment ℝ P Q hy
  exact D.toDissection.edge_point_not_interior hy'

/-- **B1: the clamps.**  The chord `[P, Q]` is clamped by the two target sides (`CornerParaClamp.clamps'` applied to the
barycentric data of `sides`): supporting functionals `g` of the target at `P` (the side of `P`) and `h` at `Q`, and the
open chord lies in the interior of the target. -/
theorem clamp (hC : CornerChord D α β γ k iA P Q) :
    (∃ (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ), (∀ y ∈ D.target.carrier, g y ≤ cg) ∧ g P = cg ∧ g Q < cg) ∧
    (∃ (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ), (∀ y ∈ D.target.carrier, h y ≤ ch) ∧ h Q = ch ∧ h P < ch) ∧
    openSegment ℝ P Q ⊆ interior D.target.carrier := by
  obtain ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, hr1, hP, hQ⟩ := hC.sides
  obtain ⟨⟨g, cg, hg, hgP, hgQ, -⟩, ⟨h, ch, hh, hhQ, hhP, -⟩, hint, -, -, -, -⟩ :=
    clamps' D.target k w z hkw.symm hkz.symm hwz hp0 hp1 hr0 hr1
  rw [hP, hQ]
  exact ⟨⟨g, cg, hg, hgP, hgQ⟩, ⟨h, ch, hh, hhQ, hhP⟩, hint⟩

/-- **B2: the line of the chord.**  The supporting functional of `T_A` along its `b`-edge: `T_A ⊆ {φ ≤ c0}`, `φ = c0`
on `P` and `Q`, `φ A < c0`.  So the FAR chain of the chord is `lineChain (-φ) (-c0)` (the convention of
`CornerParaClamp.far_edge_b`) and the NEAR chain `lineChain φ c0` contains `T_A`'s own chord edge. -/
theorem line (hC : CornerChord D α β γ k iA P Q) :
    ∃ (φ : Plane →ₗ[ℝ] ℝ) (c0 : ℝ) (eA : Fin 3), φ ≠ 0 ∧ (∀ x ∈ (D.tile iA).carrier, φ x ≤ c0) ∧
      φ P = c0 ∧ φ Q = c0 ∧ φ (D.target.pts k) < c0 ∧
      (D.tile iA).edge eA = segment ℝ P Q ∧ (iA, eA) ∈ D.lineChain φ c0 ∧
      dist ((D.tile iA).pts eA) ((D.tile iA).pts (eA + 1)) = dist P Q := by
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  obtain ⟨φ, c0, hφ, hle, h1, h2, h3⟩ := exists_supporting (D.tile iA) (j + 1)
  have e11 : j + 1 + 1 = j + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) j
  have e12 : j + 1 + 2 = j := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) j
  have h2' : φ ((D.tile iA).pts (j + 2)) = c0 := by rw [← e11]; exact h2
  have h3' : φ ((D.tile iA).pts j) < c0 := by rw [← e12]; exact h3
  have hmem : (iA, j + 1) ∈ D.lineChain φ c0 :=
    Dissection.mem_lineChain.mpr ⟨h1, h2, fun i => hle _ (subset_convexHull ℝ _ ⟨i, rfl⟩)⟩
  refine ⟨φ, c0, j + 1, hφ, hle, ?_, ?_, ?_, ?_, hmem, ?_⟩
  · rcases hvert with ⟨hP, -⟩ | ⟨hP, -⟩
    · rw [hP]; exact h1
    · rw [hP]; exact h2'
  · rcases hvert with ⟨-, hQ⟩ | ⟨-, hQ⟩
    · rw [hQ]; exact h2'
    · rw [hQ]; exact h1
  · rw [hjA]; exact h3'
  · rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · show segment ℝ ((D.tile iA).pts (j + 1)) ((D.tile iA).pts (j + 1 + 1)) = _
      rw [e11, hP, hQ]
    · show segment ℝ ((D.tile iA).pts (j + 1)) ((D.tile iA).pts (j + 1 + 1)) = _
      rw [e11, hP, hQ, segment_symm]
  · rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [e11, hP, hQ]
    · rw [e11, hP, hQ, dist_comm]

end CornerChord

/-! ## 3. The packaged clamp data (plugs into `CornerParaClamp.far_edge_b`) -/

/-- **B1 + B2 packaged** (plan §3, Steps B1/B2).  From a `CornerChord` we get, in one statement, everything
`CornerParaClamp.far_edge_b` / `chord_far_sum` need besides the model: the line of the chord (`φ`, `c0`, with `T_A` in
`{φ ≤ c0}`, `A` strictly below), the two clamps `g`, `h` of the target at `P`, `Q`, the open chord in the target
interior, and the wall property; plus the NEAR chain membership `(iA, eA) ∈ lineChain φ c0` with `eA` the chord edge
of `T_A`, and its length `= |PQ|`. -/
theorem corner_chord_clamps {N : ℕ} {D : CongruentDissection N} {α β γ : ℝ} {k : Fin 3} {iA : Fin N}
    {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    P ≠ Q ∧ ∃ (φ : Plane →ₗ[ℝ] ℝ) (c0 : ℝ) (eA : Fin 3) (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ)
        (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ),
      φ ≠ 0 ∧ (∀ x ∈ (D.tile iA).carrier, φ x ≤ c0) ∧ φ P = c0 ∧ φ Q = c0 ∧
      φ (D.target.pts k) < c0 ∧
      (D.tile iA).edge eA = segment ℝ P Q ∧ (iA, eA) ∈ D.lineChain φ c0 ∧
      dist ((D.tile iA).pts eA) ((D.tile iA).pts (eA + 1)) = dist P Q ∧
      (∀ y ∈ D.target.carrier, g y ≤ cg) ∧ g P = cg ∧ g Q < cg ∧
      (∀ y ∈ D.target.carrier, h y ≤ ch) ∧ h Q = ch ∧ h P < ch ∧
      openSegment ℝ P Q ⊆ interior D.target.carrier ∧
      (∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) := by
  obtain ⟨⟨g, cg, hg, hgP, hgQ⟩, ⟨h, ch, hh, hhQ, hhP⟩, hint⟩ := hC.clamp
  obtain ⟨φ, c0, eA, hφ, hle, hφP, hφQ, hφA, hedge, hmem, hlen⟩ := hC.line
  exact ⟨hC.ne_PQ, φ, c0, eA, g, cg, h, ch, hφ, hle, hφP, hφQ, hφA, hedge, hmem, hlen,
    hg, hgP, hgQ, hh, hhQ, hhP, hint, hC.wall⟩

/-- **The packaged clamp data plugs into `far_edge_b`** (B3 + B4 for the corner chord): the far chain of the corner
`b`-chord is ONE edge `e₀` and that edge is exactly `[P, Q]`.  (This is the interface check for CP-3: the output of
`corner_chord_clamps` is consumed by `CornerParaClamp.far_edge_b` with no re-derived geometry.) -/
theorem corner_chord_far_edge {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    ∃ (φ : Plane →ₗ[ℝ] ℝ) (c0 : ℝ), φ ≠ 0 ∧ (∀ x ∈ (D.tile iA).carrier, φ x ≤ c0) ∧
      φ P = c0 ∧ φ Q = c0 ∧ φ (D.target.pts k) < c0 ∧
      ∃ e₀ ∈ D.lineChain (-φ) (-c0), D.lineChain (-φ) (-c0) = {e₀} ∧
        (D.tile e₀.1).edge e₀.2 = segment ℝ P Q := by
  obtain ⟨hPQ, φ, c0, eA, g, cg, h, ch, hφ, hle, hφP, hφQ, hφA, -, -, -, hg, hgP, hgQ, hh, hhQ, hhP,
    hint, hwall⟩ := corner_chord_clamps hC
  exact ⟨φ, c0, hφ, hle, hφP, hφQ, hφA, far_edge_b hM hco he hef φ hφ c0 hPQ hφP hφQ g cg hg hgP hgQ
    h ch hh hhQ hhP hint hwall hC.lenPQ⟩

/-! ## 4. A corner chord exists exactly at a `β`-corner (no chord at the apex) -/

/-- **A corner chord exists at `k` iff the corner angle at `k` is `β`.**  (`←` is `corner_chord_data`; `→`: the field
`angA` says some tile presents `β` at `A`, and at a `3α`-corner no tile does,
`TileAt.congruentDissection_apex_counts`.)  So there is no `CornerChord` at the apex of a base-β target: the field `angA`
is load-bearing, and the structure is not satisfiable at every corner. -/
theorem corner_chord_iff {N : ℕ} (D : CongruentDissection N) {e f : ℕ} {s α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (k : Fin 3) :
    (∃ (iA : Fin N) (P Q : Plane), CornerChord D α β γ k iA P Q) ↔
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β := by
  refine ⟨?_, corner_chord_data D hco he hef hM hA hshape k⟩
  rintro ⟨iA, P, Q, hC⟩
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := angleFacts hA
  rcases hshape k with h3 | hb
  · exfalso
    obtain ⟨-, hc, -, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D α β γ hαβ hαγ
      hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' k h3
    have hmem : iA ∈ ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)) := by
      simpa using hC.angA
    exact Finset.card_ne_zero_of_mem hmem hc
  · exact hb

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.CornerChord.ne_PQ
#print axioms Erdos634.CornerPara.CornerChord.ne_PA
#print axioms Erdos634.CornerPara.CornerChord.ne_QA
#print axioms Erdos634.CornerPara.CornerChord.chordEdge
#print axioms Erdos634.CornerPara.CornerChord.edge_AP
#print axioms Erdos634.CornerPara.CornerChord.edge_AQ
#print axioms Erdos634.CornerPara.CornerChord.range_pts
#print axioms Erdos634.CornerPara.CornerChord.carrier_eq
#print axioms Erdos634.CornerPara.CornerChord.A_mem_tile
#print axioms Erdos634.CornerPara.CornerChord.P_mem_tile
#print axioms Erdos634.CornerPara.CornerChord.Q_mem_tile
#print axioms Erdos634.CornerPara.CornerChord.P_frontier
#print axioms Erdos634.CornerPara.CornerChord.Q_frontier
#print axioms Erdos634.CornerPara.CornerChord.sides_edge
#print axioms Erdos634.CornerPara.CornerChord.sides_strict
#print axioms Erdos634.CornerPara.CornerChord.wall
#print axioms Erdos634.CornerPara.CornerChord.clamp
#print axioms Erdos634.CornerPara.CornerChord.line
#print axioms Erdos634.CornerPara.corner_chord_clamps
#print axioms Erdos634.CornerPara.corner_chord_far_edge
#print axioms Erdos634.CornerPara.corner_chord_iff
