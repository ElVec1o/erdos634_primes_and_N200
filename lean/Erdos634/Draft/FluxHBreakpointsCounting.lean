import Erdos634.Dissection
import Erdos634.EdgeChain
import Erdos634.WallChain
import Erdos634.LineParam
import Erdos634.Draft.FluxHBreakpointsInjectivity
import Erdos634.EdgeWordConversion

/-!
# The counting sub-part of the breakpoint bijection

Closing row 14's `F4` (and, by the same shape, row 15's remaining leaves, row 4's L7/L8, row 3's item 3)
needs a **counting** fact: tying `EdgeWordConversion.side_walk_congruent`'s word `(P,Q,R)` — an
*unordered* multiplicity triple, `P+Q+R ≤ 3N`, no positional data — to
`Draft.FluxHBreakpointsInjectivity.nondegenerateTraceChain`'s *cardinality* (the object the
pointwise breakpoint-classification machinery in `FluxHBreakpoints*` indexes).

## What this file does

**Proved** (`target_side_lineChain_eq_nondegenerate`, `target_side_word_card_eq`): for a *target
side* wall (the case F4/row14 needs, and the case `Draft.FluxHBreakpointsFrontier`'s capstone
restricts to), the finset underlying `EdgeWordConversion.side_walk_congruent`'s word
equation is **literally the same finset**, up to a proved extensional equality, as
`nondegenerateTraceChain D f c u v`. Consequently the word's multiplicity sum is **exactly**, not
merely `≤ 3N`, the cardinality of `nondegenerateTraceChain`, which by
`nondegenerateTraceChain_orderedChain_length` is exactly the length of the *sorted,
one-entry-per-edge* chain that the breakpoint machinery classifies.

**Not proved.** Turning "the chain has `n = P+Q+R` edges" into "so `n_a + n_b
≤ n − 1`, hence `n_c ≥ 1`" (F4's pigeonhole) needs two further, separate facts, *neither* of which
this file builds, and *neither* of which is a corollary of the equality above:

1. **A count of interior breakpoints in terms of chain length.** An ordered chain of `n` edges
   (`Contiguity.orderedChain`, sorted by `edgeParam`'s left endpoint) has `n − 1` *adjacent pairs*;
   this is elementary list combinatorics, not proved in the corpus for `orderedChain` specifically,
   and it is not the hard part.
2. **Every `a`- or `b`-type edge has a `γ` at (at least) one of its own two endpoints.** This is
   the geometric content of Beeson's argument. Nothing in
   `Draft.FluxHBreakpointsPoint`/`FluxHBreakpointsFrontier` (pointwise classification *given* a
   breakpoint) or `EdgeWordConversion` (word existence, no per-edge angle data) produces a function
   from "this side's `a`/`b`-edges" to "an endpoint where a `γ`-tile sits".
   `Draft.FluxFRow14Derive`'s header names exactly this as the missing third ingredient (its
   "row14_F4... NOT CLOSED" paragraph); the three breakpoint files classify a breakpoint's angle
   multiset *given that it is one*, and never assert that an edge has one.

Fact 2 is the genuine obstruction, not a bridging exercise: it is a per-tile-type geometric claim
("an `a`-edge cannot have both its endpoints γ-free") that would need its own proof from the tile's
angle relations (`3α+2β=π`, `γ=2α+β`) and the tiling's local vertex-figure constraints — the
kind of argument `TileAt.congruentDissection_boundary_figure_cases` classifies *after* the fact but
never asserts must happen. Without it, an injection {edges}→{breakpoints} cannot be built: an
`a`-edge could in principle touch two `α`/`β`-only breakpoints and never touch a `γ`, in which case
no counting argument of this shape forces `n_c ≥ 1` at all. It needs a new geometric theorem about
the tile's own vertex figure along a straight side, comparable in scope to `TileAt.lean`'s existing
`congruentDissection_boundary_figure_cases` development.

`Row14.row14_rational`'s hypothesis list is **unchanged**: `hF4` is not discharged. What is new is the
identification of the word-count with the chain length, which is pure counting with no per-edge angle
content; Fact 2 is the entire remaining obstruction.

Axiom-clean; no `sorry` (standard axioms only).
-/

namespace Erdos634.Draft.FluxHBreakpointsCounting

open Erdos634.Geometry Erdos634.Geometry.Dissection
open Erdos634.Contiguity Erdos634.LineParam
open Erdos634.Draft.FluxHBreakpointsInjectivity
open Erdos634.EdgeWordConversion
open Set

open scoped Classical

variable {N : ℕ}

/-! ## Step 1: the target-side chain, described as a filter on "edge fully contains in the side"

Exactly the finset `hasEdgeChains_edge`/`side_partition`/`side_walk_abc` build internally
(`Dissection.lean:753-754`), but re-derived here as an explicit extensional equality against
`D.lineChain f c`, which is the finset the breakpoint machinery (`nondegenerateTraceChain`, a
filter of `D.lineChain f c`) actually indexes. Neither existing file states this equality; it is
genuinely new (though every step is a one-line composition of already-proved facts). -/

/-- **A target-side chain edge is entirely contained in that side.** For the supporting `(f, c)` of
target side `i` (`exists_supporting`), every `D.lineChain f c` edge lies inside
`segment (target i) (target (i+1))`, not merely on its line. -/
theorem lineChain_edge_subset_side (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  rw [← target_contact_side D.target f c hle hi hi1 hi2]
  intro y hy
  exact ⟨tile_subset_target D e.1 (Tri.edge_subset_carrier _ e.2 hy),
    D.lineChain_edge_subset he y hy⟩

/-- **Conversely, an edge contained in a target side is a chain edge of its supporting line.** The
other half of the extensional equality: `edge ⊆ S` forces both `mem_lineChain`-fields, using that
`S`'s own points satisfy `f = c` (`target_contact_side`) and every tile is inside the target
(`tile_subset_target`, `hle`). -/
theorem side_subset_edge_mem_lineChain (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) {e : Fin N × Fin 3}
    (hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1))) :
    e ∈ D.lineChain f c := by
  have hS : segment ℝ (D.target.pts i) (D.target.pts (i + 1))
      ⊆ {x | x ∈ D.target.carrier ∧ f x = c} := by
    rw [← target_contact_side D.target f c hle hi hi1 hi2]
  have hA : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 := left_mem_segment ℝ _ _
  have hB : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).edge e.2 := right_mem_segment ℝ _ _
  have hfA := (hS (hsub hA)).2
  have hfB := (hS (hsub hB)).2
  refine Dissection.mem_lineChain.mpr ⟨hfA, hfB, fun k => ?_⟩
  have hptsk : (D.tile e.1).pts k ∈ (D.tile e.1).carrier :=
    Tri.edge_subset_carrier _ k (left_mem_segment ℝ _ _)
  exact hle _ (tile_subset_target D e.1 hptsk)

/-- **The extensional equality.** `D.lineChain f c` is exactly the finset of edges contained in
target side `i`, for the side's own supporting `(f, c)`. -/
theorem target_side_lineChain_eq_filter (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) :
    D.lineChain f c = Finset.univ.filter
      (fun e : Fin N × Fin 3 => (D.tile e.1).edge e.2
        ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1))) := by
  classical
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨lineChain_edge_subset_side D f c hle hi hi1 hi2,
    side_subset_edge_mem_lineChain D f c hle hi hi1 hi2⟩

/-! ## Step 2: every target-side chain edge has a nondegenerate trace

A chain edge on a target side is *entirely* contained in the wall segment (Step 1), and its two
endpoints are always distinct (`Tri.indep`), so its trace with the wall is the whole edge — never a
single point. This puts every `D.lineChain f c` edge into `nondegenerateTraceChain`, closing the
"empty/degenerate trace" concern `FluxHBreakpointsInjectivity.lean`'s header raises, for exactly the
case (a target side) that concern turns out never to bite in. -/

/-- **A target-side chain edge's endpoints are distinct.** Immediate from `Tri.indep`
(`edge_succ_ne`, `EdgeWordConversion.lean:56-57`, reused here). -/
theorem tile_edge_endpoints_ne (T : Erdos634.Geometry.Tri) (k : Fin 3) :
    T.pts k ≠ T.pts (k + 1) := by
  intro h
  exact Erdos634.EdgeWordConversion.edge_succ_ne k (T.indep.injective h)

/-- **Every target-side chain edge lies in `nondegenerateTraceChain`.** The trace with the wall is
the whole edge (Step 1), which has positive length (distinct endpoints), so `edgeParam`'s two
coordinates cannot coincide: coinciding would force the trace's Hausdorff measure to be `0`, but it
equals the edge's own positive length. -/
theorem target_side_lineChain_subset_nondegenerate (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ)
    (hf : f ≠ 0) (c : ℝ) (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    e ∈ nondegenerateTraceChain D f c (D.target.pts i) (D.target.pts (i + 1)) := by
  set u := D.target.pts i
  set v := D.target.pts (i + 1)
  have huv : u ≠ v := tile_edge_endpoints_ne D.target i
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ u v :=
    lineChain_edge_subset_side D f c hle hi hi1 hi2 he
  have hinter : (D.tile e.1).edge e.2 ∩ segment ℝ u v = (D.tile e.1).edge e.2 :=
    Set.inter_eq_left.mpr hsub
  have hne : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) :=
    tile_edge_endpoints_ne (D.tile e.1) e.2
  have hdpos : 0 < dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := dist_pos.mpr hne
  have hmeasedge : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      ((D.tile e.1).edge e.2) = ENNReal.ofReal
        (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) := by
    rw [Tri.hausdorff_edge, edist_dist]
  rw [mem_nondegenerateTraceChain_iff]
  refine ⟨he, ?_⟩
  by_contra hcon
  push_neg at hcon
  rcases edgeParam_spec D f hf c u v huv he hi hi1 with ⟨hempty, -⟩ | ⟨-, -, heqtr, hmeastr⟩
  · rw [hinter] at hempty
    have : (D.tile e.1).pts e.2 ∈ (∅ : Set Plane) :=
      hempty ▸ left_mem_segment ℝ _ _
    exact absurd this (Set.notMem_empty _)
  · have hle' : max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
        ≤ min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 := hcon
    have heq0 : max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
        = min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 :=
      le_antisymm hle' min_le_max
    rw [hinter] at hmeastr
    rw [hmeasedge] at hmeastr
    have habs : |(edgeParam D f c u v e).1 - (edgeParam D f c u v e).2| = 0 := by
      have h0 : |(edgeParam D f c u v e).1 - (edgeParam D f c u v e).2|
          = max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
            - min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 := by
        rcases le_total (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 with h | h
        · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
        · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
      rw [h0, heq0, sub_self]
    rw [habs, zero_mul] at hmeastr
    have hdne : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ 0 := hdpos.ne'
    exact hdne (by
      have := (ENNReal.ofReal_eq_ofReal_iff le_rfl (le_of_lt hdpos)).mp hmeastr.symm
      linarith [this])

/-- **The equality.** For a target side's supporting `(f, c)`, `D.lineChain f c` and
`nondegenerateTraceChain D f c u v` coincide exactly — the "empty/degenerate trace" filter that
distinguishes them in general (`FluxHBreakpointsInjectivity`'s header) removes nothing here. -/
theorem target_side_lineChain_eq_nondegenerate (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ)
    (hf : f ≠ 0) (c : ℝ) (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) :
    D.lineChain f c = nondegenerateTraceChain D f c (D.target.pts i) (D.target.pts (i + 1)) := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    exact target_side_lineChain_subset_nondegenerate D f hf c hle hi hi1 hi2 he
  · intro e he
    exact (mem_nondegenerateTraceChain_iff D f c _ _).mp he |>.1

/-! ## Step 3: the word count is exactly `D.lineChain f c`'s cardinality

Re-derives `hasEdgeChains_edge`'s cover argument (`Dissection.lean:745-792`) and
`Dissection.side_walk`'s length identity (`EdgeChain.lean:578-601`) directly for `D.lineChain f c`
— not for the opaque existential witness `side_walk_abc` uses internally — using Step 1's
extensional equality to reuse `contact_is_edge`/`SegmentDense.subset_closure_diff_finite` exactly
as the original proof does. This avoids relying on any (unstated, unproved) uniqueness of the
covering partition. -/

/-- **Target-side chain edges cover the side exactly.** Same content as `hasEdgeChains_edge`,
specialized to the finset the breakpoint machinery indexes. -/
theorem target_side_lineChain_cover (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) :
    (⋃ e ∈ D.lineChain f c, (D.tile e.1).edge e.2)
      = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  classical
  set S : Set Plane := segment ℝ (D.target.pts i) (D.target.pts (i + 1)) with hSdef
  have hS : {x ∈ D.target.carrier | f x = c} = S := target_contact_side D.target f c hle hi hi1 hi2
  rw [target_side_lineChain_eq_filter D f c hle hi hi1 hi2]
  set part : Finset (Fin N × Fin 3) :=
    Finset.univ.filter (fun e : Fin N × Fin 3 => (D.tile e.1).edge e.2 ⊆ S) with hpart
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    have : (D.tile e.1).edge e.2 ⊆ S := by rw [hpart, Finset.mem_filter] at he; exact he.2
    exact this hxe
  · have hFfin : (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2).Finite :=
      Set.finite_range _
    have hUclosed : IsClosed (⋃ e ∈ part, (D.tile e.1).edge e.2) :=
      Set.Finite.isClosed_biUnion (Finset.finite_toSet part)
        (fun e _ => (D.tile e.1).isClosed_edge e.2)
    have hnd : D.target.pts i ≠ D.target.pts (i + 1) := tile_edge_endpoints_ne D.target i
    have hkey : S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)
              ⊆ ⋃ e ∈ part, (D.tile e.1).edge e.2 := by
      rintro x ⟨hxS, hxF⟩
      have hxt : x ∈ D.target.carrier ∧ f x = c := by rw [← hS] at hxS; exact hxS
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (by rw [D.covers]; exact hxt.1)
      have hlej : ∀ y ∈ (D.tile j).carrier, f y ≤ c :=
        fun y hy => hle y (tile_subset_target D j hy)
      have hxv : ∀ k, x ≠ (D.tile j).pts k := by
        intro k hk; exact hxF ⟨(j, k), hk.symm⟩
      obtain ⟨k, hk⟩ := contact_is_edge (D.tile j) f c hf hlej hxj hxt.2 hxv
      have hsub : (D.tile j).edge k ⊆ S := by
        rw [← hk, ← hS]
        rintro y ⟨hy1, hy2⟩
        exact ⟨tile_subset_target D j hy1, hy2⟩
      refine Set.mem_iUnion₂.mpr ⟨(j, k), ?_, ?_⟩
      · rw [hpart, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub⟩
      · rw [← hk]; exact ⟨hxj, hxt.2⟩
    calc S ⊆ closure (S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)) :=
          Erdos634.SegmentDense.subset_closure_diff_finite hnd hFfin
      _ ⊆ closure (⋃ e ∈ part, (D.tile e.1).edge e.2) := closure_mono hkey
      _ = _ := hUclosed.closure_eq

/-- **Target-side chain edges partition-disjoint.** Direct instance of the generic
`Dissection.sameside_edges_subsingleton`, no new content. -/
theorem target_side_lineChain_disjoint (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hle : ∀ x ∈ D.target.carrier, f x ≤ c) :
    ∀ e₁ ∈ D.lineChain f c, ∀ e₂ ∈ D.lineChain f c, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton := by
  intro e₁ he₁ e₂ he₂ hne
  exact D.sameside_edges_subsingleton f c hf hne
    (fun y hy => hle y (tile_subset_target D e₁.1 hy))
    (fun y hy => hle y (tile_subset_target D e₂.1 hy))
    (D.lineChain_edge_subset he₁) (D.lineChain_edge_subset he₂)

/-- **The exact length sum over the target-side chain.** `Dissection.side_walk`'s conclusion, for
`D.lineChain f c` specifically rather than an opaque partition witness. -/
theorem target_side_lineChain_sum (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) :
    ∑ e ∈ D.lineChain f c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = dist (D.target.pts i) (D.target.pts (i + 1)) := by
  classical
  set S : Set Plane := segment ℝ (D.target.pts i) (D.target.pts (i + 1)) with hSdef
  have hsum := sum_hausdorff_of_partition (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2) S
    (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2) (Set.finite_range _)
    (fun e _ => (D.tile e.1).isClosed_edge e.2 |>.measurableSet)
    (target_side_lineChain_disjoint D f hf c hle)
    (fun e he => lineChain_edge_subset_side D f c hle hi hi1 hi2 he)
    (by
      have hcov := target_side_lineChain_cover D f hf c hle hi hi1 hi2
      intro x hx; exact hcov ▸ hx.1)
  have heq : ∑ e ∈ D.lineChain f c, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = edist (D.target.pts i) (D.target.pts (i + 1)) := by
    have hlhs : ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2)
        = ∑ e ∈ D.lineChain f c, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
      Finset.sum_congr rfl (fun e _ => Tri.hausdorff_edge (D.tile e.1) e.2)
    rw [hlhs, hSdef, MeasureTheory.hausdorffMeasure_segment] at hsum
    exact hsum
  have h1 : ENNReal.ofReal
        (∑ e ∈ D.lineChain f c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := by
    calc ENNReal.ofReal
          (∑ e ∈ D.lineChain f c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
        = ∑ e ∈ D.lineChain f c,
            ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) :=
          ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)
      _ = ∑ e ∈ D.lineChain f c, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
          Finset.sum_congr rfl fun e _ => (edist_dist _ _).symm
      _ = edist (D.target.pts i) (D.target.pts (i + 1)) := heq
      _ = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := edist_dist _ _
  exact (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun e _ => dist_nonneg) dist_nonneg).mp h1

/-- **The main result: the word count is exactly the breakpoint chain's cardinality.** For a
`CongruentDissection` and a target side `i`, the multiplicities `(P, Q, R)` of
`EdgeWordConversion.side_walk_congruent`'s word equation satisfy `P + Q + R =
(nondegenerateTraceChain D f c u v).card` **exactly** — not merely `≤ 3N`
(`side_walk_congruent`'s own bound) — where `nondegenerateTraceChain` is precisely the finset
`Draft.FluxHBreakpointsInjectivity`'s ordered-chain/breakpoint machinery indexes. Composed with
`nondegenerateTraceChain_orderedChain_length`, this is exactly `P + Q + R = (orderedChain ...).length`:
the word's total edge-count *is* the sorted breakpoint chain's length, on the nose. This is the
piece of P66/P71's "counting" gap that is pure combinatorics with no per-edge angle data; Fact 2 in
this file's header (an `a`/`b`-edge has a `γ` at an endpoint) is the remaining, genuinely geometric,
NOT-closed piece. -/
theorem target_side_word_card_eq (D : CongruentDissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (hle : ∀ x ∈ D.target.carrier, f x ≤ c) {i : Fin 3}
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c) :
    ∃ P Q R : ℕ,
      (P : ℝ) * sideLen D 0 + (Q : ℝ) * sideLen D 1 + (R : ℝ) * sideLen D 2
        = dist (D.target.pts i) (D.target.pts (i + 1)) ∧
      P + Q + R =
        (nondegenerateTraceChain D.toDissection f c (D.target.pts i)
          (D.target.pts (i + 1))).card := by
  classical
  obtain ⟨P, Q, R, hPQR, hcard⟩ := Erdos634.Geometry.sum_three_values (D.lineChain f c)
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    (sideLen D 0) (sideLen D 1) (sideLen D 2)
    (fun e _ => edge_length_trichotomy D e.1 e.2)
  refine ⟨P, Q, R, ?_, ?_⟩
  · rw [hPQR]; exact target_side_lineChain_sum D.toDissection f hf c hle hi hi1 hi2
  · rw [hcard, target_side_lineChain_eq_nondegenerate D.toDissection f hf c hle hi hi1 hi2]

/-! ## Non-vacuity: `target_side_word_card_eq`'s hypothesis bundle is satisfiable

`exists_supporting` is unconditional (proved for *every* `Tri` and side index), so `f, c, hf, hle,
hi, hi1, hi2` are always jointly satisfiable; instantiating at `EdgeWordConversion`'s own concrete
`wallCongruentDissection : CongruentDissection 2` (median-cut two-tile witness, already used to
show `word_of_chain_sum` non-vacuous) and side `i = 0` gives an actual witness, checked below —
this is a real dissection, not `False → False`. -/

theorem target_side_word_card_eq_witness :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q R : ℕ),
      (P : ℝ) * sideLen Erdos634.EdgeWordConversion.wallCongruentDissection 0
        + (Q : ℝ) * sideLen Erdos634.EdgeWordConversion.wallCongruentDissection 1
        + (R : ℝ) * sideLen Erdos634.EdgeWordConversion.wallCongruentDissection 2
        = dist (Erdos634.EdgeWordConversion.wallCongruentDissection.target.pts 0)
            (Erdos634.EdgeWordConversion.wallCongruentDissection.target.pts (0 + 1)) ∧
      P + Q + R = (nondegenerateTraceChain
        Erdos634.EdgeWordConversion.wallCongruentDissection.toDissection f c
        (Erdos634.EdgeWordConversion.wallCongruentDissection.target.pts 0)
        (Erdos634.EdgeWordConversion.wallCongruentDissection.target.pts (0 + 1))).card := by
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ :=
    exists_supporting Erdos634.EdgeWordConversion.wallCongruentDissection.target (0 : Fin 3)
  obtain ⟨P, Q, R, hPQR, hcard⟩ :=
    target_side_word_card_eq Erdos634.EdgeWordConversion.wallCongruentDissection f hf c hle hi hi1 hi2
  exact ⟨f, c, P, Q, R, hPQR, hcard⟩

end Erdos634.Draft.FluxHBreakpointsCounting

#print axioms Erdos634.Draft.FluxHBreakpointsCounting.target_side_word_card_eq_witness
#print axioms Erdos634.Draft.FluxHBreakpointsCounting.target_side_lineChain_eq_filter
#print axioms Erdos634.Draft.FluxHBreakpointsCounting.target_side_lineChain_eq_nondegenerate
#print axioms Erdos634.Draft.FluxHBreakpointsCounting.target_side_lineChain_cover
#print axioms Erdos634.Draft.FluxHBreakpointsCounting.target_side_lineChain_sum
#print axioms Erdos634.Draft.FluxHBreakpointsCounting.target_side_word_card_eq
