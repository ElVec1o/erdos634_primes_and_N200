import Erdos634.Dissection
import Erdos634.ChordTraceReal
import Erdos634.Contiguity
import Erdos634.LineParam
import Erdos634.Draft.FluxHBreakpointsInjectivity

/-!
# Materializing a breakpoint as an actual `Plane` point

Erdős #634, P67's "breakpoint bijection" project, sub-part 2 of 3.  `LineParam.lean`/
`Contiguity.lean`'s ordering machinery works purely with real-number parameter data
(`edgeParam`, `sortedPositions`) — nowhere does it identify a shared breakpoint between two
adjacent chain edges with an actual `Plane` point, still less with one of the tile's own vertices.

This file supplies exactly that identification, for two `FluxHBreakpointsInjectivity.
nondegenerateTraceChain`-edges that are *adjacent* in the sorted order (`e₁`'s sorted-right-endpoint
equals `e₂`'s sorted-left-endpoint) **and whose shared parameter lies strictly inside `(0,1)`**
(i.e. the breakpoint is not one of the wall's own two endpoints `u`, `v`).  The main result,
`shared_breakpoint_is_vertex`, produces indices `j₁ j₂ : Fin 3` with
`(D.tile e₁.1).pts j₁ = (D.tile e₂.1).pts j₂`, and both sides equal to the single point
`AffineMap.lineMap u v r` for the shared parameter `r`.

## The geometric content, precisely

Every chain edge `(D.tile e.1).edge e.2` is, by definition (`Tri.edge`), the segment between two of
the tile's own vertices `A := (D.tile e.1).pts e.2`, `B := (D.tile e.1).pts (e.2 + 1)`.  Since
`e ∈ D.lineChain f c`, both `A` and `B` satisfy `f = c`, hence (via `ker_finrank_one`/the same
device as `ChordTraceReal.isSegment_of_convex_inter_hyperplane`) both lie on the line through `u ≠
v`: `A = lineMap u v tA`, `B = lineMap u v tB` for real `tA, tB` (`point_eq_lineMap_of_agree`
below — genuinely new, extracted from the existing machinery but not previously stated at this
level of generality).

The trace `(D.tile e.1).edge e.2 ∩ segment ℝ u v` is then, via `image_segment` applied
twice and `Set.image_inter`/`Set.image_eq_image` (injectivity of `lineMap u v`), the image under
`lineMap u v` of the *real*-interval intersection `segment ℝ tA tB ∩ Icc 0 1`, i.e. (via
`Set.Icc_inter_Icc`) `Icc (min tA tB ⊔ 0) (max tA tB ⊓ 1)`.  Comparing this against
`edgeParam_spec`'s own description of the trace as `segment (lineMap tp) (lineMap tq)` and cancelling
`lineMap u v` (injective) identifies `max tp tq` with `max tA tB ⊓ 1` *exactly* — not merely up to
measure zero.  This is the new fact `Contiguity`'s "no gap" argument never supplies: that one is a
statement about which *real numbers* are covered, not about which endpoint of which original
segment a given parameter came from.

When `max tp tq < 1` (the parameter is not at `v`), the `⊓ 1` cannot be doing the work, so
`max tA tB ⊓ 1 = max tA tB`, forcing `max tp tq = max tA tB` — i.e. the right end of the trace *is*
one of the tile's own vertices, `A` or `B`.  Symmetrically for the left end and `min tp tq > 0`.

Composing this per-edge fact for two adjacent nondegenerate-trace edges, whose shared parameter `r`
is (by the adjacency hypothesis) simultaneously the right end of one trace and the left end of the
other, and lies in `Ioo 0 1`, gives that `r`'s point is a vertex of *both* tiles: the desired
`(D.tile e₁.1).pts j₁ = (D.tile e₂.1).pts j₂`.

Axiom-clean; no `sorry` (mirroring the corpus's standing style) — every step above is discharged
below with the named Mathlib/corpus lemmas; no new axioms or `sorry`s are introduced.
-/

namespace Erdos634.Draft.FluxHBreakpointsPoint

open Erdos634.Geometry Erdos634.Contiguity Erdos634.LineParam
open Erdos634.Draft.FluxHBreakpointsInjectivity
open Set

/-! ## Step 1: any point sharing `f`'s value with two distinct points lies on their line

Genuinely reusable, general-purpose version of the device inside
`ChordTraceReal.isSegment_of_convex_inter_hyperplane` (lines 140-146 there) and
`ChordTraceReal.eq_of_mem_line_of_agree`, extracted as a standalone statement about a `LinearMap`
(rather than embedded in a bigger, differently-shaped theorem). Not previously stated at this
generality in the corpus. -/

/-- **A point agreeing with `f` on two distinct points of the same value lies on their line.**
If `f u = f v = f z` and `u ≠ v`, then `z = lineMap u v t` for some real `t`. -/
theorem point_eq_lineMap_of_agree (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) {u v z : Plane}
    (huv : u ≠ v) (hfuv : f u = f v) (hfz : f z = f u) :
    ∃ t : ℝ, z = AffineMap.lineMap u v t := by
  have hker1 := Erdos634.ChordTraceReal.ker_finrank_one f hf
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker f) := by omega
  obtain ⟨v0, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hspan : ∀ w : LinearMap.ker f, ∃ t : ℝ, t • v0 = w :=
    (finrank_eq_one_iff_of_nonzero' v0 hv0).mp hker1
  have hvuker : v - u ∈ LinearMap.ker f := by
    show f (v - u) = 0
    rw [map_sub]; simp [hfuv]
  have hzuker : z - u ∈ LinearMap.ker f := by
    show f (z - u) = 0
    rw [map_sub]; simp [hfz]
  obtain ⟨tv, htv⟩ := hspan ⟨v - u, hvuker⟩
  obtain ⟨tz, htz⟩ := hspan ⟨z - u, hzuker⟩
  have htv' : v - u = tv • (v0 : Plane) := congrArg Subtype.val htv |>.symm
  have htz' : z - u = tz • (v0 : Plane) := congrArg Subtype.val htz |>.symm
  have htvne : tv ≠ 0 := by
    intro h; apply huv
    have : v - u = 0 := by rw [htv', h, zero_smul]
    exact sub_eq_zero.mp this |>.symm
  refine ⟨tz / tv, ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hgoal : (tz / tv) • (v - u) = z - u := by
    rw [htv', htz', smul_smul]
    congr 1
    field_simp
  rw [hgoal]; abel

/-! ## Step 2: a tile edge's own vertices, parametrized along `u v` -/

/-- **A chain edge's two vertices lie on the wall line**, hence are `lineMap u v` images. -/
theorem tile_edge_vertices_eq_lineMap {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    ∃ tA tB : ℝ, (D.tile e.1).pts e.2 = AffineMap.lineMap u v tA ∧
      (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap u v tB := by
  have hA : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 := left_mem_segment ℝ _ _
  have hB : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).edge e.2 := right_mem_segment ℝ _ _
  have hfA : f ((D.tile e.1).pts e.2) = c := D.lineChain_edge_subset he _ hA
  have hfB : f ((D.tile e.1).pts (e.2 + 1)) = c := D.lineChain_edge_subset he _ hB
  obtain ⟨tA, hA'⟩ := point_eq_lineMap_of_agree f hf huv (hu.trans hv.symm) (hfA.trans hu.symm)
  obtain ⟨tB, hB'⟩ := point_eq_lineMap_of_agree f hf huv (hu.trans hv.symm) (hfB.trans hu.symm)
  exact ⟨tA, tB, hA', hB'⟩

/-! ## Step 3: the trace's real-number description, in terms of the vertex parameters -/

/-- **The trace, as a real interval intersection, pulled back through `lineMap u v`.** -/
theorem trace_eq_lineMap_image_Icc {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    ∃ tA tB : ℝ,
      (D.tile e.1).pts e.2 = AffineMap.lineMap u v tA ∧
      (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap u v tB ∧
      (D.tile e.1).edge e.2 ∩ segment ℝ u v
        = (AffineMap.lineMap u v) '' (Icc (min tA tB ⊔ 0) (max tA tB ⊓ 1)) := by
  obtain ⟨tA, tB, hA, hB⟩ := tile_edge_vertices_eq_lineMap D f hf c u v huv hu hv he
  refine ⟨tA, tB, hA, hB, ?_⟩
  have hedge : (D.tile e.1).edge e.2 = (AffineMap.lineMap u v) '' segment ℝ tA tB := by
    show segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = _
    rw [hA, hB, image_segment ℝ]
  have hseg : segment ℝ u v = (AffineMap.lineMap u v) '' Icc (0:ℝ) 1 := by
    have himg := image_segment ℝ (AffineMap.lineMap u v : ℝ →ᵃ[ℝ] Plane) (0:ℝ) 1
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at himg
    rw [← himg, segment_eq_Icc (by norm_num : (0:ℝ) ≤ 1)]
  have hinter : (D.tile e.1).edge e.2 ∩ segment ℝ u v
      = (AffineMap.lineMap u v) '' (segment ℝ tA tB ∩ Icc (0:ℝ) 1) := by
    rw [hedge, hseg, ← Set.image_inter (LineParam.lineMap_injective_of_ne huv)]
  rw [hinter, segment_eq_Icc' tA tB, Set.Icc_inter_Icc]

/-! ## Step 4: matching against `edgeParam`'s own description, and reading off the vertex

`edgeParam_spec` describes the same trace as `segment (lineMap tp) (lineMap tq)`. Converting that,
too, to a `lineMap`-image of an `Icc` and cancelling the injective `lineMap u v` identifies
`(min tp tq, max tp tq)` *exactly* with `(min tA tB ⊔ 0, max tA tB ⊓ 1)` — the promised upgrade from
"the real parameters agree" (all `Contiguity`/`LineParam` give) to "the endpoint is literally one of
the tile's own two vertices", once the wall-endpoint case (`⊔ 0`/`⊓ 1` actually biting) is excluded
by hypothesis. -/

open Erdos634.LineParam in
/-- **The nonempty-trace case's parameters match the vertex parameters exactly.** -/
theorem edgeParam_eq_vertex_Icc {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c)
    (hne : (edgeParam D f c u v e) ≠ (0, 0))
    (tA tB : ℝ) (hA : (D.tile e.1).pts e.2 = AffineMap.lineMap u v tA)
    (hB : (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap u v tB)
    (htrace : (D.tile e.1).edge e.2 ∩ segment ℝ u v
        = (AffineMap.lineMap u v) '' (Icc (min tA tB ⊔ 0) (max tA tB ⊓ 1))) :
    min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 = min tA tB ⊔ 0 ∧
    max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 = max tA tB ⊓ 1 := by
  rcases edgeParam_spec D f hf c u v huv he hu hv with ⟨-, hz⟩ | ⟨-, -, heq, -⟩
  · exact absurd hz hne
  · set tp := (edgeParam D f c u v e).1
    set tq := (edgeParam D f c u v e).2
    have himg : (AffineMap.lineMap u v) '' Icc (min tp tq) (max tp tq)
        = (AffineMap.lineMap u v) '' Icc (min tA tB ⊔ 0) (max tA tB ⊓ 1) := by
      rw [← segment_eq_Icc' tp tq, image_segment ℝ, ← heq, htrace]
    have hIcc : Icc (min tp tq) (max tp tq) = Icc (min tA tB ⊔ 0) (max tA tB ⊓ 1) :=
      (Set.image_eq_image (LineParam.lineMap_injective_of_ne huv)).mp himg
    exact (Icc_eq_Icc_iff min_le_max).mp hIcc

/-- **The right endpoint, when not at `v` (parameter `< 1`), is the max-parameter tile vertex.** -/
theorem edgeParam_max_eq_vertex {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c)
    (hne : (edgeParam D f c u v e) ≠ (0, 0))
    (hlt : max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 < 1) :
    AffineMap.lineMap u v (max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
      = (D.tile e.1).pts e.2 ∨
    AffineMap.lineMap u v (max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
      = (D.tile e.1).pts (e.2 + 1) := by
  obtain ⟨tA, tB, hA, hB, htrace⟩ := trace_eq_lineMap_image_Icc D f hf c u v huv hu hv he
  obtain ⟨-, hmax⟩ := edgeParam_eq_vertex_Icc D f hf c u v huv hu hv he hne tA tB hA hB htrace
  have hmaxlt : max tA tB ⊓ 1 < 1 := hmax ▸ hlt
  have hcases : max tA tB ⊓ 1 = max tA tB := by
    rcases le_total (max tA tB) 1 with h | h
    · exact min_eq_left h
    · exact absurd (min_eq_right h ▸ hmaxlt) (lt_irrefl 1)
  rw [hmax, hcases]
  rcases le_total tA tB with hle | hle
  · rw [max_eq_right hle]; exact Or.inr hB.symm
  · rw [max_eq_left hle]; exact Or.inl hA.symm

/-- **The left endpoint, when not at `u` (parameter `> 0`), is the min-parameter tile vertex.** -/
theorem edgeParam_min_eq_vertex {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c)
    (hne : (edgeParam D f c u v e) ≠ (0, 0))
    (hgt : (0:ℝ) < min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2) :
    AffineMap.lineMap u v (min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
      = (D.tile e.1).pts e.2 ∨
    AffineMap.lineMap u v (min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
      = (D.tile e.1).pts (e.2 + 1) := by
  obtain ⟨tA, tB, hA, hB, htrace⟩ := trace_eq_lineMap_image_Icc D f hf c u v huv hu hv he
  obtain ⟨hmin, -⟩ := edgeParam_eq_vertex_Icc D f hf c u v huv hu hv he hne tA tB hA hB htrace
  have hmingt : (0:ℝ) < min tA tB ⊔ 0 := hmin ▸ hgt
  have hcases : min tA tB ⊔ 0 = min tA tB := by
    rcases le_total 0 (min tA tB) with h | h
    · exact max_eq_left h
    · exact absurd (max_eq_right h ▸ hmingt) (lt_irrefl 0)
  rw [hmin, hcases]
  rcases le_total tA tB with hle | hle
  · rw [min_eq_left hle]; exact Or.inl hA.symm
  · rw [min_eq_right hle]; exact Or.inr hB.symm

/-! ## Step 5: the main assembly — an adjacent breakpoint is literally a shared `Plane` vertex

For two `nondegenerateTraceChain` edges `e₁ e₂` adjacent in the sorted order (`e₁`'s right endpoint
equals `e₂`'s left endpoint `r`), with `r` strictly interior to `(0,1)` (not one of the wall's own
two endpoints `u`, `v`), the shared breakpoint materializes as an actual `Plane` point equal to a
vertex of **both** tiles. -/

open Erdos634.LineParam in
/-- **The main result.** Two nondegenerate-trace chain edges whose sorted intervals are adjacent at
an interior parameter `r ∈ (0,1)` share an actual `Plane` vertex: `lineMap u v r` equals one of
`e₁`'s own two vertices and one of `e₂`'s own two vertices, in particular giving indices `j₁ j₂` with
`(D.tile e₁.1).pts j₁ = (D.tile e₂.1).pts j₂`. -/
theorem shared_breakpoint_is_vertex {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    {e₁ e₂ : Fin N × Fin 3}
    (he₁ : e₁ ∈ nondegenerateTraceChain D f c u v) (he₂ : e₂ ∈ nondegenerateTraceChain D f c u v)
    (hadj : max (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2
        = min (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2)
    (hr0 : (0:ℝ) < max (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2)
    (hr1 : max (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2 < 1) :
    ∃ j₁ j₂ : Fin 3, (D.tile e₁.1).pts j₁ = (D.tile e₂.1).pts j₂ ∧
      (D.tile e₁.1).pts j₁ =
        AffineMap.lineMap u v (max (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2) := by
  obtain ⟨hp1, hd1⟩ := (mem_nondegenerateTraceChain_iff D f c u v).mp he₁
  obtain ⟨hp2, hd2⟩ := (mem_nondegenerateTraceChain_iff D f c u v).mp he₂
  have hne1 : (edgeParam D f c u v e₁) ≠ (0, 0) := by
    intro h; rw [h] at hd1; simp at hd1
  have hne2 : (edgeParam D f c u v e₂) ≠ (0, 0) := by
    intro h; rw [h] at hd2; simp at hd2
  have h1 := edgeParam_max_eq_vertex D f hf c u v huv hu hv hp1 hne1 hr1
  have hr1' : min (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2 < 1 :=
    hadj ▸ hr1
  have hr0' : (0:ℝ) < min (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2 :=
    hadj ▸ hr0
  have h2 := edgeParam_min_eq_vertex D f hf c u v huv hu hv hp2 hne2 hr0'
  rcases h1 with h1 | h1
  · have h1' : AffineMap.lineMap u v
        (min (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2)
        = (D.tile e₁.1).pts e₁.2 := hadj ▸ h1
    rcases h2 with h2 | h2
    · exact ⟨e₁.2, e₂.2, h1'.symm.trans h2, h1.symm⟩
    · exact ⟨e₁.2, e₂.2 + 1, h1'.symm.trans h2, h1.symm⟩
  · have h1' : AffineMap.lineMap u v
        (min (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2)
        = (D.tile e₁.1).pts (e₁.2 + 1) := hadj ▸ h1
    rcases h2 with h2 | h2
    · exact ⟨e₁.2 + 1, e₂.2, h1'.symm.trans h2, h1.symm⟩
    · exact ⟨e₁.2 + 1, e₂.2 + 1, h1'.symm.trans h2, h1.symm⟩

end Erdos634.Draft.FluxHBreakpointsPoint
