import Erdos634.Dissection
import Erdos634.Contiguity
import Erdos634.WallChain
import Erdos634.LineParam

/-!
# The nonempty/nondegenerate-trace subchain is injective under `edgeParam`'s left endpoint

P67, sub-part 1 of 3 (the "breakpoint bijection" project).  `LineParam.lean:508-517` flags that
`Contiguity.sortedPositions`/`orderedChain`'s "one entry per edge" guarantee
(`orderedChain_length`) needs `Set.InjOn pos chain`, and that this **fails in general** on the raw
chain `D.lineChain f c`: every chain edge whose trace on the wall segment `segment ℝ u v` is empty
defaults its `edgeParam` to `(0, 0)` (`LineParam.edgeParam`), so any two empty-trace edges collide.

This file supplies the fix, but a genuine subtlety was found along the way (see the discussion
below `nondegenerateTraceChain`): the literal "nonempty trace" subchain the task specifies is
**not** enough to force injectivity by the technique `distinct_left_endpoints` gives, because a
chain edge can meet the wall segment in exactly one point (a single shared endpoint), and two
*distinct* such edges can share that same point — `Dissection.sameside_edges_subsingleton` (via
`LineParam.edgeParam_Icc_subsingleton`) only bounds their full-edge overlap by "at most one point",
which is consistent with that one point being shared. What **is** provably injective, by exactly
`distinct_left_endpoints`'s technique with no new geometric input, is the subchain of edges whose
trace is **nondegenerate** (more than one point, i.e. a genuine sub-segment, not a single touch) —
this is a strictly smaller class than "nonempty trace" but still exactly the class the empty-trace
collision comment was worried about excluding, since a nondegenerate trace is in particular
nonempty and does not default to `(0, 0)`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Draft.FluxHBreakpointsInjectivity

open Erdos634.Geometry Erdos634.Contiguity Erdos634.LineParam Set

/-! ## A real-number lemma: a subsingleton intersection of two open intervals is empty

The core fact `Ioo_disjoint_of_subsingleton_inter` (`LineParam.lean:184-218`) already proves,
wrapped in `lineMap`; this is exactly its underlying real-number skeleton (its own proof, lines
187-218, minus the `lineMap` lifting), extracted so it can be reused directly on the raw parameter
intervals without re-deriving it. -/

/-- **A subsingleton intersection of two nonempty-or-not open intervals is empty.** A nonempty
intersection of two open real intervals is itself a nonempty open interval, hence infinite — so it
cannot be a subsingleton unless it is already empty. Same technique as
`LineParam.Ioo_disjoint_of_subsingleton_inter`, without the `lineMap` wrapping. -/
theorem Ioo_inter_Ioo_eq_empty_of_subsingleton {p1 q1 p2 q2 : ℝ}
    (hsub : (Ioo p1 q1 ∩ Ioo p2 q2).Subsingleton) : Ioo p1 q1 ∩ Ioo p2 q2 = ∅ := by
  by_contra hne
  have hne' : (Ioo p1 q1 ∩ Ioo p2 q2).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  rw [Set.Ioo_inter_Ioo, Set.nonempty_Ioo] at hne'
  obtain ⟨x, hx1, hx2⟩ := exists_between hne'
  obtain ⟨y, hy1, hy2⟩ := exists_between hx2
  have hxy : x ≠ y := hy1.ne
  have hxmem : x ∈ Ioo p1 q1 ∩ Ioo p2 q2 := by
    rw [Set.Ioo_inter_Ioo]; exact ⟨hx1, hx2⟩
  have hymem : y ∈ Ioo p1 q1 ∩ Ioo p2 q2 := by
    rw [Set.Ioo_inter_Ioo]; exact ⟨hx1.trans hy1, hy2⟩
  exact hxy (hsub hxmem hymem)



/-! ## The nondegenerate-trace subchain

Filtering `D.lineChain f c` by "trace meets the wall segment in more than one point" (equivalently,
under `edgeParam_spec`'s dichotomy, `edgeParam`'s two coordinates are distinct — the trace is a
genuine sub-segment rather than a point or empty). This is the class on which
`distinct_left_endpoints` applies with no further geometric input; see the header discussion for why
the plain "nonempty trace" class (which the empty-trace-collision comment names) is not, in
general, enough. -/

open scoped Classical in
/-- **The nondegenerate-trace subchain**: chain edges whose `edgeParam` left/right coordinates are
distinct, i.e. whose trace on `segment ℝ u v` is a genuine sub-segment (not empty, and not a single
point). -/
noncomputable def nondegenerateTraceChain {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (u v : Plane) : Finset (Fin N × Fin 3) :=
  (D.lineChain f c).filter fun e =>
    min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
      < max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2

theorem mem_nondegenerateTraceChain_iff {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (u v : Plane) {e : Fin N × Fin 3} :
    e ∈ nondegenerateTraceChain D f c u v ↔
      e ∈ D.lineChain f c ∧
        min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
          < max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 := by
  classical
  simp [nondegenerateTraceChain]

/-- **A nondegenerate-trace edge has nonempty trace** — so this subchain is in particular a
sub-Finset of the "nonempty trace" class named in the task, not a disjoint notion from it: it is
exactly the case `edgeParam ≠ (0, 0)` with, additionally, the two coordinates distinct. Uses
`edgeParam_spec`'s dichotomy: the empty-trace case forces `edgeParam = (0, 0)`, whose `min = max`,
contradicting the nondegeneracy hypothesis. -/
theorem nondegenerateTraceChain_trace_nonempty {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ)
    (hf : f ≠ 0) (c : ℝ) (u v : Plane) (huv : u ≠ v) (hS : segment ℝ u v ⊆ {y | f y = c})
    {e : Fin N × Fin 3} (he : e ∈ nondegenerateTraceChain D f c u v) :
    ((D.tile e.1).edge e.2 ∩ segment ℝ u v).Nonempty := by
  have hu : f u = c := hS (left_mem_segment ℝ u v)
  have hv : f v = c := hS (right_mem_segment ℝ u v)
  obtain ⟨hchain, hdeg⟩ := (mem_nondegenerateTraceChain_iff D f c u v).mp he
  rcases edgeParam_spec D f hf c u v huv hchain hu hv with ⟨-, hz⟩ | ⟨-, -, heq, -⟩
  · rw [hz] at hdeg; simp at hdeg
  · exact heq ▸ ⟨AffineMap.lineMap u v (edgeParam D f c u v e).1, left_mem_segment ℝ _ _⟩



/-! ## Injectivity of `edgeParam`'s left endpoint on the nondegenerate subchain

The heart of the fix. `edgeParam_Icc_subsingleton` (`LineParam.lean:385-421`) already gives, for
any two *distinct* chain edges under the standard side hypotheses, that their sorted `Icc`
parameter intervals meet in at most one point. Restricted to the nondegenerate subchain, the open
interiors `Ioo` are themselves nonempty open intervals, so their intersection — a subset of the
`Icc` intersection, hence itself a subsingleton by `Set.Subsingleton.anti` — must, by
`Ioo_inter_Ioo_eq_empty_of_subsingleton`, be empty. That is exactly
`Contiguity.distinct_left_endpoints`'s hypothesis, and its conclusion is the desired injectivity. -/

/-- **`edgeParam`'s left endpoint is injective on the nondegenerate-trace subchain.** Exactly
`distinct_left_endpoints`'s technique (as directed): the two edges' open parameter intervals are
disjoint (`Ioo_inter_Ioo_eq_empty_of_subsingleton` applied to `edgeParam_Icc_subsingleton`'s bound),
so `distinct_left_endpoints` gives their left endpoints (`min`s) distinct. -/
theorem injOn_min_edgeParam_nondegenerateTraceChain {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c}) :
    Set.InjOn (fun e => min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
      (nondegenerateTraceChain D f c u v : Set (Fin N × Fin 3)) := by
  have hu : f u = c := hS (left_mem_segment ℝ u v)
  have hv : f v = c := hS (right_mem_segment ℝ u v)
  intro e1 he1 e2 he2 heq
  simp only [Finset.mem_coe] at he1 he2
  obtain ⟨hp1, hd1⟩ := (mem_nondegenerateTraceChain_iff D f c u v).mp he1
  obtain ⟨hp2, hd2⟩ := (mem_nondegenerateTraceChain_iff D f c u v).mp he2
  by_contra hne
  obtain ⟨hi1, hi1', hle1'⟩ := Dissection.mem_lineChain.mp hp1
  obtain ⟨hi2, hi2', hle2'⟩ := Dissection.mem_lineChain.mp hp2
  have hle1 : ∀ y ∈ (D.tile e1.1).carrier, f y ≤ c :=
    Tri.carrier_subset_halfplane _ f c hle1'
  have hle2 : ∀ y ∈ (D.tile e2.1).carrier, f y ≤ c :=
    Tri.carrier_subset_halfplane _ f c hle2'
  have hicc := edgeParam_Icc_subsingleton D f hf c u v huv hp1 hp2 hne hu hv hle1 hle2
  have hsub : Ioo (min (edgeParam D f c u v e1).1 (edgeParam D f c u v e1).2)
        (max (edgeParam D f c u v e1).1 (edgeParam D f c u v e1).2) ∩
      Ioo (min (edgeParam D f c u v e2).1 (edgeParam D f c u v e2).2)
        (max (edgeParam D f c u v e2).1 (edgeParam D f c u v e2).2) ⊆
      Icc (min (edgeParam D f c u v e1).1 (edgeParam D f c u v e1).2)
        (max (edgeParam D f c u v e1).1 (edgeParam D f c u v e1).2) ∩
      Icc (min (edgeParam D f c u v e2).1 (edgeParam D f c u v e2).2)
        (max (edgeParam D f c u v e2).1 (edgeParam D f c u v e2).2) :=
    Set.inter_subset_inter Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hioo := Ioo_inter_Ioo_eq_empty_of_subsingleton (hicc.anti hsub)
  exact absurd heq (Erdos634.Contiguity.distinct_left_endpoints hd1 hd2 hioo)



/-! ## The corrected `orderedChain_length`

Instantiating `Contiguity.orderedChain_length` against the nondegenerate subchain and the
injectivity just proved. `orderedChain` needs `[Inhabited (Fin N × Fin 3)]`; `D.pos : 0 < N`
(`Dissection.lean:252`) supplies a genuine witness `⟨0, D.pos⟩ : Fin N`, so the instance is
satisfiable, not vacuous — callers discharge it with `haveI := (⟨⟨0, D.pos⟩⟩ : Inhabited (Fin N))`. -/

/-- **One entry per nondegenerate-trace chain edge.** The corrected form of
`Contiguity.orderedChain_length` for the subchain on which the left-endpoint key is actually
injective. -/
theorem nondegenerateTraceChain_orderedChain_length {N : ℕ} [Inhabited (Fin N)]
    (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c}) :
    (Erdos634.Contiguity.orderedChain (nondegenerateTraceChain D f c u v)
        (fun e => min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)).length
      = (nondegenerateTraceChain D f c u v).card :=
  Erdos634.Contiguity.orderedChain_length _ _
    (injOn_min_edgeParam_nondegenerateTraceChain D f hf c u v huv hS)

end Erdos634.Draft.FluxHBreakpointsInjectivity

