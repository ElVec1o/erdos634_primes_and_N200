import Erdos634.Dissection
import Erdos634.TileAt
import Erdos634.Draft.FluxHBreakpointsPoint

/-!
# Discharging `TileAt`'s boundary-figure hypotheses at a chain-interior breakpoint

Erdős #634, P67's "breakpoint bijection" project, sub-part 3 of 3 (the capstone). Sub-parts 1
(`Draft.FluxHBreakpointsInjectivity`) and 2 (`Draft.FluxHBreakpointsPoint`) produce, for two
`nondegenerateTraceChain`-adjacent chain edges on a wall segment `[u, v]` whose shared parameter
`r` is strictly interior (`r ∈ (0,1)`), an actual `Plane` vertex `w := lineMap u v r` shared by
both tiles (`shared_breakpoint_is_vertex`).

`TileAt.congruentDissection_boundary_figure_cases` (`TileAt.lean:682-707`) classifies the
angle-multiset at a point `v` of a `CongruentDissection`, but needs two hypotheses nowhere
discharged for such a breakpoint:

* `v ∈ frontier D.target.carrier`
* `v ∉ Set.range D.target.pts`

This file discharges both, **specifically for the case the wall `[u, v]` is a target side**
(`u = D.target.pts i`, `v = D.target.pts (i+1)`, the endpoints supplied by `exists_supporting`) —
this is the case F4/row 14 actually needs (a target *side*'s breakpoints), and it is also the only
case `shared_breakpoint_is_vertex`'s own setup is naturally read against: nothing in sub-parts 1/2
restricts `u, v` to being a target side rather than an interior chord, but instantiating them as an
interior chord's endpoints has no counterpart to `exists_supporting`/`target_contact_side` (an
interior wall has no "strict inequality on the third vertex" structure to build the halfplane
bound from), so that case is left for further work rather than forced here.

No `sorry`; axiom-clean (checked via `#print axioms` on the capstone theorem, standard axioms
only, matching the corpus's style).
-/

namespace Erdos634.Draft.FluxHBreakpointsFrontier

open Erdos634.Geometry Erdos634.Geometry.Dissection
open Erdos634.Contiguity Erdos634.LineParam
open Erdos634.Draft.FluxHBreakpointsInjectivity Erdos634.Draft.FluxHBreakpointsPoint
open Set

/-! ## Step A: a point of `{f = c}` inside a halfplane-bounded convex tile is a frontier point

General convexity fact, not previously stated in the corpus: same technique as
`Dissection.two_vertices_on_line` (`Dissection.lean:496-529`) — an interior point of a convex set
bounded by a supporting hyperplane `f ≤ c` cannot itself satisfy `f = c`, because a small ball
around it would contain points pushed strictly past `c` along any direction `f` does not vanish
on. Stated standalone here (`two_vertices_on_line` embeds the same push-argument inside a
different, bigger theorem and does not expose it). -/

/-- **A boundary-value point of a halfplane-bounded convex tile lies in its frontier.** If
`f ≤ c` on all of `T.carrier` and `f x = c` at some `x ∈ T.carrier`, then `x ∈ frontier T.carrier`
(it cannot be interior, since interior points admit a ball on which `f` would have to exceed `c`
in the direction `f` increases). -/
theorem Tri.mem_frontier_of_supporting (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hle : ∀ y ∈ T.carrier, f y ≤ c) {x : Plane} (hx : x ∈ T.carrier) (hfx : f x = c) :
    x ∈ frontier T.carrier := by
  have hclosed : IsClosed T.carrier := T.isCompact.isClosed
  rw [frontier, hclosed.closure_eq]
  refine ⟨hx, fun hxi => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hxi
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h; push_neg at h; exact hf (LinearMap.ext fun z => by simp [h z])
  set y' : Plane := if 0 < f y then y else -y with hy'def
  have hy'pos : 0 < f y' := by
    rw [hy'def]
    split
    · assumption
    · rename_i hnp
      have hneg : f y < 0 := lt_of_le_of_ne (not_lt.mp hnp) hy
      simpa using neg_pos.mpr hneg
  have hynorm : 0 < ‖y'‖ := by
    rcases eq_or_ne y' 0 with h0 | h0
    · rw [h0, map_zero] at hy'pos; exact absurd hy'pos (lt_irrefl 0)
    · exact norm_pos_iff.mpr h0
  set t : ℝ := ε / (2 * ‖y'‖) with htdef
  have htpos : 0 < t := by positivity
  have hval : t * ‖y'‖ = ε / 2 := by
    rw [htdef]; field_simp
  have hmemball : x + t • y' ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + t • y' - x = t • y' := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hval]
    linarith
  have hin : x + t • y' ∈ T.carrier := interior_subset (hball hmemball)
  have hle' := hle _ hin
  rw [map_add, map_smul, smul_eq_mul, hfx] at hle'
  nlinarith [mul_pos htpos hy'pos]

/-! ## Step B: an interior point of a target side is a frontier point and not a target vertex

Specializes Step A to `u = T.pts i`, `v = T.pts (i+1)` via `exists_supporting`/the same
strict-inequality-on-the-third-vertex data `target_contact_side` uses, and separately rules out
the three vertices by the wall-line's constant `f`-value versus `exists_supporting`'s strict
inequality (third vertex) and `lineMap`-injectivity (the two endpoints). -/

/-- **An interior point of one target side is a frontier point, not equal to any target vertex.**
For `r ∈ (0,1)`, `lineMap (T.pts i) (T.pts (i+1)) r` lies in `frontier T.carrier` and is not
`T.pts k` for any `k`. -/
theorem target_side_interior_point_frontier_not_vertex (T : Tri) (i : Fin 3) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    AffineMap.lineMap (T.pts i) (T.pts (i + 1)) r ∈ frontier T.carrier ∧
    AffineMap.lineMap (T.pts i) (T.pts (i + 1)) r ∉ Set.range T.pts := by
  classical
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting T i
  set w : Plane := AffineMap.lineMap (T.pts i) (T.pts (i + 1)) r with hwdef
  have hfw : f w = c := by
    rw [hwdef, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub,
      smul_eq_mul, hi, hi1]
    ring
  have hwseg : w ∈ segment ℝ (T.pts i) (T.pts (i + 1)) := by
    rw [segment_eq_image_lineMap]; exact ⟨r, ⟨hr0.le, hr1.le⟩, rfl⟩
  have hwedge : w ∈ T.edge i := by rw [Tri.edge]; exact hwseg
  have hwmem : w ∈ T.carrier := T.edge_subset_carrier i hwedge
  have hfrontier : w ∈ frontier T.carrier :=
    Tri.mem_frontier_of_supporting T f hf c hle hwmem hfw
  have hne : T.pts i ≠ T.pts (i + 1) := by
    intro h
    have hij : i = i + 1 := T.indep.injective h
    fin_cases i <;> exact absurd hij (by decide)
  have hnotvertex : w ∉ Set.range T.pts := by
    rintro ⟨k, hk⟩
    have hexh : k = i ∨ k = i + 1 ∨ k = i + 2 := by
      fin_cases i <;> fin_cases k <;> decide
    rcases hexh with heq | heq | heq
    · -- w = T.pts i = lineMap u v 0, so r = 0 by injectivity, contradicting hr0
      rw [heq] at hk
      have h0 : w = AffineMap.lineMap (T.pts i) (T.pts (i + 1)) (0 : ℝ) := by
        rw [AffineMap.lineMap_apply_zero]; exact hk.symm
      have hr0' : r = 0 := lineMap_injective_of_ne hne (hwdef ▸ h0)
      exact absurd hr0' hr0.ne'
    · -- w = T.pts (i+1) = lineMap u v 1, so r = 1 by injectivity, contradicting hr1
      rw [heq] at hk
      have h1 : w = AffineMap.lineMap (T.pts i) (T.pts (i + 1)) (1 : ℝ) := by
        rw [AffineMap.lineMap_apply_one]; exact hk.symm
      have hr1' : r = 1 := lineMap_injective_of_ne hne (hwdef ▸ h1)
      exact absurd hr1' hr1.ne
    · -- w = T.pts (i+2), but f (T.pts (i+2)) < c = f w
      rw [heq] at hk
      rw [hk] at hi2
      exact absurd hfw (by linarith)
  exact ⟨hfrontier, hnotvertex⟩

/-! ## Step C: assembly — `TileAt`'s two hypotheses at a `shared_breakpoint_is_vertex` point,
when the wall is a target side

Instantiates `shared_breakpoint_is_vertex` (sub-part 2, `FluxHBreakpointsPoint.lean`) with
`u = D.target.pts i`, `v = D.target.pts (i+1)` (a target side) and its own `f, c, hf, hle, hi,
hi1, hi2` supplied by the caller (typically from `exists_supporting D.target i` — left as
hypotheses here rather than reconstructed internally via `Classical.choose`, matching
`shared_breakpoint_is_vertex`'s own style and avoiding an unreadable, choice-laden statement).
Discharges `congruentDissection_boundary_figure_cases`'s two hypotheses at the resulting shared
vertex via Step B, and applies the classification. This is the capstone of the whole
breakpoint-bijection project (P67), restricted to the wall-is-a-target-side case named in the
task. -/

/-- The breakpoint parameter: the right end of `e`'s trace on the wall `[u, v]`. -/
noncomputable def breakpointParam {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (u v : Plane) (e : Fin N × Fin 3) : ℝ :=
  max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2

/-- The breakpoint, as an actual `Plane` point on the wall line. -/
noncomputable def breakpointPt {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (u v : Plane) (e : Fin N × Fin 3) : Plane :=
  AffineMap.lineMap u v (breakpointParam D f c u v e)

/-- **The capstone.** At every interior breakpoint (`r ∈ (0,1)`) shared by two
`nondegenerateTraceChain`-adjacent chain edges on a *target side* `[D.target.pts i,
D.target.pts (i+1)]`: the breakpoint is an actual shared `Plane` vertex of both tiles, **and**
the local angle multiset there is one of the three named cases
(`TileAt.congruentDissection_boundary_figure_cases`'s conclusion) — the two hypotheses that
theorem needs (`frontier` membership, non-vertex-hood) are discharged here, not assumed. This
closes P67 end to end for the wall-is-a-target-side case. -/
theorem shared_breakpoint_boundary_figure_cases {N : ℕ} (D : CongruentDissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (i : Fin 3)
    (hi : f (D.target.pts i) = c) (hi1 : f (D.target.pts (i + 1)) = c)
    (hi2 : f (D.target.pts (i + 2)) < c)
    (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {e₁ e₂ : Fin N × Fin 3}
    (he₁ : e₁ ∈ nondegenerateTraceChain D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)))
    (he₂ : e₂ ∈ nondegenerateTraceChain D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)))
    (hadj : breakpointParam D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁
      = min (edgeParam D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₂).1
          (edgeParam D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₂).2)
    (hr0 : (0:ℝ) < breakpointParam D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
    (hr1 : breakpointParam D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁ < 1) :
    (∃ j₁ j₂ : Fin 3, (D.tile e₁.1).pts j₁ = (D.tile e₂.1).pts j₂) ∧
    ((({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = Real.pi} : Finset (Fin N)).card = 1 ∧
        ({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = α} : Finset (Fin N)).card = 0 ∧
        ({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = β} : Finset (Fin N)).card = 0 ∧
        ({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = γ} : Finset (Fin N)).card = 0) ∨
      (({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = α} : Finset (Fin N)).card = 3 ∧
        ({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = β} : Finset (Fin N)).card = 2 ∧
        ({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = γ} : Finset (Fin N)).card = 0) ∨
      (({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = α} : Finset (Fin N)).card = 1 ∧
        ({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = β} : Finset (Fin N)).card = 1 ∧
        ({j | (D.tile j).localAngle
          (breakpointPt D.toDissection f c (D.target.pts i) (D.target.pts (i + 1)) e₁)
          = γ} : Finset (Fin N)).card = 1)) := by
  classical
  have huv : D.target.pts i ≠ D.target.pts (i + 1) := by
    intro h
    have hij : i = i + 1 := D.target.indep.injective h
    fin_cases i <;> exact absurd hij (by decide)
  obtain ⟨j₁, j₂, hshared, -⟩ :=
    shared_breakpoint_is_vertex D.toDissection f hf c (D.target.pts i) (D.target.pts (i + 1))
      huv hi hi1 he₁ he₂ hadj hr0 hr1
  obtain ⟨hfrontier, hnotvertex⟩ :=
    target_side_interior_point_frontier_not_vertex D.target i hr0 hr1
  refine ⟨⟨j₁, j₂, hshared⟩, ?_⟩
  exact congruentDissection_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0
    hπ0 hγdef hrel hirr hα' hβ' hγ' hfrontier hnotvertex

end Erdos634.Draft.FluxHBreakpointsFrontier
