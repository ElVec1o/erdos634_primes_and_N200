import Mathlib.Tactic
import Erdos634.WallChain
import Erdos634.EdgeChain
import Erdos634.LineParam

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the trapezoid lemma for a stopped run (their Lemma 32, p. 26).
# Theorem D' (Lemma 32, 1D tools): the end of a wall segment lies on a chain edge  

`endpoint_in_chain` : for a wall segment `[P,Q]` (interior, on the line `{F = c}`, meeting no tile interior) the end `Q` lies on an edge
of the chain of the line: the chain covers the open segment outside the finitely many tile vertices (`wall_cover`), the chain is a finite
union of closed edges, and `Q` is a limit of such points.
-/

open MeasureTheory Set

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry

theorem endpoint_in_chain {N : ℕ} (D : Dissection N) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q : Plane}
    (hPQ : P ≠ Q) (hS : segment ℝ P Q ⊆ {y | F y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∃ e ∈ D.lineChain F c, Q ∈ (D.tile e.1).edge e.2 := by
  classical
  set U : Set Plane := ⋃ e ∈ D.lineChain F c, (D.tile e.1).edge e.2 with hU
  have hcl : IsClosed U := isClosed_biUnion_finset (fun e _ => (D.tile e.1).isClosed_edge e.2)
  have hsub : openSegment ℝ P Q \ D.vertexSet ⊆ U := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := D.wall_cover F c hF hPQ hS hint hwall hx.1 hx.2
    exact Set.mem_iUnion₂.mpr ⟨e, he, hxe⟩
  have hQcl : Q ∈ closure (openSegment ℝ P Q \ D.vertexSet) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hd : 0 < dist P Q := dist_pos.mpr hPQ
    set δ : ℝ := min (1 / 2) (ε / (2 * dist P Q)) with hδ
    have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
    have hδ2 : δ * dist P Q ≤ ε / 2 := by
      have : δ ≤ ε / (2 * dist P Q) := min_le_right _ _
      calc δ * dist P Q ≤ ε / (2 * dist P Q) * dist P Q := by gcongr
        _ = ε / 2 := by field_simp
    have hinf : (Set.Ioo (1 - δ) 1).Infinite := Set.Ioo_infinite (by linarith)
    have hfin : {t : ℝ | AffineMap.lineMap P Q t ∈ D.vertexSet}.Finite := by
      refine Set.Finite.preimage (f := fun t : ℝ => AffineMap.lineMap P Q t) ?_ D.vertexSet_finite
      intro a _ b _ hab
      exact Erdos634.LineParam.lineMap_injective_of_ne hPQ hab
    obtain ⟨t, ht, htF⟩ := (hinf.diff hfin).nonempty
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨AffineMap.lineMap P Q t, ⟨?_, htF⟩, ?_⟩
    · rw [openSegment_eq_image_lineMap]
      exact ⟨t, ⟨ht0, ht.2⟩, rfl⟩
    · rw [dist_comm, dist_lineMap_right, Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
      have : 1 - t < δ := by linarith [ht.1]
      calc (1 - t) * dist P Q < δ * dist P Q := by gcongr
        _ ≤ ε / 2 := hδ2
        _ < ε := by linarith
  have hQU : Q ∈ U := closure_minimal hsub hcl hQcl
  obtain ⟨e, he, hQe⟩ := Set.mem_iUnion₂.mp hQU
  exact ⟨e, he, hQe⟩

#print axioms endpoint_in_chain
end Erdos634.Draft.ThmDRun
