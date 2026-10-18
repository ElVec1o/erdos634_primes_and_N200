import Mathlib.Tactic
import Erdos634.WallChain
import Erdos634.EdgeChain
import Erdos634.MarchInduction

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (H2), general geometry: the far-side edge chain of an interior segment with frontier ends  

For a segment `[P,Q]` on the line `{g = c}`, open segment inside the target, ends on the frontier, a wall
(no tile interior meets it), the chain `D.lineChain g c` (tile edges on the line whose tile lies in `{g <= c}`):

* every chain edge lies in `[P,Q]` (a point of the line in the target is in `[P,Q]`: otherwise an end would be interior);
* the chain edges' lengths sum to `|PQ|`;  every non-vertex point of the open segment lies on a chain edge;
* distinct chain edges meet in at most a point.

Built from `WallChain.wall_partition/wall_cover` and `EdgeChain.sameside_edges_subsingleton`.
-/

open MeasureTheory Set

namespace Erdos634.Draft.ThmDRowFar

open Erdos634.Geometry

/-- an interior point and a closure point: the open segment is interior -/
theorem end_not_beyond {K : Set Plane} (hK : Convex ℝ K) {P d y : Plane} (hd : d ≠ 0)
    (hz : P + (1 / 2 : ℝ) • d ∈ interior K) (hy : y ∈ K) (τ : ℝ) (hτ : τ < 0)
    (hyτ : y = P + τ • d) : P ∈ interior K := by
  have hy' : y ∈ closure K := subset_closure hy
  have hm := hK.openSegment_interior_closure_subset_interior hz hy'
  have hden : 0 < 1 - 2 * τ := by linarith
  refine hm ⟨-2 * τ / (1 - 2 * τ), 1 / (1 - 2 * τ), ?_, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) hden
  · exact div_pos one_pos hden
  · field_simp; ring
  · rw [hyτ]
    have h1 : (-2 * τ / (1 - 2 * τ)) • (P + (1 / 2 : ℝ) • d) + (1 / (1 - 2 * τ)) • (P + τ • d)
        = ((-2 * τ / (1 - 2 * τ)) + (1 / (1 - 2 * τ))) • P
          + ((-2 * τ / (1 - 2 * τ)) * (1 / 2) + (1 / (1 - 2 * τ)) * τ) • d := by module
    rw [h1]
    have h2 : (-2 * τ / (1 - 2 * τ)) + (1 / (1 - 2 * τ)) = 1 := by field_simp; ring
    have h3 : (-2 * τ / (1 - 2 * τ)) * (1 / 2) + (1 / (1 - 2 * τ)) * τ = 0 := by field_simp; ring
    rw [h2, h3]; simp

/-- the other end: reflect -/
theorem end_not_beyond' {K : Set Plane} (hK : Convex ℝ K) {P d y : Plane} (hd : d ≠ 0)
    (hz : P + (1 / 2 : ℝ) • d ∈ interior K) (hy : y ∈ K) (τ : ℝ) (hτ : 1 < τ)
    (hyτ : y = P + τ • d) : P + d ∈ interior K := by
  have hy' : y ∈ closure K := subset_closure hy
  have hm := hK.openSegment_interior_closure_subset_interior hz hy'
  have hden : 0 < 2 * τ - 1 := by linarith
  refine hm ⟨(2 * τ - 2) / (2 * τ - 1), 1 / (2 * τ - 1), ?_, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) hden
  · exact div_pos one_pos hden
  · field_simp; ring
  · rw [hyτ]
    have h1 : ((2 * τ - 2) / (2 * τ - 1)) • (P + (1 / 2 : ℝ) • d) + (1 / (2 * τ - 1)) • (P + τ • d)
        = (((2 * τ - 2) / (2 * τ - 1)) + (1 / (2 * τ - 1))) • P
          + (((2 * τ - 2) / (2 * τ - 1)) * (1 / 2) + (1 / (2 * τ - 1)) * τ) • d := by module
    rw [h1]
    have h2 : ((2 * τ - 2) / (2 * τ - 1)) + (1 / (2 * τ - 1)) = 1 := by field_simp; ring
    have h3 : ((2 * τ - 2) / (2 * τ - 1)) * (1 / 2) + (1 / (2 * τ - 1)) * τ = 1 := by field_simp; ring
    rw [h2, h3]; simp

/-- **A point of the line in the target lies in `[P,Q]`.** -/
theorem line_target_subset {K : Set Plane} (hK : Convex ℝ K) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg : g ≠ 0)
    {P Q : Plane} (hPQ : P ≠ Q) (hP : g P = c) (hQ : g Q = c)
    (hint : openSegment ℝ P Q ⊆ interior K)
    (hPf : P ∉ interior K) (hQf : Q ∉ interior K)
    {y : Plane} (hy : y ∈ K) (hgy : g y = c) : y ∈ segment ℝ P Q := by
  set d : Plane := Q - P with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
  have hmid : P + (1 / 2 : ℝ) • d ∈ interior K := by
    apply hint
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hd]; module
  have hn := rotVec_ne_zero hg
  have hc1 : cross (rotVec g) (y - P) = 0 := by
    rw [← rotVec_spec, map_sub, hgy, hP, sub_self]
  have hc2 : cross (rotVec g) d = 0 := by
    rw [← rotVec_spec, hd, map_sub, hQ, hP, sub_self]
  have hcr := cross_eq_zero_of_common_ker hn hc2 hc1
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hd0 hcr
  have hyτ : y = P + τ • d := by rw [← hτ]; abel
  rcases lt_trichotomy τ 0 with h | h | h
  · exact absurd (end_not_beyond hK hd0 hmid hy τ h hyτ) hPf
  · rw [h, zero_smul, add_zero] at hyτ; rw [hyτ]; exact left_mem_segment ℝ P Q
  · rcases le_or_gt τ 1 with h1 | h1
    · rw [segment_eq_image_lineMap]
      refine ⟨τ, ⟨h.le, h1⟩, ?_⟩
      rw [hyτ, AffineMap.lineMap_apply]
      simp [hd]; abel
    · have := end_not_beyond' hK hd0 hmid hy τ h1 hyτ
      have hQe : P + d = Q := by rw [hd]; abel
      rw [hQe] at this
      exact absurd this hQf

/-- **Chain edges lie in `[P,Q]` when the ends are frontier points.** -/
theorem chain_sub_of_frontier {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg : g ≠ 0)
    {P Q : Plane} (hPQ : P ≠ Q)
    (hS : segment ℝ P Q ⊆ {y | g y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hPf : P ∈ frontier D.target.carrier) (hQf : Q ∈ frontier D.target.carrier) :
    ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
  have hP : g P = c := hS (left_mem_segment ℝ P Q)
  have hQ : g Q = c := hS (right_mem_segment ℝ P Q)
  intro e he
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  have m1 := line_target_subset D.target.convex g c hg hPQ hP hQ hint hPf.2 hQf.2
    (Erdos634.MarchInduction.pts_mem_target D (e.1) (e.2)) h1
  have m2 := line_target_subset D.target.convex g c hg hPQ hP hQ hint hPf.2 hQf.2
    (Erdos634.MarchInduction.pts_mem_target D (e.1) (e.2 + 1)) h2
  exact (convex_segment P Q).segment_subset m1 m2

/-- **The far chain of an interior segment whose chain edges are known to stay inside it** (blocked ends: the line may continue
past an end as long as no far-side tile edge on it does). -/
theorem far_chain_blocked {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg : g ≠ 0)
    {P Q : Plane} (hPQ : P ≠ Q)
    (hS : segment ℝ P Q ⊆ {y | g y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hsub : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q) :
    (∑ e ∈ D.lineChain g c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P Q) ∧
    (∀ x ∈ openSegment ℝ P Q, x ∉ D.vertexSet → ∃ e ∈ D.lineChain g c, x ∈ (D.tile e.1).edge e.2) ∧
    (∀ e₁ ∈ D.lineChain g c, ∀ e₂ ∈ D.lineChain g c, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton) := by
  classical
  refine ⟨?_, fun x hx hxv => D.wall_cover g c hg hPQ hS hint hwall hx hxv, ?_⟩
  · have hpart := D.wall_partition g c hg hPQ hS hint hwall
    have h1 : ∑ e ∈ D.lineChain g c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile e.1).edge e.2 ∩ segment ℝ P Q)
        = ∑ e ∈ D.lineChain g c, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Set.inter_eq_left.mpr (hsub e he)]
      exact (D.tile e.1).hausdorff_edge e.2
    rw [h1, MeasureTheory.hausdorffMeasure_segment] at hpart
    have h2 : ENNReal.ofReal (∑ e ∈ D.lineChain g c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
        = ENNReal.ofReal (dist P Q) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg), ← edist_dist]
      calc _ = ∑ e ∈ D.lineChain g c, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
            Finset.sum_congr rfl fun e _ => (edist_dist _ _).symm
        _ = edist P Q := hpart
    exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun e _ => dist_nonneg) dist_nonneg).mp h2
  · intro e₁ h₁ e₂ h₂ hne
    obtain ⟨-, -, hle₁⟩ := Dissection.mem_lineChain.mp h₁
    obtain ⟨-, -, hle₂⟩ := Dissection.mem_lineChain.mp h₂
    exact D.sameside_edges_subsingleton g c hg hne
      ((D.tile e₁.1).carrier_subset_halfplane g c hle₁)
      ((D.tile e₂.1).carrier_subset_halfplane g c hle₂)
      (D.lineChain_edge_subset h₁) (D.lineChain_edge_subset h₂)

/-- **The far chain of an interior segment with frontier ends.** -/
theorem far_chain {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg : g ≠ 0)
    {P Q : Plane} (hPQ : P ≠ Q)
    (hS : segment ℝ P Q ⊆ {y | g y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hPf : P ∈ frontier D.target.carrier) (hQf : Q ∈ frontier D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) :
    (∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q) ∧
    (∑ e ∈ D.lineChain g c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P Q) ∧
    (∀ x ∈ openSegment ℝ P Q, x ∉ D.vertexSet → ∃ e ∈ D.lineChain g c, x ∈ (D.tile e.1).edge e.2) ∧
    (∀ e₁ ∈ D.lineChain g c, ∀ e₂ ∈ D.lineChain g c, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton) := by
  have hsub := chain_sub_of_frontier D g c hg hPQ hS hint hPf hQf
  exact ⟨hsub, far_chain_blocked D g c hg hPQ hS hint hwall hsub⟩

#print axioms far_chain
#print axioms far_chain_blocked
end Erdos634.Draft.ThmDRowFar
