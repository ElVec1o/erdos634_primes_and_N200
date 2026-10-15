import Mathlib.Tactic
import Erdos634.Draft.T30LL3Far

/-!
# The far chain of a chord whose end `Z` is an interior point of the target, with the line continuing into a tile

`chain_sum_open_end`: let `R ≠ Z` lie on the line `{f = c}`, `R` clamped by a supporting functional `g` of the target (`g R = cg`, `g Z < cg`), the open chord inside the target and a wall
(no tile interior meets it), and suppose the line just past `Z` runs into the interior of a tile (`hover`).  Then every chain edge meeting the chord lies inside it, and the chain edges
inside the chord have lengths summing to `|RZ|` (`ENNReal` form).  (`chain_edge_lengths_sum` needs both ends clamped; here `Z` is clamped by the tile instead.)
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.ChordFar Erdos634.TPErdos Erdos634.LineParam

theorem lineMap_between (R Z : Plane) (ty t τ : ℝ) (h1 : ty < τ) (h2 : τ ≤ t) :
    AffineMap.lineMap R Z τ ∈ segment ℝ (AffineMap.lineMap R Z ty) (AffineMap.lineMap R Z t) := by
  have hd : 0 < t - ty := by linarith
  refine ⟨(t - τ) / (t - ty), (τ - ty) / (t - ty), div_nonneg (by linarith) hd.le,
    div_nonneg (by linarith) hd.le, by field_simp; ring, ?_⟩
  ext i
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul]
  field_simp
  ring

open scoped Classical in
theorem chain_sum_open_end {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {R Z : Plane} (hRZ : R ≠ Z) (hfR : f R = c) (hfZ : f Z = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg) (hgR : g R = cg)
    (hgZ : g Z < cg)
    (hint : openSegment ℝ R Z ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ R Z, ∀ i, y ∉ interior (D.tile i).carrier)
    (hover : ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      ∃ i, AffineMap.lineMap R Z (1 + s) ∈ interior (D.tile i).carrier) :
    (∀ e ∈ D.lineChain f c, (∃ y, y ∈ (D.tile e.1).edge e.2 ∧ y ∈ segment ℝ R Z) →
        (D.tile e.1).edge e.2 ⊆ segment ℝ R Z) ∧
    ∑ e ∈ (D.lineChain f c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ R Z),
        ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist R Z) := by
  classical
  have hS := segment_sub_level f c hfR hfZ
  have hgl : ∀ τ : ℝ, g (AffineMap.lineMap R Z τ) = cg + τ * (g Z - cg) := by
    intro τ
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, map_add, map_smul, map_sub,
      smul_eq_mul, hgR]
    ring
  have hclaim : ∀ e ∈ D.lineChain f c, (∃ y, y ∈ (D.tile e.1).edge e.2 ∧ y ∈ segment ℝ R Z) →
      (D.tile e.1).edge e.2 ⊆ segment ℝ R Z := by
    intro e he ⟨y, hye, hyS⟩ x hx
    by_contra hxS
    obtain ⟨s0, hs0, hover'⟩ := hover
    have hfx := D.lineChain_edge_subset he x hx
    have hfy := D.lineChain_edge_subset he y hye
    have hxT : x ∈ D.target.carrier := Erdos634.BaseSelection.tile_subset_target D e.1
      ((D.tile e.1).edge_subset_carrier e.2 hx)
    obtain ⟨t, rfl⟩ := line_eq_lineMap f hf c hfR hfZ hRZ hfx
    obtain ⟨ty, rfl⟩ := line_eq_lineMap f hf c hfR hfZ hRZ hfy
    have ht0 : 0 ≤ t := by
      have := hg _ hxT
      rw [hgl] at this
      nlinarith
    have hty : 0 ≤ ty ∧ ty ≤ 1 := by
      rw [segment_eq_image_lineMap] at hyS
      obtain ⟨u, hu, hu'⟩ := hyS
      have := lineMap_injective_of_ne hRZ hu'
      rw [← this]; exact hu
    have ht1 : 1 < t := by
      by_contra hle
      push_neg at hle
      exact hxS (by rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht0, hle⟩, rfl⟩)
    obtain ⟨i, hi⟩ := hover' (min s0 (t - 1)) (lt_min hs0 (by linarith)) (min_le_left _ _)
    have hw : AffineMap.lineMap R Z (1 + min s0 (t - 1)) ∈ (D.tile e.1).edge e.2 := by
      have hconv : Convex ℝ ((D.tile e.1).edge e.2) := convex_segment _ _
      exact hconv.segment_subset hye hx
        (lineMap_between R Z ty t _ (by have := lt_min hs0 (by linarith : (0 : ℝ) < t - 1); linarith)
          (by have := min_le_right s0 (t - 1); linarith))
    exact D.edge_point_not_interior hw i hi
  refine ⟨hclaim, ?_⟩
  have hpart := D.wall_partition f c hf hRZ hS hint hwall
  rw [← Finset.sum_filter_add_sum_filter_not (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ R Z)] at hpart
  have h0 : ∑ e ∈ (D.lineChain f c).filter (fun e => ¬ (D.tile e.1).edge e.2 ⊆ segment ℝ R Z),
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        ((D.tile e.1).edge e.2 ∩ segment ℝ R Z) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨heC, hns⟩ := Finset.mem_filter.mp he
    have : (D.tile e.1).edge e.2 ∩ segment ℝ R Z = ∅ := by
      by_contra hne
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact hns (hclaim e heC ⟨y, hy.1, hy.2⟩)
    rw [this]; simp
  rw [h0, add_zero, MeasureTheory.hausdorffMeasure_segment, edist_dist] at hpart
  rw [← hpart]
  refine Finset.sum_congr rfl fun e he => ?_
  have hsub := (Finset.mem_filter.mp he).2
  rw [Set.inter_eq_self_of_subset_left hsub]
  show _ = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
    (segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  rw [MeasureTheory.hausdorffMeasure_segment, edist_dist]

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.chain_sum_open_end
