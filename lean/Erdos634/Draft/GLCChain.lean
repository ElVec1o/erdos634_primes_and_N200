import Mathlib.Tactic
import Erdos634.Draft.T30LL4Chain
import Erdos634.Draft.GLCReflect

/-!
# Far chains for G2: open-ended chord with a weak "no edge crosses `Z`" hypothesis; the `2a` chord

* `chain_sum_open_end'`: `chain_sum_open_end` (T30LL4Chain) with the hypothesis `hover` (the line past `Z` runs into a tile interior) replaced by the weaker
  `hclaim`: every chain edge meeting the OPEN chord `(R,Z)` lies inside `[R,Z]` (edges only touching at `Z` are allowed).  Conclusion: the chain edges inside the chord have lengths summing to `|RZ|`.
* `open_chain_counts`: with edge lengths in `{s0,s1,s2}` and a word lemma, the inside edges have the prescribed counts.
* `far_edge_at_end_a`: the `2a` analogue of `far_edge_at_end`: a clamped interior wall chord `PQ` of length `2 s0` whose only representation is `2 s0` (two `s0`-edges):
  some far-chain tile has the edge `[P, midpoint P Q]`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.ChordFar Erdos634.TPErdos Erdos634.LineParam Erdos634.C2Forward
open Erdos634.EdgeWordConversion Erdos634.Pi3L3

open scoped Classical in
theorem chain_sum_open_end' {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {R Z : Plane} (hRZ : R ≠ Z) (hfR : f R = c) (hfZ : f Z = c)
    (hint : openSegment ℝ R Z ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ R Z, ∀ i, y ∉ interior (D.tile i).carrier)
    (hclaim : ∀ e ∈ D.lineChain f c, (∃ y, y ∈ (D.tile e.1).edge e.2 ∧ y ∈ openSegment ℝ R Z) →
        (D.tile e.1).edge e.2 ⊆ segment ℝ R Z) :
    ∑ e ∈ (D.lineChain f c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ R Z),
        ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist R Z) := by
  classical
  have hS := segment_sub_level f c hfR hfZ
  have hpart := D.wall_partition f c hf hRZ hS hint hwall
  rw [← Finset.sum_filter_add_sum_filter_not (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ R Z)] at hpart
  have h0 : ∑ e ∈ (D.lineChain f c).filter (fun e => ¬ (D.tile e.1).edge e.2 ⊆ segment ℝ R Z),
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        ((D.tile e.1).edge e.2 ∩ segment ℝ R Z) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨heC, hns⟩ := Finset.mem_filter.mp he
    have hsub : (D.tile e.1).edge e.2 ∩ segment ℝ R Z ⊆ {R, Z} := by
      intro y hy
      by_contra hyn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hyn
      have hyo : y ∈ openSegment ℝ R Z := by
        rw [← insert_endpoints_openSegment] at hy
        rcases hy.2 with h | h | h
        · exact absurd h hyn.1
        · exact absurd h hyn.2
        · exact h
      exact hns (hclaim e heC ⟨y, hy.1, hyo⟩)
    refine MeasureTheory.measure_mono_null hsub ?_
    have h1 : dimH ({R, Z} : Set Plane) < ((1 : NNReal) : ENNReal) := by
      rw [dimH_countable (Set.toFinite _).countable]; simp
    have h2 := hausdorffMeasure_of_dimH_lt h1
    simpa using h2
  rw [h0, add_zero, MeasureTheory.hausdorffMeasure_segment, edist_dist] at hpart
  rw [← hpart]
  refine Finset.sum_congr rfl fun e he => ?_
  have hsub := (Finset.mem_filter.mp he).2
  rw [Set.inter_eq_self_of_subset_left hsub]
  show _ = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
    (segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  rw [MeasureTheory.hausdorffMeasure_segment, edist_dist]


open scoped Classical in
theorem open_chain_counts {N : ℕ} (D : CongruentDissection N) {s0 s1 s2 L : ℝ} {x0 y0 z0 : ℕ}
    (hsides : ∀ i : Fin 3, sideLen D i = s0 ∨ sideLen D i = s1 ∨ sideLen D i = s2)
    (hword : ∀ x y z : ℕ, (x : ℝ) * s0 + y * s1 + z * s2 = L → x = x0 ∧ y = y0 ∧ z = z0)
    (hL : 0 ≤ L) (S : Finset (Fin N × Fin 3))
    (hsum : ∑ e ∈ S, ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal L) :
    let len : Fin N × Fin 3 → ℝ := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
    (S.filter (fun e => len e = s0)).card = x0 ∧
    (S.filter (fun e => len e ≠ s0 ∧ len e = s1)).card = y0 ∧
    (S.filter (fun e => len e ≠ s0 ∧ len e ≠ s1)).card = z0 := by
  intro len
  have hnn : ∀ e ∈ S, 0 ≤ len e := fun e _ => dist_nonneg
  rw [← ENNReal.ofReal_sum_of_nonneg hnn,
    ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg hnn) hL] at hsum
  have hmem : ∀ e ∈ S, len e = s0 ∨ len e = s1 ∨ len e = s2 := by
    intro e _
    rcases edge_length_trichotomy D e.1 e.2 with h' | h' | h'
    · simp only [len]; rw [h']; exact hsides 0
    · simp only [len]; rw [h']; exact hsides 1
    · simp only [len]; rw [h']; exact hsides 2
  have hc := letter_counts S len s0 s1 s2 hmem
  exact hword _ _ _ (by rw [← hc]; exact hsum)

end Erdos634.GLC
