import Mathlib.Tactic
import Erdos634.Draft.GLCChain

/-!
# The far chain of a doubled chord of length `2a` (two `a`-edges), first edge at the end

Used in G2, Case 1 (the chord `P₂Q₁` of length `2a`).

`far_edges_a`, `far_edge_at_end_a`: the `a`-version of `T30LL3Far.far_edges_c`/`far_edge_at_end` (there `c`, `SixtyData`): for a clamped, interior, wall chord `PQ` of length `2a`
with the word lemma `x a + y b + z c = 2a → (x,y,z) = (2,0,0)` (`GLCArith.hword_2a_real`), every far-chain edge has length `a`, and some far-chain tile has the edge `[P, midpoint P Q]`
(either order) with its third vertex strictly on the far side.  Same proof as the originals.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.ChordFar Erdos634.EdgeWordConversion Erdos634.LineParam Erdos634.TPErdos Erdos634.Pi3L3

theorem far_edges_a {N : ℕ} (D : CongruentDissection N) {a b c : ℝ}
    (hsides : ∀ i : Fin 3, sideLen D i = a ∨ sideLen D i = b ∨ sideLen D i = c)
    (hword2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = 2 * a → x = 2 ∧ y = 0 ∧ z = 0)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c0 : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c0) (hfQ : f Q = c0)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = 2 * a) :
    ∀ e ∈ D.lineChain (-f) (-c0),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a := by
  have hcnt := far_chain_counts D (x0 := 2) (y0 := 0) (z0 := 0) hsides
    (fun x y z hxyz => hword2 x y z hxyz)
    f hf c0 hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall hdist
  obtain ⟨-, h2, h3⟩ := hcnt
  simp only at h2 h3
  intro e he
  by_contra n1
  by_cases n2 : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b
  · have : e ∈ (D.lineChain (-f) (-c0)).filter (fun e => dist ((D.tile e.1).pts e.2)
        ((D.tile e.1).pts (e.2 + 1)) ≠ a ∧ dist ((D.tile e.1).pts e.2)
        ((D.tile e.1).pts (e.2 + 1)) = b) := Finset.mem_filter.mpr ⟨he, n1, n2⟩
    rw [Finset.card_eq_zero.mp h2] at this; simp at this
  · have : e ∈ (D.lineChain (-f) (-c0)).filter (fun e => dist ((D.tile e.1).pts e.2)
        ((D.tile e.1).pts (e.2 + 1)) ≠ a ∧ dist ((D.tile e.1).pts e.2)
        ((D.tile e.1).pts (e.2 + 1)) ≠ b) := Finset.mem_filter.mpr ⟨he, n1, n2⟩
    rw [Finset.card_eq_zero.mp h3] at this; simp at this

theorem far_edge_at_end_a {N : ℕ} (D : CongruentDissection N) {a b c : ℝ}
    (hsides : ∀ i : Fin 3, sideLen D i = a ∨ sideLen D i = b ∨ sideLen D i = c)
    (hword2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = 2 * a → x = 2 ∧ y = 0 ∧ z = 0)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c0 : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c0) (hfQ : f Q = c0)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = 2 * a) :
    ∃ (K : Fin N) (k : Fin 3),
      (((D.tile K).pts k = P ∧ (D.tile K).pts (k + 1) = midpoint ℝ P Q) ∨
        ((D.tile K).pts k = midpoint ℝ P Q ∧ (D.tile K).pts (k + 1) = P)) ∧
      (-f) ((D.tile K).pts (k + 2)) < -c0 ∧ (∀ i, (-f) ((D.tile K).pts i) ≤ -c0) := by
  classical
  have hcpos : 0 < a := by have := dist_pos.mpr hPQ; linarith
  have hf' : -f ≠ 0 := neg_ne_zero.mpr hf
  have hall := far_edges_a D hsides hword2 f hf c0 hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall hdist
  have hu : (-f) P = -c0 := by simp [hfP]
  have hv : (-f) Q = -c0 := by simp [hfQ]
  have hS' : segment ℝ P Q ⊆ {y | (-f) y = -c0} := by
    intro y hy
    have := segment_sub_level f c0 hfP hfQ hy
    simp only [Set.mem_setOf_eq] at this ⊢
    simp [this]
  have hcov := lineChain_covers_Icc' D.toDissection (-f) hf' (-c0) P Q hPQ hS' hint hwall
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  rw [← hcov] at h0
  simp only [Set.mem_iUnion, exists_prop] at h0
  obtain ⟨e, he, he0⟩ := h0
  have hsub := chain_edge_subset_chord D.toDissection (-f) hf' (-c0) hPQ hu hv g cg hg hgP hgQ h ch hh hhQ hhP he
  have hXE : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 := left_mem_segment ℝ _ _
  have hYE : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).edge e.2 := right_mem_segment ℝ _ _
  obtain ⟨hlk, hlk1, hle⟩ := Dissection.mem_lineChain.mp he
  have hlen := hall e he
  have hmid : (D.tile e.1).edge e.2 = segment ℝ P (midpoint ℝ P Q) := by
    rcases edgeParam_spec D.toDissection (-f) hf' (-c0) P Q hPQ he hu hv with ⟨hempty, -⟩ | ⟨hb1, hb2, htrace, hmeas⟩
    · exfalso
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) _ ⟨hXE, hsub hXE⟩
    · generalize edgeParam D.toDissection (-f) (-c0) P Q e = pr at he0 hb1 hb2 htrace hmeas
      obtain ⟨tp, tq⟩ := pr
      simp only at he0 hb1 hb2 htrace hmeas
      have hint' : (D.tile e.1).edge e.2 ∩ segment ℝ P Q = (D.tile e.1).edge e.2 := Set.inter_eq_left.mpr hsub
      rw [hint'] at htrace hmeas
      have hμ : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) ((D.tile e.1).edge e.2)
          = ENNReal.ofReal a := by
        have : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            (segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
            = edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := MeasureTheory.hausdorffMeasure_segment _ _
        rw [edist_dist, hlen] at this
        exact this
      rw [hμ] at hmeas
      have hn : |tp - tq| * (2 * a) = a := by
        have := (ENNReal.ofReal_eq_ofReal_iff hcpos.le (by positivity)).mp hmeas
        rw [hdist] at this; linarith
      have habs : |tp - tq| = 1 / 2 := by
        have : (|tp - tq| - 1 / 2) * (2 * a) = 0 := by linear_combination hn
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · exfalso; linarith
      have hmin : min tp tq ≤ 0 := he0.1
      have hz : (tp = 0 ∧ tq = 1 / 2) ∨ (tq = 0 ∧ tp = 1 / 2) := by
        rcases le_total tp tq with hle' | hle'
        · rw [min_eq_left hle'] at hmin
          have : tp = 0 := le_antisymm hmin hb1.1
          rw [this, zero_sub, abs_neg, abs_of_nonneg hb2.1] at habs
          exact Or.inl ⟨this, habs⟩
        · rw [min_eq_right hle'] at hmin
          have : tq = 0 := le_antisymm hmin hb2.1
          rw [this, sub_zero, abs_of_nonneg hb1.1] at habs
          exact Or.inr ⟨this, habs⟩
      have hlm : AffineMap.lineMap P Q (1 / 2 : ℝ) = midpoint ℝ P Q := by
        unfold midpoint; congr 1; simp [invOf_eq_inv]
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [htrace, h1, h2, hlm, AffineMap.lineMap_apply_zero]
      · rw [htrace, h1, h2, hlm, AffineMap.lineMap_apply_zero, segment_symm]
  have hdPM : dist P (midpoint ℝ P Q) = a := by
    have h2n : ‖(2 : ℝ)‖ = 2 := by simp
    rw [dist_left_midpoint (𝕜 := ℝ) P Q, hdist, h2n]; ring
  have hPM : P ≠ midpoint ℝ P Q := by
    intro hh'
    rw [← hh', dist_self] at hdPM
    linarith
  have hend := seg_endpoints hPM (hmid ▸ hXE) (hmid ▸ hYE) (by rw [hlen, hdPM])
  have hlast : (-f) ((D.tile e.1).pts (e.2 + 2)) < -c0 := by
    refine third_strict (D.tile e.1) (-f) hf' (-c0) ?_ e.2 hlk hlk1
    intro i; exact hle i
  refine ⟨e.1, e.2, ?_, hlast, hle⟩
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

end Erdos634.GLC

#print axioms Erdos634.GLC.far_edge_at_end_a
