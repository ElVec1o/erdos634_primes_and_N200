import Mathlib.Tactic
import Erdos634.Draft.ThmDHalfFan
import Erdos634.EdgeChain

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D': no tile straddles an interior segment; the far-side fan at a vertex of the segment  

Companion of `ThmDHalfFan`.  The hypotheses of `halfplane_junction_fan` (`hS`, `hout`) are discharged from
the covering of the line near `p` by tiles that lie in the closed *right* half plane:

* `interior_overlap` — a point of the carrier of tile `i` that is an interior point of tile `j` forces `i = j`;
* `not_straddle`     — if the line `(p,u)` near `p` is covered by tiles lying in the right half plane, then every
  tile either lies (near `p`) in the left half plane or has null trace on it;
* `farside_fan_vertex` — the fan of the left-side tiles at `p`: two distinct left tiles with prescribed angles at
  `p` leave a residue forming a `Fan`;
* `hcov_of_segments` — the covering hypothesis from two near tiles holding `[p-u, p]` and `[p, p+u]`.
-/

open MeasureTheory Set Metric

namespace Erdos634.Draft.ThmDHalf

open Erdos634.Geometry Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

theorem convex_leftHP (p u : Plane) : Convex ℝ (LeftHP p u) := by
  intro x hx y hy a b ha hb hab
  simp only [LeftHP, mem_setOf_eq] at *
  have h : a • x + b • y - p = a • (x - p) + b • (y - p) := by
    obtain rfl : b = 1 - a := by linarith
    module
  rw [h, cross_add_right, cross_smul_right, cross_smul_right]
  have := mul_nonneg ha hx
  have := mul_nonneg hb hy
  linarith

theorem convex_rightHP (p u : Plane) : Convex ℝ (RightHP p u) := by
  intro x hx y hy a b ha hb hab
  simp only [RightHP, mem_setOf_eq] at *
  have h : a • x + b • y - p = a • (x - p) + b • (y - p) := by
    obtain rfl : b = 1 - a := by linarith
    module
  rw [h, cross_add_right, cross_smul_right, cross_smul_right]
  have := mul_nonpos_of_nonneg_of_nonpos ha hx
  have := mul_nonpos_of_nonneg_of_nonpos hb hy
  linarith

/-- A tile whose three vertices lie in a convex set lies in it. -/
theorem carrier_subset_of_pts {S : Set Plane} (hS : Convex ℝ S) (T : Tri) (h : ∀ k, T.pts k ∈ S) :
    T.carrier ⊆ S := by
  unfold Tri.carrier
  exact convexHull_min (by rintro _ ⟨k, rfl⟩; exact h k) hS

/-- **A point of tile `i`'s carrier cannot be an interior point of another tile.** -/
theorem interior_overlap {N : ℕ} (D : Dissection N) {i j : Fin N} {c : Plane}
    (hi : c ∈ (D.tile i).carrier) (hj : c ∈ interior (D.tile j).carrier) : i = j := by
  by_contra hij
  have hcl : c ∈ closure (interior (D.tile i).carrier) := by
    rw [(D.tile i).convex.closure_interior_eq_closure_of_nonempty_interior (D.tile i).interior_nonempty,
      (D.tile i).isCompact.isClosed.closure_eq]
    exact hi
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl _ isOpen_interior hj
  exact (D.interiors_disjoint hij).le_bot ⟨hy2, hy1⟩ |>.elim

/-- **No tile straddles the line.** -/
theorem not_straddle {N : ℕ} (D : Dissection N) (p u : Plane) (hu : u ≠ 0) {r0 : ℝ}
    (hcov : ∀ c : Plane, cross u (c - p) = 0 → c ∈ ball p r0 →
      ∃ j, c ∈ (D.tile j).carrier ∧ (D.tile j).carrier ⊆ RightHP p u)
    (i : Fin N) :
    (D.tile i).carrier ∩ ball p r0 ⊆ LeftHP p u ∨
      volume ((D.tile i).carrier ∩ ball p r0 ∩ LeftHP p u) = 0 := by
  classical
  by_cases hsub : (D.tile i).carrier ∩ ball p r0 ⊆ LeftHP p u
  · exact Or.inl hsub
  right
  obtain ⟨y, ⟨hyT, hyB⟩, hyL⟩ := not_subset.mp hsub
  have hy0 : cross u (y - p) < 0 := by
    simp only [LeftHP, mem_setOf_eq, not_le] at hyL; exact hyL
  by_contra hpos
  -- an interior point strictly on the left
  have hex : ∃ z ∈ (D.tile i).carrier ∩ ball p r0 ∩ LeftHP p u,
      z ∉ (frontier (D.tile i).carrier ∪ {y : Plane | cross u (y - p) = 0}) := by
    by_contra hno
    push_neg at hno
    apply hpos
    refine measure_mono_null hno ?_
    exact measure_union_null (D.tile i).volume_frontier (volume_line_null p u hu)
  obtain ⟨z, ⟨⟨hzT, hzB⟩, hzL⟩, hzn⟩ := hex
  have hzint : z ∈ interior (D.tile i).carrier := by
    by_contra hni
    exact hzn (Or.inl ⟨subset_closure hzT, hni⟩)
  have hz0 : 0 < cross u (z - p) := by
    have h1 : 0 ≤ cross u (z - p) := hzL
    have h2 : cross u (z - p) ≠ 0 := fun h => hzn (Or.inr h)
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  set cz := cross u (z - p) with hcz
  set cy := cross u (y - p) with hcy
  set t : ℝ := cz / (cz - cy) with ht
  have hden : 0 < cz - cy := by linarith
  have ht0 : 0 < t := div_pos hz0 hden
  have ht1 : t < 1 := by rw [ht, div_lt_one hden]; linarith
  set c : Plane := (1 - t) • z + t • y with hc
  have hcm : c ∈ openSegment ℝ z y := ⟨1 - t, t, by linarith, ht0, by ring, rfl⟩
  have hcint : c ∈ interior (D.tile i).carrier :=
    (D.tile i).convex.openSegment_interior_closure_subset_interior hzint (subset_closure hyT) hcm
  have hcB : c ∈ ball p r0 := (convex_ball p r0).openSegment_subset hzB hyB hcm
  have hcross : cross u (c - p) = 0 := by
    have h : c - p = (1 - t) • (z - p) + t • (y - p) := by rw [hc]; module
    rw [h, cross_add_right, cross_smul_right, cross_smul_right]
    have : (1 - t) * cz + t * cy = 0 := by
      rw [ht]; field_simp; ring
    simpa [hcz, hcy] using this
  obtain ⟨j, hcj, hjR⟩ := hcov c hcross hcB
  have hji : j = i := interior_overlap D hcj hcint
  subst hji
  have := hjR hzT
  simp only [RightHP, mem_setOf_eq] at this
  linarith

/-- The line near `p` lies in `[p-u, p] ∪ [p, p+u]`. -/
theorem line_near_mem_segment (p u : Plane) (hu : u ≠ 0) {c : Plane} (hc : cross u (c - p) = 0)
    (hd : dist c p < ‖u‖) : c ∈ segment ℝ p (p + u) ∨ c ∈ segment ℝ (p - u) p := by
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hu hc
  have hcp : c = p + τ • u := by rw [← hτ]; abel
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hτ1 : |τ| < 1 := by
    rw [dist_eq_norm, hcp, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hd
    by_contra h
    push_neg at h
    nlinarith [abs_nonneg τ]
  rcases le_total 0 τ with h0 | h0
  · left
    refine ⟨1 - τ, τ, by rw [abs_of_nonneg h0] at hτ1; linarith, h0, by ring, ?_⟩
    rw [hcp]; module
  · right
    have hs : 0 ≤ -τ := by linarith
    refine ⟨-τ, 1 + τ, hs, by rw [abs_of_nonpos h0] at hτ1; linarith, by ring, ?_⟩
    rw [hcp]; module

/-- The covering hypothesis from two near tiles holding `[p-u,p]` and `[p,p+u]`. -/
theorem hcov_of_segments {N : ℕ} (D : Dissection N) (p u : Plane) (hu : u ≠ 0) {r0 : ℝ}
    (hr0 : r0 ≤ ‖u‖) (t1 t2 : Fin N)
    (h1p : p ∈ (D.tile t1).carrier) (h1u : p + u ∈ (D.tile t1).carrier)
    (h2p : p ∈ (D.tile t2).carrier) (h2u : p - u ∈ (D.tile t2).carrier)
    (hR1 : (D.tile t1).carrier ⊆ RightHP p u) (hR2 : (D.tile t2).carrier ⊆ RightHP p u) :
    ∀ c : Plane, cross u (c - p) = 0 → c ∈ ball p r0 →
      ∃ j, c ∈ (D.tile j).carrier ∧ (D.tile j).carrier ⊆ RightHP p u := by
  intro c hc hcB
  have hd : dist c p < ‖u‖ := lt_of_lt_of_le (mem_ball.mp hcB) hr0
  rcases line_near_mem_segment p u hu hc hd with h | h
  · exact ⟨t1, (D.tile t1).convex.segment_subset h1p h1u h, hR1⟩
  · exact ⟨t2, (D.tile t2).convex.segment_subset h2u h2p h, hR2⟩

/-- **The far-side fan at a point of an interior line.** -/
theorem farside_fan_vertex {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi)
    (p u : Plane) (hu : u ≠ 0) {r0 : ℝ} (hr0 : 0 < r0)
    (hball : ball p r0 ⊆ D.target.carrier)
    (hcov : ∀ c : Plane, cross u (c - p) = 0 → c ∈ ball p r0 →
      ∃ j, c ∈ (D.tile j).carrier ∧ (D.tile j).carrier ⊆ RightHP p u)
    (tW tE : Fin N) (hWE : tW ≠ tE)
    (hWL : (D.tile tW).carrier ⊆ LeftHP p u) (hEL : (D.tile tE).carrier ⊆ LeftHP p u)
    (a a' : Ang)
    (hWa : (D.tile tW).localAngle p = angVal α a) (hEa : (D.tile tE).localAngle p = angVal α a') :
    ∃ m : Cnt, Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m) := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter fun i => (D.tile i).carrier ∩ ball p r0 ⊆ LeftHP p u
  have hmemS : ∀ i, i ∈ S ↔ (D.tile i).carrier ∩ ball p r0 ⊆ LeftHP p u := by
    intro i; simp [S]
  refine halfplane_junction_fan D model hcong α hirr hA0 hA1 hA2 hα h3α p u hu hr0
    (fun y hy => hball hy.2) S (fun i hi => (hmemS i).mp hi) ?_ tW tE
    ((hmemS tW).mpr (fun y hy => hWL hy.1)) ((hmemS tE).mpr (fun y hy => hEL hy.1)) hWE a a' hWa hEa
  intro i hi
  rcases not_straddle D p u hu hcov i with h | h
  · exact absurd ((hmemS i).mpr h) hi
  · exact h

/-! ### The combinatorial core of the row step -/

/-- Lower and upper end angles of the far tile across an `a`-edge: `D` is `(γ, β)`, the mirror `N` is `(β, γ)`. -/
def lowA (b : Bool) : Ang := if b then Ang.ga else Ang.be
def upA (b : Bool) : Ang := if b then Ang.be else Ang.ga

/-- **Row orientation (combinatorial).**  `T i = true` means the far tile across `e_i` is `D`.  The fans at the
interior diagonal vertices force consecutive tiles to have the same type; the fan at the end `P` (where the near tile
has `γ`) forces the first to be `D`. -/
theorem row_orient_comb (w : ℕ) (T : ℕ → Bool)
    (hmid : ∀ i, i + 1 < w → ∃ m : Cnt, Fan (Cnt.add (Cnt.add (lowA (T i)).cnt (upA (T (i + 1))).cnt) m))
    (hP : 0 < w → ∃ m : Cnt, Fan (Cnt.add (Cnt.add Ang.ga.cnt (upA (T 0)).cnt) m)) :
    ∀ i, i < w → T i = true := by
  have h0 : 0 < w → T 0 = true := by
    intro hw
    obtain ⟨m, hm⟩ := hP hw
    by_contra hF
    have : T 0 = false := by simpa using hF
    rw [this] at hm
    exact no_two_gamma _ _ m hm ⟨rfl, rfl⟩
  have hstep : ∀ i, i + 1 < w → T i = true → T (i + 1) = true := by
    intro i hi hT
    obtain ⟨m, hm⟩ := hmid i hi
    by_contra hF
    have : T (i + 1) = false := by simpa using hF
    rw [hT, this] at hm
    exact no_two_gamma _ _ m hm ⟨rfl, rfl⟩
  intro i hi
  induction i with
  | zero => exact h0 hi
  | succ k ih => exact hstep k hi (ih (by omega))

/-- Negative control: the mixed pair (D below, N above) is a fan violation as well (`β + β`). -/
theorem mixed_pair_forbidden (m : Cnt) :
    ¬ Fan (Cnt.add (Cnt.add (lowA false).cnt (upA true).cnt) m) := fun h =>
  no_two_beta _ _ m h ⟨rfl, rfl⟩

/-- Witness: the all-`D` row satisfies every fan hypothesis (`γ + β + α·... ` completes to a `Fan`). -/
theorem row_orient_witness (w : ℕ) :
    (∀ i, i + 1 < w → ∃ m : Cnt, Fan (Cnt.add (Cnt.add (lowA ((fun _ => true) i)).cnt
      (upA ((fun _ => true) (i + 1))).cnt) m)) ∧
    (0 < w → ∃ m : Cnt, Fan (Cnt.add (Cnt.add Ang.ga.cnt (upA ((fun _ => true) 0)).cnt) m)) := by
  refine ⟨fun i _ => ⟨(1, 0, 0), ?_⟩, fun _ => ⟨(1, 0, 0), ?_⟩⟩ <;>
    simp [Fan, Cnt.add, lowA, upA, Ang.cnt]

#print axioms interior_overlap
#print axioms not_straddle
#print axioms hcov_of_segments
#print axioms farside_fan_vertex
#print axioms row_orient_comb
#print axioms mixed_pair_forbidden
#print axioms row_orient_witness
end Erdos634.Draft.ThmDHalf
