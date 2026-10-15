import Mathlib.Tactic
import Erdos634.Draft.GLCChain
import Erdos634.Draft.T30LL4Tri

/-!
# Points just inside a tile past a relative-interior edge point

`hover_of_edge_rel_interior`: let `T` be a triangle, `k` an index, `f` a functional equal to `c0` at `T.pts k, T.pts (k+1)` and `> c0` at the third vertex, `Z` a point on the line `f = c0`
which is in the relative interior of the edge `[T.pts k, T.pts (k+1)]` (both barycentric coordinates `k`, `k+1` positive) and `u` a vector with `f u > 0`.
Then `Z + s u ∈ interior T` for all small `s > 0` (used: the line `Y Z` past `Z` runs into the interior of the far-chain tile whose edge passes through `Z`).
`relint_of_openSegment`: if `Z` lies in the open segment between two distinct points of the edge `[T.pts k, T.pts (k+1)]` then both coordinates `k, k+1` of `Z` are positive.
-/

namespace Erdos634.GLC

open Erdos634.Geometry

theorem coord_third (T : Tri) (k : Fin 3) (f : Plane →ₗ[ℝ] ℝ) (c0 : ℝ) (hk0 : f (T.pts k) = c0)
    (hk1 : f (T.pts (k + 1)) = c0) (hk2 : c0 < f (T.pts (k + 2))) (w : Plane) :
    T.basis.coord (k + 2) w = (f w - c0) / (f (T.pts (k + 2)) - c0) := by
  have hs := T.basis.sum_coord_apply_eq_one w
  have hl := T.basis.linear_combination_coord_eq_self w
  have hfw : f w = ∑ i, T.basis.coord i w * f (T.pts i) := by
    conv_lhs => rw [← hl]
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  have hpos : f (T.pts (k + 2)) - c0 ≠ 0 := by linarith
  rw [eq_div_iff hpos]
  rw [Fin.sum_univ_three] at hs hfw
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue] at hk0 hk1 hk2 ⊢
    have e1 : (0 : Fin 3) + 1 = 1 := rfl
    have e2 : (0 : Fin 3) + 2 = 2 := rfl
    rw [e1] at hk1; rw [e2] at hk2 ⊢
    rw [hk0, hk1] at hfw
    rw [hfw]; linear_combination (-c0) * hs
  · simp only [Fin.mk_one, Fin.isValue] at hk0 hk1 hk2 ⊢
    have e1 : (1 : Fin 3) + 1 = 2 := rfl
    have e2 : (1 : Fin 3) + 2 = 0 := rfl
    rw [e1] at hk1; rw [e2] at hk2 ⊢
    rw [hk0, hk1] at hfw
    rw [hfw]; linear_combination (-c0) * hs
  · have e1 : (2 : Fin 3) + 1 = 0 := rfl
    have e2 : (2 : Fin 3) + 2 = 1 := rfl
    simp only [Fin.reduceFinMk, Fin.isValue] at hk0 hk1 hk2 ⊢
    rw [e1] at hk1; rw [e2] at hk2 ⊢
    rw [hk0, hk1] at hfw
    rw [hfw]; linear_combination (-c0) * hs

theorem hover_of_edge_rel_interior (T : Tri) (k : Fin 3) (f : Plane →ₗ[ℝ] ℝ) (c0 : ℝ)
    (hk0 : f (T.pts k) = c0) (hk1 : f (T.pts (k + 1)) = c0) (hk2 : c0 < f (T.pts (k + 2)))
    {Z u : Plane} (hZ0 : 0 < T.basis.coord k Z) (hZ1 : 0 < T.basis.coord (k + 1) Z)
    (hfZ : f Z = c0) (hfu : 0 < f u) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 → Z + s • u ∈ interior T.carrier := by
  have hint : interior T.carrier = {x | ∀ i, 0 < T.basis.coord i x} := by
    have : T.carrier = convexHull ℝ (Set.range (T.basis : Fin 3 → Plane)) := rfl
    rw [this]
    exact AffineBasis.interior_convexHull T.basis
  have hcont : ∀ i : Fin 3, Continuous fun s : ℝ => T.basis.coord i (Z + s • u) := by
    intro i
    exact (AffineMap.continuous_of_finiteDimensional (T.basis.coord i)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hev : ∀ᶠ s in nhds (0 : ℝ), 0 < T.basis.coord k (Z + s • u) ∧ 0 < T.basis.coord (k + 1) (Z + s • u) := by
    refine Filter.Eventually.and ?_ ?_
    · have := (hcont k).continuousAt (x := 0)
      exact this.eventually (lt_mem_nhds (by simpa using hZ0))
    · have := (hcont (k + 1)).continuousAt (x := 0)
      exact this.eventually (lt_mem_nhds (by simpa using hZ1))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by positivity, fun s hs hsle => ?_⟩
  rw [hint]
  have hmem := hball (y := s) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; linarith)
  have hcov : ∀ m t : Fin 3, t = m ∨ t = m + 1 ∨ t = m + 2 := by decide
  intro i
  rcases hcov k i with rfl | rfl | rfl
  · exact hmem.1
  · exact hmem.2
  · rw [coord_third T k f c0 hk0 hk1 hk2, map_add, map_smul, hfZ, smul_eq_mul]
    apply div_pos _ (by linarith)
    have := mul_pos hs hfu
    linarith

theorem relint_of_openSegment (T : Tri) (k : Fin 3) {y x Z : Plane}
    (hy : y ∈ segment ℝ (T.pts k) (T.pts (k + 1))) (hx : x ∈ segment ℝ (T.pts k) (T.pts (k + 1)))
    (hyx : y ≠ x) (hZ : Z ∈ openSegment ℝ y x) :
    0 < T.basis.coord k Z ∧ 0 < T.basis.coord (k + 1) Z := by
  obtain ⟨a1, b1, ha1, hb1, hab1, rfl⟩ := hy
  obtain ⟨a2, b2, ha2, hb2, hab2, rfl⟩ := hx
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hZ
  have hform : s • (a1 • T.pts k + b1 • T.pts (k + 1)) + t • (a2 • T.pts k + b2 • T.pts (k + 1))
      = (s * a1 + t * a2) • T.pts k + (s * b1 + t * b2) • T.pts (k + 1) + (0 : ℝ) • T.pts (k + 2) := by
    module
  have hsum : (s * a1 + t * a2) + (s * b1 + t * b2) + 0 = 1 := by
    have : (s * a1 + t * a2) + (s * b1 + t * b2) = s * (a1 + b1) + t * (a2 + b2) := by ring
    rw [add_zero, this, hab1, hab2]; linarith
  rw [hform, Erdos634.C2Forward.coord_comb3 T k k _ _ _ hsum, Erdos634.C2Forward.coord_comb3 T k (k + 1) _ _ _ hsum]
  have n1 : k ≠ k + 1 := (by decide : ∀ x : Fin 3, x ≠ x + 1) k
  have n2 : k ≠ k + 2 := (by decide : ∀ x : Fin 3, x ≠ x + 2) k
  have n3 : k + 1 ≠ k := (by decide : ∀ x : Fin 3, x + 1 ≠ x) k
  have n4 : k + 1 ≠ k + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k
  simp only [if_true, if_neg n1, if_neg n2, if_neg n3, if_neg n4]
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have h1 : s * a1 + t * a2 ≤ 0 := by linarith [mul_zero (0 : ℝ)]
    have ha1' : a1 = 0 := by nlinarith [mul_nonneg hs.le ha1, mul_nonneg ht.le ha2, mul_pos hs ht]
    have ha2' : a2 = 0 := by nlinarith [mul_nonneg hs.le ha1, mul_nonneg ht.le ha2, mul_pos hs ht]
    apply hyx
    have : b1 = 1 := by linarith
    have : b2 = 1 := by linarith
    simp [ha1', ha2', *]
  · by_contra hcon
    have h1 : s * b1 + t * b2 ≤ 0 := by linarith [mul_zero (0 : ℝ)]
    have hb1' : b1 = 0 := by nlinarith [mul_nonneg hs.le hb1, mul_nonneg ht.le hb2, mul_pos hs ht]
    have hb2' : b2 = 0 := by nlinarith [mul_nonneg hs.le hb1, mul_nonneg ht.le hb2, mul_pos hs ht]
    apply hyx
    have : a1 = 1 := by linarith
    have : a2 = 1 := by linarith
    simp [hb1', hb2', *]

end Erdos634.GLC

#print axioms Erdos634.GLC.hover_of_edge_rel_interior
#print axioms Erdos634.GLC.relint_of_openSegment
