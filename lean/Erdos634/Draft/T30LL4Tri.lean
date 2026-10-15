import Mathlib.Tactic
import Erdos634.Draft.T30LL4Word

/-!
# Two triangle facts for (L4)

* `interior_of_three`: a strictly positive convex combination of the three vertices of a tile is an interior point of the tile.
* `wall_of_hull_func`: if the carrier of tile `j` is `convexHull {P,Q,Z}` and a functional is `c` on `Q, Z` and `≥ c` at `P`, the open segment `QZ` lies in no tile interior.
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry

theorem coord_comb3 (T : Tri) (m i : Fin 3) (x0 x1 x2 : ℝ) (h : x0 + x1 + x2 = 1) :
    T.basis.coord i (x0 • T.pts m + x1 • T.pts (m + 1) + x2 • T.pts (m + 2)) =
      x0 * (if i = m then 1 else 0) + x1 * (if i = m + 1 then 1 else 0) + x2 * (if i = m + 2 then 1 else 0) := by
  have hd : ∀ x, T.basis.coord i x = (T.basis.coord i).linear x + T.basis.coord i 0 :=
    fun x => by simpa using congrFun (AffineMap.decomp (T.basis.coord i)) x
  have hc : ∀ n : Fin 3, T.basis.coord i (T.pts n) = if i = n then 1 else 0 :=
    fun n => AffineBasis.coord_apply T.basis i n
  have hl : ∀ n : Fin 3, (T.basis.coord i).linear (T.pts n) = (if i = n then 1 else 0) - T.basis.coord i 0 := by
    intro n; have := hc n; rw [hd] at this; linarith
  rw [hd]
  simp only [map_add, map_smul, smul_eq_mul, hl]
  linear_combination (-(T.basis.coord i 0)) * h

theorem interior_of_three (T : Tri) (m : Fin 3) (x0 x1 x2 : ℝ) (h0 : 0 < x0) (h1 : 0 < x1) (h2 : 0 < x2)
    (h : x0 + x1 + x2 = 1) : x0 • T.pts m + x1 • T.pts (m + 1) + x2 • T.pts (m + 2) ∈ interior T.carrier := by
  have hint : interior T.carrier = {x | ∀ i, 0 < T.basis.coord i x} := by
    have : T.carrier = convexHull ℝ (Set.range (T.basis : Fin 3 → Plane)) := rfl
    rw [this]
    exact AffineBasis.interior_convexHull T.basis
  rw [hint]
  intro i
  show 0 < T.basis.coord i _
  rw [coord_comb3 T m i x0 x1 x2 h]
  fin_cases m <;> fin_cases i <;> simp <;> linarith

theorem wall_of_hull_func {N : ℕ} (D : Dissection N) (j : Fin N) {P Q Z : Plane}
    (hcar : (D.tile j).carrier = convexHull ℝ {P, Q, Z}) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hQ : f Q = c) (hZ : f Z = c) (hP : c ≤ f P) :
    ∀ y ∈ openSegment ℝ Q Z, ∀ i, y ∉ interior (D.tile i).carrier := by
  intro y hy i
  have hyseg : y ∈ segment ℝ Q Z := openSegment_subset_segment ℝ _ _ hy
  have hyj : y ∈ (D.tile j).carrier := by
    rw [hcar]
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp : Q ∈ ({P, Q, Z} : Set Plane)))
      (subset_convexHull ℝ _ (by simp : Z ∈ ({P, Q, Z} : Set Plane))) hyseg
  have hfy : f y = c := by
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hyseg
    simp only [map_add, map_smul, smul_eq_mul, hQ, hZ]
    rw [← add_mul, hst, one_mul]
  by_cases hij : i = j
  · subst hij
    intro hint
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hint
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hf (LinearMap.ext hcon)
    set w : Plane := (f v)⁻¹ • v with hw
    have hfw : f w = 1 := by rw [hw, map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
    set ε : ℝ := r / (2 * (‖w‖ + 1)) with hε
    have hεpos : 0 < ε := by positivity
    have hmem : y - ε • w ∈ Metric.ball y r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_pos hεpos, hε]
      have h1 : 0 < ‖w‖ + 1 := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w]
    have hin := interior_subset (hball hmem)
    rw [hcar] at hin
    have hsub : convexHull ℝ ({P, Q, Z} : Set Plane) ⊆ {x | c ≤ f x} := by
      refine convexHull_min ?_ ((convex_halfSpace_ge f.isLinear c))
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact hP
      · exact hQ.ge
      · exact hZ.ge
    have := hsub hin
    simp only [Set.mem_setOf_eq, map_sub, map_smul, smul_eq_mul, hfy, hfw] at this
    linarith
  · exact D.carrier_point_not_interior hyj i hij

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.interior_of_three
#print axioms Erdos634.C2Forward.wall_of_hull_func
