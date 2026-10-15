import Mathlib.Tactic
import Erdos634.Draft.T30LPi3Tile
import Erdos634.Draft.FluxHBreakpointsFrontier

/-!
# The chord clamps from the corner placement

`clamps`: for a triangle `T`, pairwise distinct vertex indices `v, w, z`, and `P = (1-p) T_v + p T_w`, `Q = (1-r) T_v + r T_z` with
`p, r ∈ (0,1)` (two points on the two sides at the vertex `T_v`, strictly inside the sides), the chord `PQ` is clamped in the sense of
`ChordFar.chord_far_sum`: supporting functionals `g` (side `vw`, with `g P = c_g`, `g Q < c_g`) and `h` (side `vz`, `h Q = c_h`, `h P < c_h`),
`openSegment P Q ⊆ interior T.carrier`, and `P` is a non-vertex frontier point.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry

theorem aff_comb (f : Plane →ᵃ[ℝ] ℝ) (P Q : Plane) (a b : ℝ) (hab : a + b = 1) :
    f (a • P + b • Q) = a * f P + b * f Q := by
  have hd : ∀ x, f x = f.linear x + f 0 := fun x => by simpa using congrFun (AffineMap.decomp f) x
  rw [hd (a • P + b • Q), hd P, hd Q]
  simp only [map_add, map_smul, smul_eq_mul]
  linear_combination (-(f 0)) * hab

theorem lin_comb (f : Plane →ₗ[ℝ] ℝ) (P Q : Plane) (a b : ℝ) :
    f (a • P + b • Q) = a * f P + b * f Q := by
  simp [map_add, map_smul]

theorem supp_pair (T : Tri) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ x ∈ T.carrier, f x ≤ c) ∧
      f (T.pts v) = c ∧ f (T.pts w) = c ∧ f (T.pts z) < c := by
  have h : ∀ v w z : Fin 3, v ≠ w → v ≠ z → w ≠ z → ((w = v + 1 ∧ z = v + 2) ∨ (v = w + 1 ∧ z = w + 2)) := by
    decide
  rcases h v w z hvw hvz hwz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact exists_supporting T v
  · obtain ⟨f, c, hf, hle, h1, h2, h3⟩ := exists_supporting T w
    exact ⟨f, c, hf, hle, h2, h1, h3⟩

theorem cover3 : ∀ v w z i : Fin 3, v ≠ w → v ≠ z → w ≠ z → (i = v ∨ i = w ∨ i = z) := by decide

theorem clamps (T : Tri) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) {p r : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    let P : Plane := (1 - p) • T.pts v + p • T.pts w
    let Q : Plane := (1 - r) • T.pts v + r • T.pts z
    (∃ (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ), (∀ y ∈ T.carrier, g y ≤ cg) ∧ g P = cg ∧ g Q < cg ∧ g ≠ 0) ∧
    (∃ (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ), (∀ y ∈ T.carrier, h y ≤ ch) ∧ h Q = ch ∧ h P < ch ∧ h ≠ 0) ∧
    openSegment ℝ P Q ⊆ interior T.carrier ∧ P ∈ frontier T.carrier ∧ P ∉ Set.range T.pts ∧
    P ∈ T.carrier ∧ Q ∈ T.carrier := by
  intro P Q
  have hcd : ∀ (i j : Fin 3), T.basis.coord i (T.pts j) = if i = j then 1 else 0 :=
    fun i j => AffineBasis.coord_apply T.basis i j
  have hcP : ∀ i, T.basis.coord i P = (1 - p) * (if i = v then 1 else 0) + p * (if i = w then 1 else 0) := by
    intro i
    show T.basis.coord i ((1 - p) • T.pts v + p • T.pts w) = _
    rw [aff_comb _ _ _ _ _ (by ring), hcd, hcd]
  have hcQ : ∀ i, T.basis.coord i Q = (1 - r) * (if i = v then 1 else 0) + r * (if i = z then 1 else 0) := by
    intro i
    show T.basis.coord i ((1 - r) • T.pts v + r • T.pts z) = _
    rw [aff_comb _ _ _ _ _ (by ring), hcd, hcd]
  have hPmem : P ∈ T.carrier := by
    rw [T.carrier_eq_nonneg_coord]
    intro i
    rw [hcP]
    split_ifs <;> nlinarith
  have hQmem : Q ∈ T.carrier := by
    rw [T.carrier_eq_nonneg_coord]
    intro i
    rw [hcQ]
    split_ifs <;> nlinarith
  obtain ⟨g, cg, hg0, hgle, hgv, hgw, hgz⟩ := supp_pair T v w z hvw hvz hwz
  obtain ⟨h, ch, hh0, hhle, hhv, hhz, hhw⟩ := supp_pair T v z w hvz hvw hwz.symm
  have hgP : g P = cg := by
    show g ((1 - p) • T.pts v + p • T.pts w) = cg
    rw [lin_comb, hgv, hgw]; ring
  have hgQ : g Q < cg := by
    show g ((1 - r) • T.pts v + r • T.pts z) < cg
    rw [lin_comb, hgv]; nlinarith
  have hhQ : h Q = ch := by
    show h ((1 - r) • T.pts v + r • T.pts z) = ch
    rw [lin_comb, hhv, hhz]; ring
  have hhP : h P < ch := by
    show h ((1 - p) • T.pts v + p • T.pts w) < ch
    rw [lin_comb, hhv]; nlinarith
  refine ⟨⟨g, cg, hgle, hgP, hgQ, hg0⟩, ⟨h, ch, hhle, hhQ, hhP, hh0⟩, ?_, ?_, ?_, hPmem, hQmem⟩
  · -- interior
    have hint : interior T.carrier = {x | ∀ i, 0 < T.basis.coord i x} := by
      have : T.carrier = convexHull ℝ (Set.range (T.basis : Fin 3 → Plane)) := rfl
      rw [this]
      exact AffineBasis.interior_convexHull T.basis
    rw [hint]
    rintro y ⟨a, b, ha, hb, hab, rfl⟩ i
    rw [aff_comb _ _ _ _ _ hab, hcP, hcQ]
    rcases cover3 v w z i hvw hvz hwz with rfl | rfl | rfl
    · simp [hvw, hvz]; nlinarith
    · simp [hvw.symm, hwz]; nlinarith
    · simp [hvz.symm, hwz.symm]; nlinarith
  · exact Erdos634.Draft.FluxHBreakpointsFrontier.Tri.mem_frontier_of_supporting T g hg0 cg hgle hPmem hgP
  · rintro ⟨m, hm⟩
    have h1 := hcP v
    rw [← hm, hcd] at h1
    have hv1 : (if v = v then (1:ℝ) else 0) = 1 := by simp
    rw [hv1] at h1
    simp only [hvw, if_false] at h1
    by_cases hmv : v = m
    · rw [if_pos hmv] at h1; nlinarith
    · rw [if_neg hmv] at h1; nlinarith

end Erdos634.Pi3F6
