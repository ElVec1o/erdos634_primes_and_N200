import Mathlib.Tactic
import Erdos634.Draft.T30LL3Fill

/-!
# The second tile on a side is `T + a e₁`: direction uniqueness (SAS)

* `dir_unique`: in the plane, if `u ≠ 0`, a linear functional `g` has `g u = 0`, `g q < 0`, `g w ≤ 0`, and `w, q` have the same norm and the same inner
  product with `u`, then `w = q`.  (Two vectors at the same angle from `u`, same length, are `q` and its mirror image in the line `ℝu`; the mirror has `g > 0`.)
* `pi3_edges_pair`: the two edges of a tile at a `π/3` vertex have lengths `(a,b)` or `(b,a)`.
* `side_vertices`: a triangle `U` with `π/3` at `l`, an edge `s` along the ray `ℝ≥0 u` of length `‖u‖`, the other edge `t` of length `‖q‖`, where `angle u q = π/3`,
  `g u = 0`, `g q < 0` and the vertex `U t` on the `g ≤` side: then `U s = P + u` and `U t = P + q`.  Applied to the corner tile
  `T = {O, P, Q}` (`u = P − O`, `q = Q − O`): the second tile on the side through `P` is `T + (P − O)`.
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6

theorem dir_unique_real (u0 u1 q0 q1 s0 s1 g0 g1 : ℝ) (hN : 0 < u0 ^ 2 + u1 ^ 2)
    (h1 : s0 * u0 + s1 * u1 = 0)
    (h2 : 2 * (q0 * s0 + q1 * s1) + s0 ^ 2 + s1 ^ 2 = 0)
    (hg : u0 * g0 + u1 * g1 = 0) (hq : q0 * g0 + q1 * g1 < 0)
    (hw : (q0 + s0) * g0 + (q1 + s1) * g1 ≤ 0) : s0 = 0 ∧ s1 = 0 := by
  have hσ : (s1 * u0 - s0 * u1) * (2 * (q1 * u0 - q0 * u1) + (s1 * u0 - s0 * u1)) = 0 := by
    linear_combination (u0 ^ 2 + u1 ^ 2) * h2 - (2 * (q0 * u0 + q1 * u1) + (s0 * u0 + s1 * u1)) * h1
  have hqg : (u0 ^ 2 + u1 ^ 2) * (q0 * g0 + q1 * g1) = (q1 * u0 - q0 * u1) * (u0 * g1 - u1 * g0) := by
    linear_combination (q0 * u0 + q1 * u1) * hg
  have hsg : (u0 ^ 2 + u1 ^ 2) * (s0 * g0 + s1 * g1) = (s1 * u0 - s0 * u1) * (u0 * g1 - u1 * g0) := by
    linear_combination (s0 * u0 + s1 * u1) * hg
  have hss : (u0 ^ 2 + u1 ^ 2) * (s0 ^ 2 + s1 ^ 2) = (s1 * u0 - s0 * u1) ^ 2 := by
    linear_combination (s0 * u0 + s1 * u1) * h1
  have hκ : (q1 * u0 - q0 * u1) * (u0 * g1 - u1 * g0) < 0 := by
    rw [← hqg]; exact mul_neg_of_pos_of_neg hN hq
  rcases mul_eq_zero.mp hσ with h | h
  · rw [h] at hss
    have h3 : s0 ^ 2 + s1 ^ 2 = 0 := by
      have : (u0 ^ 2 + u1 ^ 2) * (s0 ^ 2 + s1 ^ 2) = 0 := by rw [hss]; ring
      exact (mul_eq_zero.mp this).resolve_left hN.ne'
    constructor <;> nlinarith [sq_nonneg s0, sq_nonneg s1]
  · exfalso
    have hw' : (u0 ^ 2 + u1 ^ 2) * ((q0 + s0) * g0 + (q1 + s1) * g1) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inl ⟨hN.le, hw⟩)
    have h4 : (u0 ^ 2 + u1 ^ 2) * ((q0 + s0) * g0 + (q1 + s1) * g1)
        = (q1 * u0 - q0 * u1) * (u0 * g1 - u1 * g0) + (s1 * u0 - s0 * u1) * (u0 * g1 - u1 * g0) := by
      linear_combination hqg + hsg
    have h5 : s1 * u0 - s0 * u1 = -(2 * (q1 * u0 - q0 * u1)) := by linarith
    rw [h5] at h4
    nlinarith [hκ, hw', h4]

theorem dir_unique {u q w : Plane} (hu : u ≠ 0) (g : Plane →ₗ[ℝ] ℝ)
    (hgu : g u = 0) (hgq : g q < 0) (hgw : g w ≤ 0)
    (hn : ‖w‖ = ‖q‖) (hin : inner ℝ u w = inner ℝ u q) : w = q := by
  have hnorm : ∀ x : Plane, ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    intro x; rw [← real_inner_self_eq_norm_sq, inner_coord]; ring
  have hN : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    rw [← hnorm]; exact pow_pos (norm_pos_iff.mpr hu) 2
  rw [inner_coord, inner_coord] at hin
  have h2 : w 0 ^ 2 + w 1 ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [← hnorm, ← hnorm, hn]
  rw [lin_coord g u] at hgu
  rw [lin_coord g q] at hgq
  rw [lin_coord g w] at hgw
  have key := dir_unique_real (u 0) (u 1) (q 0) (q 1) (w 0 - q 0) (w 1 - q 1)
    (g (EuclideanSpace.single 0 1)) (g (EuclideanSpace.single 1 1)) hN
    (by linear_combination hin) (by linear_combination h2) hgu hgq (le_of_eq_of_le (by ring) hgw)
  ext i; fin_cases i
  · simp; linarith [key.1]
  · simp; linarith [key.2]

theorem pi3_edges_pair {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c) (K : Fin N) (l : Fin 3)
    (hang : (D.tile K).angleAt l = Real.pi / 3) :
    (dist ((D.tile K).pts l) ((D.tile K).pts (l + 1)) = a ∧ dist ((D.tile K).pts l) ((D.tile K).pts (l + 2)) = b) ∨
    (dist ((D.tile K).pts l) ((D.tile K).pts (l + 1)) = b ∧ dist ((D.tile K).pts l) ((D.tile K).pts (l + 2)) = a) := by
  have hU := tile_sixty D hS K
  have hopp := opp_c_of_pi3 hirr hU l hang
  have hor := tri_two_orient hU hac hbc l hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  rcases hor with ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩
  · right
    refine ⟨h3, ?_⟩
    rw [dist_comm]; exact h1
  · left
    refine ⟨h3, ?_⟩
    rw [dist_comm]; exact h1

/-- **The second tile on a side, as vectors.**  See the module header. -/
theorem side_vertices (U : Tri) (l s t : Fin 3) (hst : (s = l + 1 ∧ t = l + 2) ∨ (s = l + 2 ∧ t = l + 1))
    (hang : U.angleAt l = Real.pi / 3) {P u q : Plane} (hl : U.pts l = P) (hu : u ≠ 0)
    (hray : SameRay ℝ u (U.pts s - P)) (hus : dist P (U.pts s) = ‖u‖) (hqt : dist P (U.pts t) = ‖q‖)
    (hangq : InnerProductGeometry.angle u q = Real.pi / 3)
    (g : Plane →ₗ[ℝ] ℝ) (hgu : g u = 0) (hgq : g q < 0) (hgt : g (U.pts t) ≤ g P) :
    U.pts s = P + u ∧ U.pts t = P + q := by
  have hus' : u = U.pts s - P := by
    refine hray.eq_of_norm_eq ?_
    rw [← dist_eq_norm, dist_comm]; exact hus.symm
  have hang' : InnerProductGeometry.angle (U.pts (l + 1) - P) (U.pts (l + 2) - P) = Real.pi / 3 := by
    have := hang
    unfold Tri.angleAt cornerAngle EuclideanGeometry.angle at this
    simp only [vsub_eq_sub] at this
    rw [hl] at this
    exact this
  have hangw : InnerProductGeometry.angle u (U.pts t - P) = Real.pi / 3 := by
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hus']; exact hang'
    · rw [hus', InnerProductGeometry.angle_comm]; exact hang'
  have hwn : ‖U.pts t - P‖ = ‖q‖ := by
    rw [← dist_eq_norm, dist_comm]; exact hqt
  have hin : inner ℝ u (U.pts t - P) = inner ℝ u q := by
    have h1 := InnerProductGeometry.cos_angle_mul_norm_mul_norm u (U.pts t - P)
    have h2 := InnerProductGeometry.cos_angle_mul_norm_mul_norm u q
    rw [hangw, Real.cos_pi_div_three, hwn] at h1
    rw [hangq, Real.cos_pi_div_three] at h2
    rw [← h1, ← h2]
  have hgw : g (U.pts t - P) ≤ 0 := by rw [map_sub]; linarith
  have hw := dir_unique hu g hgu hgq hgw hwn hin
  refine ⟨by rw [hus']; abel, ?_⟩
  rw [← hw]; abel

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.dir_unique
#print axioms Erdos634.C2Forward.side_vertices
#print axioms Erdos634.C2Forward.pi3_edges_pair
