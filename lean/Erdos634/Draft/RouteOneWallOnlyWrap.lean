import Erdos634.RouteOneWallOnly

/-!
# Wrapper: `RouteOneWallOnly` — Route 1's flank from the wall alone

Thin delegation layer exposing the key theorems of `Erdos634.RouteOneWallOnly`
under the `Draft` namespace.
No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.RouteOneWallOnlyWrap

open Erdos634.Geometry Erdos634.RouteOneWallOnly

/-- **The serving tile does not cover `V` from its own position alone.**
If every point of `T` lies weakly above `V` then `T.localAngle V ≠ 2π`. -/
theorem serving_ne_two_pi_of_above_X (T : Tri) (V : Plane)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) :
    T.localAngle V ≠ 2 * Real.pi :=
  serving_ne_two_pi_of_above T V habove

/-- **Route 1's flank at `V` from the wall alone.**
From the `α`-tile data and the local wall condition, a tile with `V` as a vertex
and a horizontal rightward edge at `V` exists.  No below-tile in the statement. -/
theorem flank_from_wall_only_X {N : ℕ} (D : Dissection N) (V A : Plane) (j : Fin N) (mj : Fin 3)
    (hV : V ∈ interior D.target.carrier) (hAcar : A ∈ D.target.carrier)
    (hjseg : openSegment ℝ V A
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier → (q - V) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier → 0 ≤ (q - V) 1) :
    ∃ (i : Fin N) (m : Fin 3), (D.tile i).pts m = V ∧
      ((((D.tile i).pts (m + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 1) - V) 0) ∨
       (((D.tile i).pts (m + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 2) - V) 0)) :=
  flank_from_wall_only D V A j mj hV hAcar hjseg hAy hAx habovej hjleft hwall

/-- **The same, with the `α`-tile's position given by its vertices.**
Carrier hypotheses on `j` replaced by six sign conditions on its three vertices. -/
theorem flank_from_wall_only_of_vertices_X {N : ℕ} (D : Dissection N) (V A : Plane)
    (j : Fin N) (mj : Fin 3)
    (hV : V ∈ interior D.target.carrier) (hAcar : A ∈ D.target.carrier)
    (hjseg : openSegment ℝ V A
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (hvj : ∀ m : Fin 3, 0 ≤ ((D.tile j).pts m - V) 1)
    (hlj : ∀ m : Fin 3, ((D.tile j).pts m - V) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier → 0 ≤ (q - V) 1) :
    ∃ (i : Fin N) (m : Fin 3), (D.tile i).pts m = V ∧
      ((((D.tile i).pts (m + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 1) - V) 0) ∨
       (((D.tile i).pts (m + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 2) - V) 0)) :=
  flank_from_wall_only_of_vertices D V A j mj hV hAcar hjseg hAy hAx hvj hlj hwall

/-! ### Non-vacuity witness

The `α`-tile side of the configuration is satisfiable: the triangle `(0,0),(-1,0),(-1,1)` at
`V = (0,0)`, `A = (-1,0)` meets all five `α`-tile conditions. -/

/-- Non-vacuity: `alpha_tile_witness` is a closed theorem; delegate directly. -/
theorem alpha_tile_witness_X :
    ∃ (T : Tri) (V A : Plane) (m : Fin 3),
      openSegment ℝ V A ⊆ openSegment ℝ (T.pts (m + 1)) (T.pts (m + 2)) ∧
      (A - V) 1 = 0 ∧ (A - V) 0 < 0 ∧
      (∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) ∧
      (∀ q : Plane, q ∈ T.carrier → (q - V) 0 ≤ 0) :=
  alpha_tile_witness

#print axioms alpha_tile_witness_X

end Erdos634.Draft.RouteOneWallOnlyWrap
