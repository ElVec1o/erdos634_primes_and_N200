import Mathlib.Tactic
import Erdos634.WedgeExtremal
import Erdos634.TP_erdos
import Erdos634.Draft.T30LPi3Tile

/-!
# Filling the angular sector at a boundary vertex

## Status of the junction step

The *configuration* half of the junction step (the placed tiles present γ, β and the point lies on a straight edge) is proved by
`march_junction_real` and `VertexFigureReal.gamma_boundary_figure_real` (the figure at a non-vertex frontier point is read off
`pin_angle_sum`). The remaining hypotheses of `march_junction_real` are the containment hypotheses `hφm, hψm`: the filling tile's
two edge directions at `v`, measured as oriented angles from the side direction `u`, lie in the uncovered wedge `[0, opening]`.

## Proved here

* `cone_interior`, `cone_disjoint` (the geometric half of containment): two distinct tiles with a common
  vertex `v` have disjoint open cones; there are no `s,t,s',t' > 0` with
  `s(P−v) + t(Q−v) = s'(P'−v) + t'(Q'−v)`, because a point `v + ε·(that vector)` is interior to both tiles for small `ε`.
  Witness: the real 2-tile dissection `TPErdos.wallDissection` at `(0,0)`; same-tile control.
* `vertex_dir_nonpos`: every tile edge at a target-boundary vertex points into the target's half-plane.
* `exists_P_tile` / `sector_step_pi3` (the π/3 sector fill): at a non-vertex frontier point of a `π/3`-tile
  `CongruentDissection` with `α ∉ ℚπ`, if tiles presenting `α` and `β` are present then the figure is exactly one each
  plus exactly one tile presenting `π/3`, the uncovered opening is `π/3` (`opening_pi3`), and a filling `π/3`-tile whose
  edge directions lie in the wedge has them on its two sides.

## Not proved

The containment hypotheses `hφm, hψm` of `sector_step_pi3` are not derived: `cone_disjoint` removes the overlap
alternative, but turning "the cone of the filling tile avoids the cones of the two placed tiles and lies in the half-plane"
into "its oriented angles lie in `[0, π/3]`" needs the cone and oriented-angle-interval dictionary and the placement
of the two placed cones (wedge order), neither of which is in Lean. `sector_step_pi3` has no witness for its
oriented-angle hypotheses on a real dissection (the figure half is witnessed in `Pi3Tile`).
-/

namespace Erdos634.SectorFill

open Erdos634.Geometry Erdos634.Pi3Tile

variable {N : ℕ}

/-- **Points of the open cone at a vertex are interior to the tile** (for small `ε`). -/
theorem cone_interior (T : Tri) (j : Fin 3) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      T.pts j + ε • (s • (T.pts (j + 1) - T.pts j) + t • (T.pts (j + 2) - T.pts j))
        ∈ interior T.carrier := by
  refine ⟨1 / (s + t + 1), by positivity, fun ε hε hε1 => ?_⟩
  have hpos : 0 < s + t + 1 := by linarith
  have hst : ε * (s + t) < 1 := by
    have h1 : ε * (s + t + 1) < 1 := by
      have := mul_lt_mul_of_pos_right hε1 hpos
      rwa [one_div, inv_mul_cancel₀ hpos.ne'] at this
    nlinarith
  have hj1 : j + 1 ≠ j := by fin_cases j <;> decide
  have hj2 : j + 2 ≠ j := by fin_cases j <;> decide
  have hj12 : j + 2 ≠ j + 1 := by fin_cases j <;> decide
  set y := T.pts j + ε • (s • (T.pts (j + 1) - T.pts j) + t • (T.pts (j + 2) - T.pts j)) with hy
  have hcoord : ∀ i, T.basis.coord i y
      = (if i = j then 1 else 0)
        + ε * (s * ((if i = j + 1 then 1 else 0) - (if i = j then 1 else 0))
          + t * ((if i = j + 2 then 1 else 0) - (if i = j then 1 else 0))) := by
    intro i
    have e : ∀ m : Fin 3, T.basis.coord i (T.pts m) = if i = m then 1 else 0 :=
      fun m => T.basis.coord_apply i m
    have key : y = (ε • (s • (T.pts (j + 1) - T.pts j) + t • (T.pts (j + 2) - T.pts j)))
        +ᵥ T.pts j := by rw [hy, vadd_eq_add, add_comm]
    have d : ∀ m n : Fin 3, (T.basis.coord i).linear (T.pts m - T.pts n)
        = (if i = m then 1 else 0) - (if i = n then 1 else 0) := by
      intro m n
      rw [← vsub_eq_sub, AffineMap.linearMap_vsub, vsub_eq_sub, e m, e n]
    rw [key, AffineMap.map_vadd, vadd_eq_add]
    simp only [map_smul, map_add, smul_eq_mul, d, e j]
    ring
  have hall : ∀ i, 0 < T.basis.coord i y := by
    intro i
    have hi : i = j ∨ i = j + 1 ∨ i = j + 2 := by
      fin_cases i <;> fin_cases j <;> decide
    rw [hcoord]
    rcases hi with rfl | rfl | rfl
    · simp [hj1, hj2, hj1.symm, hj2.symm]; nlinarith
    · simp [hj1, hj12, hj1.symm, hj12.symm]; positivity
    · simp [hj2, hj12, hj2.symm, hj12.symm]; positivity
  obtain ⟨r, hr, hball⟩ := T.ball_subset_of_pos hall
  exact mem_interior.mpr ⟨Metric.ball y r, hball, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

/-- **Two distinct tiles at a common vertex have disjoint open cones.**  There are no positive `s,t,s',t'` with
`s(P−v)+t(Q−v) = s'(P'−v)+t'(Q'−v)`, where `P,Q` (resp. `P',Q'`) are the other two vertices of the tile `i` (resp. `k`). -/
theorem cone_disjoint (D : Dissection N) {i k : Fin N} (hik : i ≠ k) {j l : Fin 3}
    (hv : (D.tile i).pts j = (D.tile k).pts l) {s t s' t' : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hs' : 0 < s') (ht' : 0 < t')
    (heq : s • ((D.tile i).pts (j + 1) - (D.tile i).pts j)
        + t • ((D.tile i).pts (j + 2) - (D.tile i).pts j)
      = s' • ((D.tile k).pts (l + 1) - (D.tile k).pts l)
        + t' • ((D.tile k).pts (l + 2) - (D.tile k).pts l)) : False := by
  obtain ⟨e1, he1, h1⟩ := cone_interior (D.tile i) j hs ht
  obtain ⟨e2, he2, h2⟩ := cone_interior (D.tile k) l hs' ht'
  have hε : 0 < min e1 e2 / 2 := by positivity
  have a1 := h1 (min e1 e2 / 2) hε (by
    have := min_le_left e1 e2; linarith [lt_min he1 he2])
  have a2 := h2 (min e1 e2 / 2) hε (by
    have := min_le_right e1 e2; linarith [lt_min he1 he2])
  rw [← heq, ← hv] at a2
  exact Set.disjoint_left.mp (D.interiors_disjoint hik) a1 a2

/-- **Edges at a boundary vertex point into the half-plane.**  If `g ≤ cg` on the target and `g = cg` at the vertex
`(tile i).pts j`, then every other vertex `(tile i).pts k` satisfies `g (P − v) ≤ 0`. -/
theorem vertex_dir_nonpos (D : Dissection N) (i : Fin N) (j k : Fin 3)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hv : g ((D.tile i).pts j) = cg) : g ((D.tile i).pts k - (D.tile i).pts j) ≤ 0 := by
  have hk : (D.tile i).pts k ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨i, subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  have := hg _ hk
  rw [map_sub, hv]; linarith

/-! ### The π/3 sector -/

/-- The uncovered opening after `α` and `β = 2π/3 − α` are placed on a straight edge is `π/3`. -/
theorem opening_pi3 (α : ℝ) : Real.pi - (α + (2 * Real.pi / 3 - α)) = Real.pi / 3 := by ring

/-- **C2, combinatorial half.**  At a non-vertex frontier point, if some tile presents `α` and some presents
`β = 2π/3 − α`, the figure is `(α, β, π/3)` exactly: one tile each, none straight; in particular exactly one tile
presents `π/3`. -/
theorem third_is_P (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) (iα : Fin N) (hiα : (D.tile iα).localAngle v = α)
    (iβ : Fin N) (hiβ : (D.tile iβ).localAngle v = 2 * Real.pi / 3 - α) :
    cnt D.toDissection v α = 1 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 1 ∧
    cnt D.toDissection v (Real.pi / 3) = 1 ∧ cnt D.toDissection v Real.pi = 0 := by
  have hα : 1 ≤ cnt D.toDissection v α :=
    Finset.card_pos.mpr ⟨iα, by simp [hiα]⟩
  have hb : (cnt D.toDissection v α = 0 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 0 ∧
        cnt D.toDissection v (Real.pi / 3) = 0 ∧ cnt D.toDissection v Real.pi = 1)
      ∨ (cnt D.toDissection v α = 0 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 0 ∧
        cnt D.toDissection v (Real.pi / 3) = 3 ∧ cnt D.toDissection v Real.pi = 0)
      ∨ (cnt D.toDissection v α = 1 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 1 ∧
        cnt D.toDissection v (Real.pi / 3) = 1 ∧ cnt D.toDissection v Real.pi = 0) :=
    boundary_fan_real D hirr hS hv hnv
  rcases hb with h | h | h
  · omega
  · omega
  · exact h

/-- **The π/3 sector step.**  After `α` and `β` are placed at a non-vertex frontier point `v`, the figure is
`(1,1,1,0)`, the uncovered opening is `π/3`, and a `π/3`-corner whose two edge directions lie in the wedge
`[0, π/3]` (measured from `u`) has them on the two sides — in one of two ways.  The containment `hφm, hψm` is a
HYPOTHESIS (see the header). -/
theorem sector_step_pi3 (D : CongruentDissection N) (o : Orientation ℝ Plane (Fin 2)) {α a b c : ℝ}
    (hirr : Irr α) (hS : D.model.SixtyData α a b c) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) (iα : Fin N) (hiα : (D.tile iα).localAngle v = α)
    (iβ : Fin N) (hiβ : (D.tile iβ).localAngle v = 2 * Real.pi / 3 - α)
    {P Q u : Plane} {φ ψ : ℝ} (hu : u ≠ 0) (hP : P - v ≠ 0) (hQ : Q - v ≠ 0)
    (hφ : (o.oangle u (P - v)).toReal = φ) (hψ : (o.oangle u (Q - v)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 3)) (hψm : ψ ∈ Set.Icc (0 : ℝ) (Real.pi / 3))
    (hcorner : cornerAngle P v Q = Real.pi / 3) :
    (cnt D.toDissection v α = 1 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 1 ∧
      cnt D.toDissection v (Real.pi / 3) = 1 ∧ cnt D.toDissection v Real.pi = 0) ∧
    ((φ = 0 ∧ ψ = Real.pi / 3) ∨ (φ = Real.pi / 3 ∧ ψ = 0)) := by
  refine ⟨third_is_P D hirr hS hv hnv iα hiα iβ hiβ, ?_⟩
  have hpi := Real.pi_pos
  exact Erdos634.WedgeExtremal.Dissection.corner_on_wedge_sides o hu hP hQ (by linarith) hφ hψ
    hφm hψm hcorner

/-! ### Witness for `cone_disjoint` on a real dissection -/

section witness

open Erdos634.TPErdos

/-- The two tiles of `wallDissection` are distinct, share the vertex `(0,0)`, and (by `cone_disjoint`) their open
cones there are disjoint: no positive combination of the edge vectors of one equals one of the other. -/
theorem cone_wall_instance {s t s' t' : ℝ} (hs : 0 < s) (ht : 0 < t) (hs' : 0 < s') (ht' : 0 < t') :
    ¬ (s • ((wallDissection.tile 0).pts (0 + 1) - (wallDissection.tile 0).pts 0)
        + t • ((wallDissection.tile 0).pts (0 + 2) - (wallDissection.tile 0).pts 0)
      = s' • ((wallDissection.tile 1).pts (0 + 1) - (wallDissection.tile 1).pts 0)
        + t' • ((wallDissection.tile 1).pts (0 + 2) - (wallDissection.tile 1).pts 0)) := by
  intro heq
  exact cone_disjoint wallDissection (i := 0) (k := 1) (j := 0) (l := 0) (by decide)
    (by rfl) hs ht hs' ht' heq

/-- Same-tile control: with `i = k` the equation is satisfiable (take everything equal), so `hik` is what
`cone_disjoint` uses. -/
theorem cone_same_tile_control (D : Dissection N) (i : Fin N) (j : Fin 3) :
    (1 : ℝ) • ((D.tile i).pts (j + 1) - (D.tile i).pts j)
        + (1 : ℝ) • ((D.tile i).pts (j + 2) - (D.tile i).pts j)
      = (1 : ℝ) • ((D.tile i).pts (j + 1) - (D.tile i).pts j)
        + (1 : ℝ) • ((D.tile i).pts (j + 2) - (D.tile i).pts j) := rfl

end witness

#print axioms cone_disjoint
#print axioms vertex_dir_nonpos
#print axioms third_is_P
#print axioms sector_step_pi3
#print axioms cone_wall_instance

end Erdos634.SectorFill
