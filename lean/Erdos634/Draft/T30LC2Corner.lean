import Mathlib.Tactic
import Erdos634.Draft.T30LC2Forward

/-!
# (C2) as a fact about a real dissection

(C2): the second supported tile on each side has `π/3` at its end next to the corner tile.

`c2_config`: at a target corner `O` (tile `i` with its `π/3`-vertex at `O`, edges along the two sides ending at `P` (side `v→w`) and `Q` (side `v→z`),
neither at a target vertex): with `T₂ = hull{P,Q,P+Q−O}` the point reflection of `T` (`aux_reflection_ex`), `T` and `T₂` present `α`/`β` at `P` and
`β`/`α` at `Q`; `forward_tile` then gives, at `P` and at `Q`, a tile `K` with a vertex of angle `π/3` there and an edge on the target side, running forward
(away from `O`).  Both ends.  `c2_doubled_corner` = the corner-level statement (as `corner_far_reflection`: only the corner angle and the side-length
hypotheses).  The edge on the side has length `a` or `b` (`pi3_edge_ab`).
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.ChordFar Erdos634.Pi3Corner Erdos634.SectorFill

theorem exists_sep {u a : Plane} (h : u 0 * a 1 - u 1 * a 0 ≠ 0) :
    ∃ m : Plane →ₗ[ℝ] ℝ, m u = 1 ∧ m a = 0 := by
  have hD : a 0 * u 1 - a 1 * u 0 ≠ 0 := by intro h'; apply h; linarith
  refine ⟨{ toFun := fun x => (a 0 * x 1 - a 1 * x 0) / (a 0 * u 1 - a 1 * u 0)
            map_add' := ?_
            map_smul' := ?_ }, ?_, ?_⟩
  · intro x y; simp only [PiLp.add_apply]; ring
  · intro c x; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  · show (a 0 * u 1 - a 1 * u 0) / (a 0 * u 1 - a 1 * u 0) = 1
    exact div_self hD
  · show (a 0 * a 1 - a 1 * a 0) / (a 0 * u 1 - a 1 * u 0) = 0
    ring

/-- The forward points `P + ε(P−O)` are outside every set whose hull is spanned by `O, P, Q, P+Q−O`. -/
theorem sep_not_mem {O P Q : Plane} (h : (P - O) 0 * (Q - O) 1 - (P - O) 1 * (Q - O) 0 ≠ 0)
    {S : Set Plane} (hS : ∀ y ∈ S, y = O ∨ y = P ∨ y = Q ∨ y = P + Q - O) {ε : ℝ} (hε : 0 < ε) :
    P + ε • (P - O) ∉ convexHull ℝ S := by
  obtain ⟨m, hmu, hma⟩ := exists_sep h
  intro hmem
  have hmP : m P = m O + 1 := by rw [map_sub] at hmu; linarith
  have hmQ : m Q = m O := by rw [map_sub] at hma; linarith
  have hconv : Convex ℝ {x : Plane | m x ≤ m O + 1} := convex_halfSpace_le m.isLinear _
  have hsub : S ⊆ {x | m x ≤ m O + 1} := by
    intro y hy
    simp only [Set.mem_setOf_eq]
    rcases hS y hy with h' | h' | h' | h' <;> rw [h']
    · linarith
    · linarith
    · linarith
    · rw [map_sub, map_add]; linarith
  have := convexHull_min hsub hconv hmem
  simp only [Set.mem_setOf_eq] at this
  rw [map_add, map_smul, map_sub, hmP] at this
  simp only [smul_eq_mul] at this
  nlinarith

theorem c2_at_end {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) {O P Q : Plane}
    (hind : (P - O) 0 * (Q - O) 1 - (P - O) 1 * (Q - O) 0 ≠ 0)
    (hPfr : P ∈ frontier D.target.carrier) (hPnv : P ∉ Set.range D.target.pts)
    (g : Plane →ₗ[ℝ] ℝ) (hg0 : g ≠ 0) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgO : g O = cg)
    {ε0 : ℝ} (hε0 : 0 < ε0) (hin : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • (P - O) ∈ D.target.carrier)
    (T T2 : Fin N) (hTc : (D.tile T).carrier = convexHull ℝ {O, P, Q})
    (hT2c : (D.tile T2).carrier = convexHull ℝ {P, Q, P + Q - O})
    (hpair : ((D.tile T).localAngle P = α ∧ (D.tile T2).localAngle P = 2 * Real.pi / 3 - α) ∨
      ((D.tile T).localAngle P = 2 * Real.pi / 3 - α ∧ (D.tile T2).localAngle P = α)) :
    ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = P ∧ (D.tile K).angleAt l = Real.pi / 3 ∧
      (SameRay ℝ (P - O) ((D.tile K).pts (l + 1) - P) ∨ SameRay ℝ (P - O) ((D.tile K).pts (l + 2) - P)) := by
  have hu : P - O ≠ 0 := by
    intro h0
    apply hind
    rw [h0]; simp
  have hgu : g (P - O) = 0 := by rw [map_sub, hgP, hgO]; ring
  have hnT : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • (P - O) ∉ (D.tile T).carrier := by
    intro ε hε _
    rw [hTc]
    exact sep_not_mem hind (fun y hy => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      tauto) hε
  have hnT2 : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • (P - O) ∉ (D.tile T2).carrier := by
    intro ε hε _
    rw [hT2c]
    exact sep_not_mem hind (fun y hy => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      tauto) hε
  rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact forward_tile D hirr hS hPfr hPnv hu g hg0 cg hg hgP hgu hε0 hin T T2 h1 h2 hnT hnT2
  · exact forward_tile D hirr hS hPfr hPnv hu g hg0 cg hg hgP hgu hε0 hin T2 T h2 h1 hnT2 hnT

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.c2_at_end
