import Mathlib.Tactic
import Erdos634.Draft.GLCFar2a
import Erdos634.Draft.GLCT4Facts
import Erdos634.Draft.GLCArith2
import Erdos634.Draft.T30LL3SideTile

/-!
# G2, Case 1 (the second tile `T3` on the `b`-side has a `b`-edge on the side: `T3 = T + (Y − O)`): no `γ`-tile with a forward edge at `Q₁`

Points as in `GLCCase2`: `O` corner, `X` (`|OX| = c`), `Y` (`|OY| = b`), `|XY| = a`, `Z = Y + (X − O)`, `Q₁ = X + (X − O)`, `Y₂ = Y + (Y − O)`.  `T4 = K_Q` has vertices `X, Q₁, Z`; `T3 = K_P = T + (Y − O)` has vertices `Y, Y₂, Z`.
The chord `[Q₁, Y₂]` has the midpoint `Z`, length `2a`, and is the union of the `a`-edges `[Q₁,Z]` of `T4` and `[Z,Y₂]` of `T3` (a wall), both ends clamped by the two side functionals `h` (at `Q₁`) and `g` (at `Y₂`),
open chord interior.  `far_edge_at_end_a` (word `2a = (2,0,0)`) gives a far tile with the `a`-edge `[Q₁,Z]`; `no_gamma_forward` finishes.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.ChordFar Erdos634.TPErdos Erdos634.LineParam Erdos634.C2Forward
open Erdos634.Pi3F6 Erdos634.Pi3Tile Erdos634.EdgeWordConversion

variable {N : ℕ}

set_option maxHeartbeats 6400000 in
open scoped Classical in
theorem g2_case1 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hb0 : 0 < b) (hbc' : b < c)
    (hsides : ∀ i : Fin 3, sideLen D i = a ∨ sideLen D i = b ∨ sideLen D i = c)
    (hword2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = 2 * a → x = 2 ∧ y = 0 ∧ z = 0)
    {O X Y : Plane} (hOX : dist O X = c) (hOY : dist O Y = b) (hXY : dist X Y = a)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh0 : h ≠ 0) (hhle : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhO : h O = ch) (hhX : h X = ch) (hhY : h Y < ch)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hgle : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgY : g Y = cg) (hgO : g O = cg) (hgX : g X < cg)
    (hQ1fr : X + (X - O) ∈ frontier D.target.carrier) (hQ1nv : X + (X - O) ∉ Set.range D.target.pts)
    (hintC : openSegment ℝ (X + (X - O)) (Y + (Y - O)) ⊆ interior D.target.carrier)
    (KQ : Fin N) (lQ : Fin 3) (hlQ : (D.tile KQ).pts lQ = X) (hangQ : (D.tile KQ).angleAt lQ = α)
    (hZQ : ((D.tile KQ).pts (lQ + 1) = X + (X - O) ∧ (D.tile KQ).pts (lQ + 2) = Y + (X - O)) ∨
      ((D.tile KQ).pts (lQ + 2) = X + (X - O) ∧ (D.tile KQ).pts (lQ + 1) = Y + (X - O)))
    (KP : Fin N) (lP : Fin 3) (hlP : (D.tile KP).pts lP = Y)
    (hZP : ((D.tile KP).pts (lP + 1) = Y + (Y - O) ∧ (D.tile KP).pts (lP + 2) = Y + (X - O)) ∨
      ((D.tile KP).pts (lP + 2) = Y + (Y - O) ∧ (D.tile KP).pts (lP + 1) = Y + (X - O))) :
    ¬ ∃ (U : Fin N) (l : Fin 3), (D.tile U).pts l = X + (X - O) ∧ (D.tile U).angleAt l = 2 * α ∧
      (SameRay ℝ (X - O) ((D.tile U).pts (l + 1) - (X + (X - O))) ∨
       SameRay ℝ (X - O) ((D.tile U).pts (l + 2) - (X + (X - O)))) := by
  rintro ⟨U, l, hU, hUang, hUray⟩
  set Z : Plane := Y + (X - O) with hZdef
  set Q1 : Plane := X + (X - O) with hQ1def
  set Y2 : Plane := Y + (Y - O) with hY2def
  have hc0 : 0 < c := by linarith
  have hu : X - O ≠ 0 := by
    intro h0
    have : X = O := sub_eq_zero.mp h0
    rw [this, dist_self] at hOX; linarith
  have hnorm_y : ‖Y - O‖ = b := by rw [← dist_eq_norm, dist_comm]; exact hOY
  have hXYne : X ≠ Y := by
    intro he; rw [← he] at hOY; linarith
  have hXZ : dist X Z = b := by
    rw [hZdef, dist_eq_norm]
    have : X - (Y + (X - O)) = -(Y - O) := by abel
    rw [this, norm_neg, hnorm_y]
  have e11 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e12 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  obtain ⟨hKQloc, hangZ, hdQZ, -⟩ := T4_Q1_facts D hα hS hab hbc KQ lQ hlQ hangQ (Q1 := Q1) (Z := Z) (u := X - O) rfl hZQ hXZ
  obtain ⟨f, c0, hf0, hfle', hf1, hf2, hf3⟩ := exists_supporting (D.tile KQ) (lQ + 1)
  rw [e11] at hf2
  rw [e12, hlQ] at hf3
  have hfle : ∀ m, f ((D.tile KQ).pts m) ≤ c0 := fun m => hfle' _ (subset_convexHull ℝ _ ⟨m, rfl⟩)
  have hfQ1Z : f Q1 = c0 ∧ f Z = c0 := by
    rcases hZQ with ⟨z1, z2⟩ | ⟨z1, z2⟩
    · rw [z1] at hf1; rw [z2] at hf2; exact ⟨hf1, hf2⟩
    · rw [z2] at hf1; rw [z1] at hf2; exact ⟨hf2, hf1⟩
  have hnegf : -f ≠ 0 := neg_ne_zero.mpr hf0
  -- the chord `Q₁ Y₂`: midpoint `Z`, length `2a`
  have hmZ : midpoint ℝ Q1 Y2 = Z := by
    rw [midpoint_eq_smul_add]; simp only [invOf_eq_inv]; rw [hQ1def, hY2def, hZdef]; module
  have hdist : dist Q1 Y2 = 2 * a := by
    rw [dist_eq_norm]
    have : Q1 - Y2 = (2 : ℝ) • (X - Y) := by rw [hQ1def, hY2def]; module
    have h2n : ‖(2 : ℝ)‖ = 2 := by simp
    rw [this, norm_smul, ← dist_eq_norm, hXY, h2n]
  have hapos : 0 < a := by
    have := dist_pos.mpr hXYne; linarith
  have hQ1Y2 : Q1 ≠ Y2 := by
    intro he; rw [he, dist_self] at hdist; linarith
  have hfY2 : f Y2 = c0 := by
    have : Y2 = (2 : ℝ) • Z - Q1 := by rw [hY2def, hZdef, hQ1def]; module
    rw [this, map_sub, map_smul, hfQ1Z.1, hfQ1Z.2]; simp only [smul_eq_mul]; ring
  -- clamps from the two side functionals
  have hhQ1 : h Q1 = ch := by rw [hQ1def, map_add, map_sub, hhX, hhO]; ring
  have hhY2 : h Y2 < ch := by rw [hY2def, map_add, map_sub, hhO]; linarith
  have hgY2 : g Y2 = cg := by rw [hY2def, map_add, map_sub, hgY, hgO]; ring
  have hgQ1 : g Q1 < cg := by rw [hQ1def, map_add, map_sub, hgO]; linarith
  -- the chord is a wall: union of the edges `[Q₁, Z]` of `T4` and `[Z, Y₂]` of `T3`
  obtain ⟨k4, hk4⟩ := pair_edge (D.tile KQ) (lQ + 1) (lQ + 2) ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) lQ)
  obtain ⟨k3, hk3⟩ := pair_edge (D.tile KP) (lP + 1) (lP + 2) ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) lP)
  have hwall : ∀ y ∈ openSegment ℝ Q1 Y2, ∀ i', y ∉ interior (D.tile i').carrier := by
    intro y hy
    rcases openSegment_halves _ _ hy with h' | h'
    · rw [hmZ] at h'
      rcases hZQ with ⟨z1, z2⟩ | ⟨z1, z2⟩
      · exact Dissection.edge_point_not_interior D.toDissection (j := KQ) (k := k4) (by rw [hk4, z1, z2]; exact h')
      · exact Dissection.edge_point_not_interior D.toDissection (j := KQ) (k := k4)
          (by rw [hk4, z1, z2, segment_symm]; exact h')
    · rw [hmZ] at h'
      rcases hZP with ⟨z1, z2⟩ | ⟨z1, z2⟩
      · exact Dissection.edge_point_not_interior D.toDissection (j := KP) (k := k3)
          (by rw [hk3, z1, z2, segment_symm]; exact h')
      · exact Dissection.edge_point_not_interior D.toDissection (j := KP) (k := k3)
          (by rw [hk3, z1, z2]; exact h')
  -- the far-chain tile with the edge `[Q₁, Z]`
  obtain ⟨Kc, k, hKc, hKc3, hKcle⟩ := far_edge_at_end_a D hsides hword2 f hf0 c0 hQ1Y2 hfQ1Z.1 hfY2
    h ch hhle hhQ1 hhY2 g cg hgle hgY2 hgQ1 hintC hwall hdist
  rw [hmZ] at hKc
  have hne : Kc ≠ KQ := by
    intro hEq
    have h1 := hfle (k + 2)
    rw [hEq] at hKc3
    have h2 : -(f ((D.tile KQ).pts (k + 2))) < -c0 := hKc3
    linarith
  exact no_gamma_forward D hα hS hab hac hQ1fr hQ1nv hu hangZ KQ hKQloc Kc k hKc hdQZ hne U l hU hUang hUray

end Erdos634.GLC

#print axioms Erdos634.GLC.g2_case1
