import Mathlib.Tactic
import Erdos634.Draft.GLCFinish
import Erdos634.Draft.GLCCorner

/-!
# Facts about `T4 = K_Q` at `Q₁` (G2)

`T4_Q1_facts`: `K` a tile of the `γ = 2α` tile with `α` at `X` (`pts l = X`), `Q₁ = X + u`, its other two vertices `Q₁` and `Z` (either order), and `|XZ| = b`.  Then
`K` presents `β = π − 3α` at `Q₁` (the vertex opposite the `b`-edge `XZ`), `|Q₁Z| = a` (opposite `α`), `∠(Z − Q₁, u) = 3α` (the supplement of `β`), and `[Q₁,Z]` is an edge of `K`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry

variable {N : ℕ}

theorem angle_of_opp_b {U : Tri} {α a b c : ℝ} (hU : U.TwoAlphaData α a b c) (hab : a ≠ b) (hbc : b ≠ c)
    (m : Fin 3) (hm : U.oppLen m = b) : U.angleAt m = Real.pi - 3 * α := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hU
  obtain ⟨n, hn⟩ := σ.surjective m
  rw [← hn] at hm ⊢
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 n with rfl | rfl | rfl
  · exact absurd (o0.symm.trans hm) hab
  · exact h1
  · exact absurd (o2.symm.trans hm) hbc.symm

theorem T4_Q1_facts (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hbc : b ≠ c)
    (K : Fin N) (l : Fin 3) {X Q1 Z u : Plane} (hl : (D.tile K).pts l = X) (hang : (D.tile K).angleAt l = α)
    (hQ1 : Q1 = X + u)
    (hZ : ((D.tile K).pts (l + 1) = Q1 ∧ (D.tile K).pts (l + 2) = Z) ∨
      ((D.tile K).pts (l + 2) = Q1 ∧ (D.tile K).pts (l + 1) = Z))
    (hXZ : dist X Z = b) :
    (D.tile K).localAngle Q1 = Real.pi - 3 * α ∧ InnerProductGeometry.angle (Z - Q1) u = 3 * α ∧
      dist Q1 Z = a ∧ ∃ k : Fin 3, ((D.tile K).pts k = Q1 ∧ (D.tile K).pts (k + 1) = Z) ∨
        ((D.tile K).pts k = Z ∧ (D.tile K).pts (k + 1) = Q1) := by
  have hU := tile_twoalpha D hS K
  have hopp := opp_a_of_alpha hα hU l hang
  have e11 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e21 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e22 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e12 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  have hXQ : X - Q1 = -u := by rw [hQ1]; abel
  have hpi : ∀ x y : Plane, InnerProductGeometry.angle x (-y) = Real.pi - InnerProductGeometry.angle x y :=
    fun x y => InnerProductGeometry.angle_neg_right x y
  have hpi' : ∀ x y : Plane, InnerProductGeometry.angle (-x) y = Real.pi - InnerProductGeometry.angle x y :=
    fun x y => InnerProductGeometry.angle_neg_left x y
  rcases hZ with ⟨z1, z2⟩ | ⟨z1, z2⟩
  · have hopp1 : (D.tile K).oppLen (l + 1) = b := by
      unfold Tri.oppLen; rw [e11, e12, z2, hl]; rw [dist_comm]; exact hXZ
    have hβ := angle_of_opp_b hU hab hbc _ hopp1
    refine ⟨?_, ?_, ?_, l + 1, Or.inl ⟨z1, ?_⟩⟩
    · rw [← z1, Tri.localAngle_vertex]; exact hβ
    · have := angleAt_eq_angle (D.tile K) (l + 1)
      rw [hβ, e11, e12, z1, z2, hl, hXQ, hpi] at this
      linarith
    · unfold Tri.oppLen at hopp; rw [z1, z2] at hopp; exact hopp
    · rw [e11]; exact z2
  · have hopp1 : (D.tile K).oppLen (l + 2) = b := by
      unfold Tri.oppLen; rw [e21, e22, z2, hl]; exact hXZ
    have hβ := angle_of_opp_b hU hab hbc _ hopp1
    refine ⟨?_, ?_, ?_, l + 1, Or.inr ⟨z2, ?_⟩⟩
    · rw [← z1, Tri.localAngle_vertex]; exact hβ
    · have := angleAt_eq_angle (D.tile K) (l + 2)
      rw [hβ, e21, e22, z1, z2, hl, hXQ, hpi', InnerProductGeometry.angle_comm] at this
      linarith
    · unfold Tri.oppLen at hopp; rw [z1, z2] at hopp; rw [dist_comm]; exact hopp
    · rw [e11]; exact z1

end Erdos634.GLC

#print axioms Erdos634.GLC.T4_Q1_facts
