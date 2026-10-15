import Mathlib.Tactic
import Erdos634.Draft.GLCT4

/-!
# `corner_G1_T4`: G1 plus `T4 = T + (X − O)` at a real `α`-corner

At a target corner of angle `α` of a `γ = 2α` dissection (hypotheses of `GLCG1.corner_G1`), with `T` the corner tile (`O`, `P = pts (j+1)`, `Q = pts (j+2)`):
the second tiles `K_P, K_Q` of G1 (an `α`-vertex at `P`, resp. `Q`, with an edge along the side) satisfy `T4Concl`: if the edge along the side has the same length as `T`'s first edge
(`|OQ|`, resp. `|OP|`; the "(c,c)" resp. "(b,b)" configuration) then `K` is the translate of `T` by `Q − O` (resp. `P − O`): the other edge ends at `Z = P + Q − O`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Cone Erdos634.Pi3F6 Erdos634.Pi3Tile

variable {N : ℕ}

/-- The conclusion of `T4_tile_side`. -/
def T4Concl (D : CongruentDissection N) (i : Fin N) (j m1 m2 : Fin 3) (K : Fin N) (l : Fin 3) : Prop :=
  (SameRay ℝ ((D.tile i).pts m1 - (D.tile i).pts j) ((D.tile K).pts (l + 1) - (D.tile i).pts m1) →
      dist ((D.tile i).pts m1) ((D.tile K).pts (l + 1)) = dist ((D.tile i).pts j) ((D.tile i).pts m1) →
      (D.tile K).pts (l + 1) = (D.tile i).pts m1 + ((D.tile i).pts m1 - (D.tile i).pts j) ∧
      (D.tile K).pts (l + 2) = (D.tile i).pts m2 + (D.tile i).pts m1 - (D.tile i).pts j) ∧
    (SameRay ℝ ((D.tile i).pts m1 - (D.tile i).pts j) ((D.tile K).pts (l + 2) - (D.tile i).pts m1) →
      dist ((D.tile i).pts m1) ((D.tile K).pts (l + 2)) = dist ((D.tile i).pts j) ((D.tile i).pts m1) →
      (D.tile K).pts (l + 2) = (D.tile i).pts m1 + ((D.tile i).pts m1 - (D.tile i).pts j) ∧
      (D.tile K).pts (l + 1) = (D.tile i).pts m2 + (D.tile i).pts m1 - (D.tile i).pts j)

theorem side_data (T : Tri) (k W V : Fin 3) (hWV : (W = k + 1 ∧ V = k + 2) ∨ (W = k + 2 ∧ V = k + 1))
    {X Y : Plane} (hX : SameRay ℝ (T.pts W - T.pts k) (X - T.pts k)) (hXne : X - T.pts k ≠ 0)
    (hY : SameRay ℝ (T.pts V - T.pts k) (Y - T.pts k)) (hYne : Y - T.pts k ≠ 0) :
    ∃ (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ), (∀ y ∈ T.carrier, h y ≤ ch) ∧
      h (T.pts k) = ch ∧ h X = ch ∧ h Y < ch := by
  obtain ⟨h, ch, -, hle, hk, hW, hV⟩ := side_functional T k W V hWV
  have hWne : T.pts W - T.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro e
    have := T.indep.injective e
    rcases hWV with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k this
    · exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k this
  have hVne : T.pts V - T.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro e
    have := T.indep.injective e
    rcases hWV with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k this
    · exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k this
  obtain ⟨p, hp0, hp⟩ := Erdos634.Pi3F6.rayparam hWne hXne hX
  obtain ⟨q, hq0, hq⟩ := Erdos634.Pi3F6.rayparam hVne hYne hY
  have hXe : X = T.pts k + p • (T.pts W - T.pts k) := by rw [← hp]; abel
  have hYe : Y = T.pts k + q • (T.pts V - T.pts k) := by rw [← hq]; abel
  refine ⟨h, ch, hle, hk, ?_, ?_⟩
  · rw [hXe, map_add, map_smul, map_sub, hk, hW]; simp
  · rw [hYe, map_add, map_smul, map_sub, hk]
    have := mul_neg_of_pos_of_neg hq0 (sub_neg.2 hV)
    simp only [smul_eq_mul]
    linarith

set_option maxHeartbeats 1600000 in
/-- **G1 + `T4 = T + (X − O)`** at an `α`-corner of a real dissection. -/
theorem corner_G1_T4 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (k : Fin 3) (hk : D.target.angleAt k = α)
    (hA1 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ b)
    (hA2 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ c)
    (hB1 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ b)
    (hB2 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ c) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k ∧ (D.tile i).angleAt j = α ∧
      (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 2) ∧ (D.tile K).angleAt l = α ∧
        (SameRay ℝ ((D.tile i).pts (j + 2) - (D.tile i).pts j) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 2)) ∨
         SameRay ℝ ((D.tile i).pts (j + 2) - (D.tile i).pts j) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 2))) ∧
        T4Concl D i j (j + 2) (j + 1) K l) ∧
      (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 1) ∧ (D.tile K).angleAt l = α ∧
        (SameRay ℝ ((D.tile i).pts (j + 1) - (D.tile i).pts j) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 1)) ∨
         SameRay ℝ ((D.tile i).pts (j + 1) - (D.tile i).pts j) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 1))) ∧
        T4Concl D i j (j + 1) (j + 2) K l) := by
  obtain ⟨i, j, hj, hang, hcase, hlen, j', hj', X, -, -, ⟨KP, lP, hKPpt, hKPang, hKPray⟩, ⟨KQ, lQ, hKQpt, hKQang, hKQray⟩⟩ :=
    corner_G1 D hα hS hab hac hword k hk hA1 hA2 hB1 hB2
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hPne : (D.tile i).pts (j + 1) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hQne : (D.tile i).pts (j + 2) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hfun : (∃ (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ), (∀ y ∈ D.target.carrier, h y ≤ ch) ∧
        h ((D.tile i).pts (j + 2)) = ch ∧ h (D.target.pts k) = ch ∧ h ((D.tile i).pts (j + 1)) < ch) ∧
      (∃ (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ), (∀ y ∈ D.target.carrier, h y ≤ ch) ∧
        h ((D.tile i).pts (j + 1)) = ch ∧ h (D.target.pts k) = ch ∧ h ((D.tile i).pts (j + 2)) < ch) := by
    rcases hcase with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
    · obtain ⟨h, ch, hle, h0, h1, h2⟩ := side_data D.target k (k + 2) (k + 1) (Or.inr ⟨rfl, rfl⟩) hr2 hQne hr1 hPne
      obtain ⟨h', ch', hle', h0', h1', h2'⟩ := side_data D.target k (k + 1) (k + 2) (Or.inl ⟨rfl, rfl⟩) hr1 hPne hr2 hQne
      exact ⟨⟨h, ch, hle, h1, h0, h2⟩, ⟨h', ch', hle', h1', h0', h2'⟩⟩
    · obtain ⟨h, ch, hle, h0, h1, h2⟩ := side_data D.target k (k + 1) (k + 2) (Or.inl ⟨rfl, rfl⟩) hr2 hQne hr1 hPne
      obtain ⟨h', ch', hle', h0', h1', h2'⟩ := side_data D.target k (k + 2) (k + 1) (Or.inr ⟨rfl, rfl⟩) hr1 hPne hr2 hQne
      exact ⟨⟨h, ch, hle, h1, h0, h2⟩, ⟨h', ch', hle', h1', h0', h2'⟩⟩
  obtain ⟨⟨hQ, chQ, hleQ, hQ1, hQ0, hQ2⟩, ⟨hP, chP, hleP, hP1, hP0, hP2⟩⟩ := hfun
  rw [← hj] at hQ0 hP0 hKQray hKPray
  refine ⟨i, j, hj, hang, ⟨KQ, lQ, hKQpt, hKQang, hKQray, ?_⟩, ⟨KP, lP, hKPpt, hKPang, hKPray, ?_⟩⟩
  · exact T4_tile_side D hα hS i j hang (j + 2) (j + 1) (Or.inr ⟨rfl, rfl⟩) KQ lQ hKQpt hKQang hQ chQ hleQ hQ1 hQ0 hQ2
  · exact T4_tile_side D hα hS i j hang (j + 1) (j + 2) (Or.inl ⟨rfl, rfl⟩) KP lP hKPpt hKPang hP chP hleP hP1 hP0 hP2

end Erdos634.GLC

#print axioms Erdos634.GLC.corner_G1_T4
