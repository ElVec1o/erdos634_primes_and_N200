import Mathlib.Tactic
import Erdos634.Draft.GLCG1
import Erdos634.Draft.GLCRay

/-!
# `T4 = T + c u`: the second tile on a side, with the corner tile's edge length on the side, is the translate of the corner tile

`T4_points` (pure plane geometry): `O` the corner, `T = {O,P,Q}` the corner tile with angle `θ` at `O`; `K` a tile with angle `θ` at `Q`, one edge `QA1` along the ray `O→Q`
of the same length as `OQ` (the "(c,c)" configuration: the second edge on the side equals the first), the other edge `QA2` of the same length as `OP` (the two edges at the
`α`-vertex are `b, c`), `A2` on the target side of the supporting functional `h`: then `A1 = 2Q − O`, `A2 = P + Q − O`, i.e. `K = T + (Q − O)`.
Method: `ray_determined` (a ray in the half-plane is fixed by angle and length); NO tile-placement or sector-filling hypothesis.
`corner_G1_T4`: wired to `GLCG1.corner_G1` at a real `α`-corner: the second tile `K_Q` at `Q` (from G1) satisfies: if its edge along the side has length `|OQ|`,
then `K_Q = T + (Q − O)`, with its `α`-vertex at `Q`, `b`-edge exactly along `QZ`, `Z = P + Q − O`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Cone Erdos634.Pi3F6 Erdos634.Pi3Tile

variable {N : ℕ}

theorem T4_points {O P Q A1 A2 : Plane} {θ : ℝ} (hu : Q - O ≠ 0)
    (hT : InnerProductGeometry.angle (P - O) (Q - O) = θ)
    (hK : InnerProductGeometry.angle (A1 - Q) (A2 - Q) = θ)
    (hray : SameRay ℝ (Q - O) (A1 - Q)) (hl1 : ‖A1 - Q‖ = ‖Q - O‖) (hl2 : ‖A2 - Q‖ = ‖P - O‖)
    (h : Plane →ₗ[ℝ] ℝ) {ch : ℝ} (hhQ : h Q = ch) (hhO : h O = ch) (hhP : h P < ch) (hhA2 : h A2 ≤ ch) :
    A1 = Q + (Q - O) ∧ A2 = P + Q - O := by
  have hne : A1 - Q ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hl1; exact hu (norm_eq_zero.mp hl1.symm)
  obtain ⟨t, ht0, ht⟩ := Erdos634.Pi3F6.rayparam hu hne hray
  have ht1 : t = 1 := by
    have := hl1
    rw [ht, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at this
    have hpos : 0 < ‖Q - O‖ := norm_pos_iff.mpr hu
    nlinarith
  rw [ht1, one_smul] at ht
  refine ⟨sub_eq_iff_eq_add'.mp ht, ?_⟩
  have hK' : InnerProductGeometry.angle (Q - O) (A2 - Q) = θ := by rw [ht] at hK; exact hK
  have hT' : InnerProductGeometry.angle (Q - O) (P - O) = θ := by
    rw [InnerProductGeometry.angle_comm]; exact hT
  have hi : inner ℝ (Q - O) (A2 - Q) = inner ℝ (Q - O) (P - O) := by
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm, ← InnerProductGeometry.cos_angle_mul_norm_mul_norm,
      hK', hT', hl2]
  have hhu : h (Q - O) = 0 := by rw [map_sub, hhQ, hhO]; ring
  have hhw : h (P - O) < 0 := by rw [map_sub, hhO]; linarith
  have hhe : h (A2 - Q) ≤ 0 := by rw [map_sub, hhQ]; linarith
  have := ray_determined (Q - O) (P - O) (A2 - Q) hu h hhu hhw hhe hl2 hi
  have h2 : A2 = P - O + Q := by rw [← this]; abel
  rw [h2]; abel

/-- The two edges at the `α`-vertex of a tile have lengths `b` and `c`, in one order. -/
theorem edges_at_alpha {U : Tri} {α a b c : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hU : U.TwoAlphaData α a b c) (hab : a ≠ b) (hac : a ≠ c) (l : Fin 3) (hl : U.angleAt l = α) :
    (dist (U.pts l) (U.pts (l + 1)) = c ∧ dist (U.pts l) (U.pts (l + 2)) = b) ∨
    (dist (U.pts l) (U.pts (l + 1)) = b ∧ dist (U.pts l) (U.pts (l + 2)) = c) := by
  have hopp := opp_a_of_alpha hirr hU l hl
  have hor := tri_orient_a hU hab hac l hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  rcases hor with ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩
  · left; exact ⟨h3, by rw [dist_comm]; exact h1⟩
  · right; exact ⟨h3, by rw [dist_comm]; exact h1⟩

/-- A supporting functional of a target side `[k, W]`, strictly negative at the third vertex `V`. -/
theorem side_functional (T : Tri) (k W V : Fin 3) (hWV : (W = k + 1 ∧ V = k + 2) ∨ (W = k + 2 ∧ V = k + 1)) :
    ∃ (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ), h ≠ 0 ∧ (∀ y ∈ T.carrier, h y ≤ ch) ∧
      h (T.pts k) = ch ∧ h (T.pts W) = ch ∧ h (T.pts V) < ch := by
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (exists_supporting T k)
  · obtain ⟨f, c0, hf, hle, h0, h1, h2⟩ := exists_supporting T (k + 2)
    rw [(by decide : ∀ x : Fin 3, x + 2 + 1 = x) k] at h1
    rw [(by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) k] at h2
    exact ⟨f, c0, hf, hle, h1, h0, h2⟩

/-- Length bookkeeping: the two edges at the `α`-vertex are `{b, c}`; if the first edge of `K` equals `|OX|` then the second equals `|OY|`. -/
theorem T4_pts_full {O X Y A1 A2 : Plane} {α b c : ℝ} (hbc : b ≠ c) (hu : X - O ≠ 0)
    (hT : InnerProductGeometry.angle (Y - O) (X - O) = α)
    (hK : InnerProductGeometry.angle (A1 - X) (A2 - X) = α)
    (hTp : (dist O X = c ∧ dist O Y = b) ∨ (dist O X = b ∧ dist O Y = c))
    (hKp : (dist X A1 = c ∧ dist X A2 = b) ∨ (dist X A1 = b ∧ dist X A2 = c))
    (hray : SameRay ℝ (X - O) (A1 - X)) (hl : dist X A1 = dist O X)
    (h : Plane →ₗ[ℝ] ℝ) {ch : ℝ} (hhX : h X = ch) (hhO : h O = ch) (hhY : h Y < ch) (hhA2 : h A2 ≤ ch) :
    A1 = X + (X - O) ∧ A2 = Y + X - O := by
  have key : dist X A2 = dist O Y := by
    rcases hTp with ⟨t1, t2⟩ | ⟨t1, t2⟩ <;> rcases hKp with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rw [k2, t2]
    · exact absurd (by linarith) hbc
    · exact absurd (by linarith) hbc
    · rw [k2, t2]
  refine T4_points hu hT hK hray ?_ ?_ h hhX hhO hhY hhA2
  · rw [← dist_eq_norm, dist_comm, hl, dist_eq_norm, norm_sub_rev]
  · rw [← dist_eq_norm, dist_comm, key, dist_eq_norm, norm_sub_rev]

/-- **`T4 = T + (X − O)` on a real dissection.**  `T = tile i` has the `α`-vertex `O = pts j`; `X = pts m1`, `Y = pts m2` its other vertices (either order);
`K` a tile with an `α`-vertex at `X`; `h` a supporting functional of the target side through `O, X`, strictly smaller at `Y`.  If an edge of `K` at `X` runs along the ray `O→X`
and has length `|OX|`, then `K` is the translate of `T` by `X − O`: that edge ends at `2X − O`, the other edge ends at `Y + X − O`. -/
theorem T4_tile_side (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (i : Fin N) (j : Fin 3) (hang : (D.tile i).angleAt j = α)
    (m1 m2 : Fin 3) (hm : (m1 = j + 1 ∧ m2 = j + 2) ∨ (m1 = j + 2 ∧ m2 = j + 1))
    (K : Fin N) (l : Fin 3) (hKpt : (D.tile K).pts l = (D.tile i).pts m1) (hKang : (D.tile K).angleAt l = α)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhX : h ((D.tile i).pts m1) = ch) (hhO : h ((D.tile i).pts j) = ch) (hhY : h ((D.tile i).pts m2) < ch) :
    (SameRay ℝ ((D.tile i).pts m1 - (D.tile i).pts j) ((D.tile K).pts (l + 1) - (D.tile i).pts m1) →
      dist ((D.tile i).pts m1) ((D.tile K).pts (l + 1)) = dist ((D.tile i).pts j) ((D.tile i).pts m1) →
      (D.tile K).pts (l + 1) = (D.tile i).pts m1 + ((D.tile i).pts m1 - (D.tile i).pts j) ∧
      (D.tile K).pts (l + 2) = (D.tile i).pts m2 + (D.tile i).pts m1 - (D.tile i).pts j) ∧
    (SameRay ℝ ((D.tile i).pts m1 - (D.tile i).pts j) ((D.tile K).pts (l + 2) - (D.tile i).pts m1) →
      dist ((D.tile i).pts m1) ((D.tile K).pts (l + 2)) = dist ((D.tile i).pts j) ((D.tile i).pts m1) →
      (D.tile K).pts (l + 2) = (D.tile i).pts m1 + ((D.tile i).pts m1 - (D.tile i).pts j) ∧
      (D.tile K).pts (l + 1) = (D.tile i).pts m2 + (D.tile i).pts m1 - (D.tile i).pts j) := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα hS
  have hTt := edges_at_alpha hα (tile_twoalpha D hS i) hab hac j hang
  have hKt := edges_at_alpha hα (tile_twoalpha D hS K) hab hac l hKang
  rw [hKpt] at hKt
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have ang0 : InnerProductGeometry.angle ((D.tile i).pts (j + 1) - (D.tile i).pts j)
      ((D.tile i).pts (j + 2) - (D.tile i).pts j) = α := by
    rw [← hang]; unfold Tri.angleAt cornerAngle EuclideanGeometry.angle; simp only [vsub_eq_sub]
  have angK : InnerProductGeometry.angle ((D.tile K).pts (l + 1) - (D.tile i).pts m1)
      ((D.tile K).pts (l + 2) - (D.tile i).pts m1) = α := by
    rw [← hKpt, ← hKang]; unfold Tri.angleAt cornerAngle EuclideanGeometry.angle; simp only [vsub_eq_sub]
  have hA2a : h ((D.tile K).pts (l + 2)) ≤ ch := hh _ (Erdos634.BaseSelection.tile_subset_target D.toDissection K
    (subset_convexHull ℝ _ ⟨l + 2, rfl⟩))
  have hA2b : h ((D.tile K).pts (l + 1)) ≤ ch := hh _ (Erdos634.BaseSelection.tile_subset_target D.toDissection K
    (subset_convexHull ℝ _ ⟨l + 1, rfl⟩))
  have hT : InnerProductGeometry.angle ((D.tile i).pts m2 - (D.tile i).pts j) ((D.tile i).pts m1 - (D.tile i).pts j) = α ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts m1) = c ∧ dist ((D.tile i).pts j) ((D.tile i).pts m2) = b) ∨
       (dist ((D.tile i).pts j) ((D.tile i).pts m1) = b ∧ dist ((D.tile i).pts j) ((D.tile i).pts m2) = c)) ∧
      (D.tile i).pts m1 - (D.tile i).pts j ≠ 0 := by
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨by rw [InnerProductGeometry.angle_comm]; exact ang0, hTt, ?_⟩
      rw [sub_ne_zero]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
    · refine ⟨ang0, ?_, ?_⟩
      · rcases hTt with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inr ⟨e2, e1⟩
        · exact Or.inl ⟨e2, e1⟩
      · rw [sub_ne_zero]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  obtain ⟨hT1, hT2, hT3⟩ := hT
  refine ⟨fun hray hl => ?_, fun hray hl => ?_⟩
  · exact T4_pts_full hbc hT3 hT1 angK hT2 (by rw [← hKpt] at hKt ⊢; exact hKt) hray hl h hhX hhO hhY hA2a
  · refine T4_pts_full hbc hT3 hT1 (by rw [InnerProductGeometry.angle_comm]; exact angK) hT2 ?_ hray hl h hhX hhO hhY hA2b
    rcases hKt with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr ⟨e2, e1⟩
    · exact Or.inl ⟨e2, e1⟩

end Erdos634.GLC

#print axioms Erdos634.GLC.T4_tile_side
