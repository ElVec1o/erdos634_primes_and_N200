import Mathlib.Tactic
import Erdos634.Draft.GLCT4Wire

/-!
# `T3` in G2 Case 2: the second tile on the `b`-side with a `c`-edge on the side has its `b`-edge along `Y → Y + (b/c)(X − O)`

`T3_points` (plane geometry): `O` the corner, `Y, X` the other vertices of the corner tile with `‖Y − O‖ = b'`, `‖X − O‖ = c'`; `K` a tile with angle `θ` at `Y` (`θ` the corner angle), one edge `YA1` along the ray `O → Y`
of length `c'` and the other edge `YA2` of length `b'`, `A2` on the target side of the supporting functional `g` of the side `OY`: then `A1 = Y + (c'/b')(Y − O)` and `A2 = Y + (b'/c')(X − O)`
(the second edge runs along the OTHER side direction, so it ends strictly inside `[Y, Z]` when `b' < c'`).
`T3_tile_side`: the same on a real dissection (indices as in `T4_tile_side`).
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Cone Erdos634.Pi3F6 Erdos634.Pi3Tile

variable {N : ℕ}

theorem T3_points {O Y X A1 A2 : Plane} {θ : ℝ} (hu : Y - O ≠ 0) (hx : X - O ≠ 0)
    (hT : InnerProductGeometry.angle (Y - O) (X - O) = θ)
    (hK : InnerProductGeometry.angle (A1 - Y) (A2 - Y) = θ)
    (hray : SameRay ℝ (Y - O) (A1 - Y)) (hl1 : ‖A1 - Y‖ = ‖X - O‖) (hl2 : ‖A2 - Y‖ = ‖Y - O‖)
    (g : Plane →ₗ[ℝ] ℝ) {cg : ℝ} (hgY : g Y = cg) (hgO : g O = cg) (hgX : g X < cg) (hgA2 : g A2 ≤ cg) :
    A1 = Y + (‖X - O‖ / ‖Y - O‖) • (Y - O) ∧ A2 = Y + (‖Y - O‖ / ‖X - O‖) • (X - O) := by
  have hne : A1 - Y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hl1; exact hx (norm_eq_zero.mp hl1.symm)
  have hpu : 0 < ‖Y - O‖ := norm_pos_iff.mpr hu
  have hpx : 0 < ‖X - O‖ := norm_pos_iff.mpr hx
  obtain ⟨t, ht0, ht⟩ := rayparam hu hne hray
  have ht1 : t = ‖X - O‖ / ‖Y - O‖ := by
    have := hl1
    rw [ht, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at this
    field_simp; linarith
  have hA1 : A1 = Y + t • (Y - O) := by rw [← ht]; abel
  refine ⟨by rw [hA1, ht1], ?_⟩
  have hK' : InnerProductGeometry.angle (t • (Y - O)) (A2 - Y) = θ := by rw [ht] at hK; exact hK
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ht0] at hK'
  have hi1 : inner ℝ (Y - O) (A2 - Y) = Real.cos θ * (‖Y - O‖ * ‖Y - O‖) := by
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm, hK', hl2]
  have hi2 : inner ℝ (Y - O) (X - O) = Real.cos θ * (‖Y - O‖ * ‖X - O‖) := by
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm, hT]
  set s : ℝ := ‖Y - O‖ / ‖X - O‖ with hs
  have hs0 : 0 < s := div_pos hpu hpx
  have hhu : g (Y - O) = 0 := by rw [map_sub, hgY, hgO]; ring
  have hhw : g (s • (X - O)) < 0 := by
    rw [map_smul, map_sub, hgO]; exact mul_neg_of_pos_of_neg hs0 (by linarith)
  have hhe : g (A2 - Y) ≤ 0 := by rw [map_sub, hgY]; linarith
  have key := ray_determined (Y - O) (s • (X - O)) (A2 - Y) hu g hhu hhw hhe
    (by rw [hl2, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hs]; field_simp)
    (by rw [hi1, inner_smul_right, hi2, hs]; field_simp)
  have : A2 = (A2 - Y) + Y := by abel
  rw [this, key]; abel

theorem T3_tile_side (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (i : Fin N) (j : Fin 3) (hang : (D.tile i).angleAt j = α)
    (m1 m2 : Fin 3) (hm : (m1 = j + 1 ∧ m2 = j + 2) ∨ (m1 = j + 2 ∧ m2 = j + 1))
    (K : Fin N) (l : Fin 3) (hKpt : (D.tile K).pts l = (D.tile i).pts m1) (hKang : (D.tile K).angleAt l = α)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhX : h ((D.tile i).pts m1) = ch) (hhO : h ((D.tile i).pts j) = ch) (hhY : h ((D.tile i).pts m2) < ch) :
    (SameRay ℝ ((D.tile i).pts m1 - (D.tile i).pts j) ((D.tile K).pts (l + 1) - (D.tile i).pts m1) →
      dist ((D.tile i).pts m1) ((D.tile K).pts (l + 1)) = dist ((D.tile i).pts j) ((D.tile i).pts m2) →
      (D.tile K).pts (l + 1) = (D.tile i).pts m1 + (‖(D.tile i).pts m2 - (D.tile i).pts j‖ /
          ‖(D.tile i).pts m1 - (D.tile i).pts j‖) • ((D.tile i).pts m1 - (D.tile i).pts j) ∧
      (D.tile K).pts (l + 2) = (D.tile i).pts m1 + (‖(D.tile i).pts m1 - (D.tile i).pts j‖ /
          ‖(D.tile i).pts m2 - (D.tile i).pts j‖) • ((D.tile i).pts m2 - (D.tile i).pts j)) ∧
    (SameRay ℝ ((D.tile i).pts m1 - (D.tile i).pts j) ((D.tile K).pts (l + 2) - (D.tile i).pts m1) →
      dist ((D.tile i).pts m1) ((D.tile K).pts (l + 2)) = dist ((D.tile i).pts j) ((D.tile i).pts m2) →
      (D.tile K).pts (l + 2) = (D.tile i).pts m1 + (‖(D.tile i).pts m2 - (D.tile i).pts j‖ /
          ‖(D.tile i).pts m1 - (D.tile i).pts j‖) • ((D.tile i).pts m1 - (D.tile i).pts j) ∧
      (D.tile K).pts (l + 1) = (D.tile i).pts m1 + (‖(D.tile i).pts m1 - (D.tile i).pts j‖ /
          ‖(D.tile i).pts m2 - (D.tile i).pts j‖) • ((D.tile i).pts m2 - (D.tile i).pts j)) := by
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
  have hT : InnerProductGeometry.angle ((D.tile i).pts m1 - (D.tile i).pts j) ((D.tile i).pts m2 - (D.tile i).pts j) = α ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts m1) = c ∧ dist ((D.tile i).pts j) ((D.tile i).pts m2) = b) ∨
       (dist ((D.tile i).pts j) ((D.tile i).pts m1) = b ∧ dist ((D.tile i).pts j) ((D.tile i).pts m2) = c)) ∧
      (D.tile i).pts m1 - (D.tile i).pts j ≠ 0 ∧ (D.tile i).pts m2 - (D.tile i).pts j ≠ 0 := by
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨ang0, hTt, ?_, ?_⟩
      · rw [sub_ne_zero]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
      · rw [sub_ne_zero]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
    · refine ⟨by rw [InnerProductGeometry.angle_comm]; exact ang0, ?_, ?_, ?_⟩
      · rcases hTt with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inr ⟨e2, e1⟩
        · exact Or.inl ⟨e2, e1⟩
      · rw [sub_ne_zero]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
      · rw [sub_ne_zero]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hT
  have hnn1 : ‖(D.tile i).pts m1 - (D.tile i).pts j‖ = dist ((D.tile i).pts j) ((D.tile i).pts m1) := by
    rw [← dist_eq_norm, dist_comm]
  have hnn2 : ‖(D.tile i).pts m2 - (D.tile i).pts j‖ = dist ((D.tile i).pts j) ((D.tile i).pts m2) := by
    rw [← dist_eq_norm, dist_comm]
  have hlen : ∀ A1 A2 : Plane, dist ((D.tile i).pts m1) A1 = dist ((D.tile i).pts j) ((D.tile i).pts m2) →
      ((dist ((D.tile i).pts m1) A1 = c ∧ dist ((D.tile i).pts m1) A2 = b) ∨
       (dist ((D.tile i).pts m1) A1 = b ∧ dist ((D.tile i).pts m1) A2 = c)) →
      ‖A1 - (D.tile i).pts m1‖ = ‖(D.tile i).pts m2 - (D.tile i).pts j‖ ∧
      ‖A2 - (D.tile i).pts m1‖ = ‖(D.tile i).pts m1 - (D.tile i).pts j‖ := by
    intro A1 A2 hl hKp
    have h1 : ‖A1 - (D.tile i).pts m1‖ = ‖(D.tile i).pts m2 - (D.tile i).pts j‖ := by
      rw [← dist_eq_norm, dist_comm, hl, ← hnn2]
    refine ⟨h1, ?_⟩
    have h2 : dist ((D.tile i).pts m1) A2 = dist ((D.tile i).pts j) ((D.tile i).pts m1) := by
      rcases hT2 with ⟨t1, t2⟩ | ⟨t1, t2⟩ <;> rcases hKp with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact absurd (by linarith) hbc
      · rw [k2, t1]
      · rw [k2, t1]
      · exact absurd (by linarith) hbc
    rw [← dist_eq_norm, dist_comm, h2, ← hnn1]
  refine ⟨fun hray hl => ?_, fun hray hl => ?_⟩
  · obtain ⟨n1, n2⟩ := hlen _ _ hl hKt
    exact T3_points hT3 hT4 hT1 angK hray n1 n2 h hhX hhO hhY hA2a
  · obtain ⟨n1, n2⟩ := hlen _ _ hl (by
      rcases hKt with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inr ⟨e2, e1⟩
      · exact Or.inl ⟨e2, e1⟩)
    exact T3_points hT3 hT4 hT1 (by rw [InnerProductGeometry.angle_comm]; exact angK) hray n1 n2 h hhX hhO hhY hA2b

end Erdos634.GLC

#print axioms Erdos634.GLC.T3_tile_side
