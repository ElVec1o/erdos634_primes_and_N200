import Mathlib.Tactic
import Erdos634.Draft.GLCForward

/-!
# A tile with a vertex at a non-vertex frontier point and an edge along the forward ray (angle `α` or `γ`)

`forward_edge_2a`: the generalization of `GLCForward.forward_tile_2a` that does NOT assume a `γ` tile at `P`: let `P` be a non-vertex frontier point, `u` the forward direction along the side, `iβ` a tile with `β` at `P` missing the forward points.
Then some tile `K` has a vertex at `P` of angle `α` OR `γ` with an edge along the ray `ℝ≥0 u` (the tile covering `P + εu` has `P` as a corner (no `π` and no `2π` in the fan), is not `iβ` (`β` is unique), so presents `α` or `γ`;
the cone argument puts `u` on an edge).  Same proof as `forward_tile_2a`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.SectorFill Erdos634.Pi3Cone Erdos634.C2Forward

variable {N : ℕ}

set_option maxHeartbeats 800000 in
theorem forward_edge_2a (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    {P u : Plane} (hP : P ∈ frontier D.target.carrier)
    (hnv : P ∉ Set.range D.target.pts) (hu : u ≠ 0)
    (g : Plane →ₗ[ℝ] ℝ) (hg0 : g ≠ 0) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgu : g u = 0)
    {ε0 : ℝ} (hε0 : 0 < ε0) (hin : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∈ D.target.carrier)
    (iβ : Fin N) (hiβ : (D.tile iβ).localAngle P = Real.pi - 3 * α)
    (hnβ : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∉ (D.tile iβ).carrier) :
    ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = P ∧
      ((D.tile K).angleAt l = α ∨ (D.tile K).angleAt l = 2 * α) ∧
      (SameRay ℝ u ((D.tile K).pts (l + 1) - P) ∨ SameRay ℝ u ((D.tile K).pts (l + 2) - P)) := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D hS
  classical
  have hpi := Real.pi_pos
  -- the tiles missing `P` are at positive distance
  have hBadClosed : IsClosed (⋃ i ∈ ({i | P ∉ (D.tile i).carrier} : Finset (Fin N)), (D.tile i).carrier) := by
    refine isClosed_biUnion_finset ?_
    intro i _
    exact (Tri.isCompact _).isClosed
  have hPnot : P ∉ (⋃ i ∈ ({i | P ∉ (D.tile i).carrier} : Finset (Fin N)), (D.tile i).carrier) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop, not_exists, not_and]
    intro i hi hmem
    exact hi hmem
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hBadClosed.isOpen_compl P hPnot
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set ε : ℝ := min ε0 (δ / (2 * ‖u‖)) with hε
  have hεpos : 0 < ε := lt_min hε0 (by positivity)
  have hεle : ε ≤ ε0 := min_le_left _ _
  have hεδ : ε * ‖u‖ < δ := by
    have h1 : ε ≤ δ / (2 * ‖u‖) := min_le_right _ _
    have h2 : ε * ‖u‖ ≤ δ / (2 * ‖u‖) * ‖u‖ := by gcongr
    have h3 : δ / (2 * ‖u‖) * ‖u‖ = δ / 2 := by field_simp
    linarith
  -- a tile `K0` covering `P + εu`
  have hy := hin ε hεpos hεle
  rw [← D.covers] at hy
  obtain ⟨K0, hyK0⟩ := Set.mem_iUnion.mp hy
  have hPK0 : P ∈ (D.tile K0).carrier := by
    by_contra hnot
    have hyb : P + ε • u ∈ (⋃ i ∈ ({i | P ∉ (D.tile i).carrier} : Finset (Fin N)), (D.tile i).carrier) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
      exact ⟨K0, hnot, hyK0⟩
    have hd : P + ε • u ∈ Metric.ball P δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
      exact hεδ
    exact hball hd hyb
  have hK0β : K0 ≠ iβ := by rintro rfl; exact hnβ ε hεpos hεle hyK0
  -- the fan at `P`: exactly one `β`, no `π`
  obtain ⟨hn2, hfan⟩ := boundary_fan_2alpha D hα hS hP hnv
  have hcβ : 0 < cntA D P (Real.pi - 3 * α) := Finset.card_pos.mpr ⟨iβ, by simp [hiβ]⟩
  have hfig : cntA D P (Real.pi - 3 * α) = 1 ∧ cntA D P Real.pi = 0 := by
    rcases hfan with h | h | h <;> omega
  have hvals := Row4.localAngle_mem D hS P K0
  have hne0 := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile K0) hPK0
  have hθ : (D.tile K0).localAngle P = α ∨ (D.tile K0).localAngle P = 2 * α := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvals
    rcases hvals with h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd (unique_of_cntA D hfig.1 h hiβ) hK0β
    · exact Or.inr h
    · exact (none_of_cntA D hfig.2 h).elim
    · exact (none_of_cntA D hn2 h).elim
    · exact absurd h hne0
  have hθ0 : (D.tile K0).localAngle P ≠ 0 := by
    rcases hθ with h | h <;> rw [h] <;> intro h' <;> linarith
  have hθπ : (D.tile K0).localAngle P ≠ Real.pi := by
    rcases hθ with h | h <;> rw [h] <;> intro h' <;> linarith
  have hθ2π : (D.tile K0).localAngle P ≠ 2 * Real.pi := by
    rcases hθ with h | h <;> rw [h] <;> intro h' <;> linarith
  obtain ⟨l, hl⟩ := Erdos634.Geometry.vertex_of_localAngle_corner (D.tile K0) rfl hθ0 hθπ hθ2π
  have hangl : (D.tile K0).angleAt l = (D.tile K0).localAngle P := by
    have h1 : (D.tile K0).localAngle ((D.tile K0).pts l) = (D.tile K0).localAngle P := by rw [hl]
    rw [Tri.localAngle_vertex] at h1
    exact h1
  refine ⟨K0, l, hl, by rw [hangl]; exact hθ, ?_⟩
  -- cone of `K0` at `P`
  obtain ⟨s, t, hs, ht, hst⟩ := hull_cone (D.tile K0) l _ hyK0
  rw [hl] at hst
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile K0).pts m ≠ (D.tile K0).pts n :=
    fun m n h hh => h ((D.tile K0).indep.injective hh)
  have he1 : (D.tile K0).pts (l + 1) - P ≠ 0 := by
    rw [sub_ne_zero, ← hl]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) l)).symm
  have he2 : (D.tile K0).pts (l + 2) - P ≠ 0 := by
    rw [sub_ne_zero, ← hl]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) l)).symm
  have hg1 : g ((D.tile K0).pts (l + 1) - P) ≤ 0 := by
    have := vertex_dir_nonpos D.toDissection K0 l (l + 1) g cg hg (by rw [hl]; exact hgP)
    rwa [hl] at this
  have hg2 : g ((D.tile K0).pts (l + 2) - P) ≤ 0 := by
    have := vertex_dir_nonpos D.toDissection K0 l (l + 2) g cg hg (by rw [hl]; exact hgP)
    rwa [hl] at this
  have hang : InnerProductGeometry.angle ((D.tile K0).pts (l + 1) - P) ((D.tile K0).pts (l + 2) - P)
      = (D.tile K0).localAngle P := by
    have := hangl
    unfold Tri.angleAt cornerAngle EuclideanGeometry.angle at this
    simp only [vsub_eq_sub] at this
    rw [hl] at this
    exact this
  set e1 := (D.tile K0).pts (l + 1) - P with he1def
  set e2 := (D.tile K0).pts (l + 2) - P with he2def
  have hεu : ε • u = s • e1 + t • e2 := by
    have : P + ε • u - P = ε • u := by abel
    rw [← this]; exact hst
  have hgε : s * g e1 + t * g e2 = 0 := by
    have := congrArg g hεu
    rw [map_smul, hgu, map_add, map_smul, map_smul] at this
    simp only [smul_eq_mul, mul_zero] at this
    linarith
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · -- `s = 0`
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le ht with h | h
      · exfalso
        rw [← hs0, ← h] at hεu
        simp only [zero_smul, add_zero] at hεu
        exact hu ((smul_eq_zero.mp hεu).resolve_left hεpos.ne')
      · exact h
    right
    have : e2 = (ε / t) • u := by
      calc e2 = t⁻¹ • (t • e2) := by rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
        _ = t⁻¹ • (ε • u) := by rw [← hs0] at hεu; simp only [zero_smul, zero_add] at hεu; rw [hεu]
        _ = (ε / t) • u := by rw [smul_smul]; congr 1; field_simp
    rw [this]
    exact SameRay.sameRay_pos_smul_right u (by positivity)
  · rcases eq_or_lt_of_le ht with ht0 | ht0
    · -- `t = 0`
      left
      have : e1 = (ε / s) • u := by
        calc e1 = s⁻¹ • (s • e1) := by rw [smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
          _ = s⁻¹ • (ε • u) := by rw [← ht0] at hεu; simp only [zero_smul, add_zero] at hεu; rw [hεu]
          _ = (ε / s) • u := by rw [smul_smul]; congr 1; field_simp
      rw [this]
      exact SameRay.sameRay_pos_smul_right u (by positivity)
    · -- `s, t > 0`: both edges on the line `g = 0`, impossible at angle `π/3`
      exfalso
      have h1 : g e1 = 0 := by nlinarith [mul_nonneg hs0.le (neg_nonneg.mpr hg1), mul_nonneg ht0.le (neg_nonneg.mpr hg2)]
      have h2 : g e2 = 0 := by nlinarith [mul_nonneg hs0.le (neg_nonneg.mpr hg1), mul_nonneg ht0.le (neg_nonneg.mpr hg2)]
      have hθpos : 0 < (D.tile K0).localAngle P := by rcases hθ with h | h <;> rw [h] <;> linarith
      have hθlt : (D.tile K0).localAngle P < Real.pi := by rcases hθ with h | h <;> rw [h] <;> linarith
      exact cross_ne_of_angle' hθpos hθlt he1 he2 hang (cross_zero_of_ker g hg0 h1 h2)

end Erdos634.GLC

#print axioms Erdos634.GLC.forward_edge_2a
