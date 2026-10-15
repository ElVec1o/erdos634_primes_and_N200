import Mathlib.Tactic
import Erdos634.Draft.GLCReflect
import Erdos634.Draft.T30LC2Forward
import Erdos634.Draft.T30LSectorFill
import Erdos634.MarchFlank
import Erdos634.CornerAnglePerm

/-!
# The forward tile at a non-vertex frontier point, `γ = 2α` tile (G1, "the second tile on the side starts with `α`")

`forward_tile_2a`: port of `C2Forward.forward_tile` to the `γ = 2α` tile.  Let `P` be a non-vertex frontier point of the target, `u ≠ 0` a direction along
the target side at `P` (`g P = cg`, `g u = 0`, `g ≠ 0` supporting), the forward segment `P + εu` in the target, and suppose tiles `iβ, iγ` present `β = π − 3α` and
`γ = 2α` at `P` and neither contains the forward points.  Then there is a tile `K` with a vertex at `P` of angle `α`, one of whose two edges at `P`
lies on the ray `ℝ≥0 u` (`SameRay`).  Method as in the original: cover `P + εu` by a tile `K0`; the fan at `P` is `(α,β,γ)` (`boundary_fan_2alpha`),
`K0 ≠ iβ, iγ`, so `K0` is THE `α`-tile; the cone/kernel argument puts `u` on an edge (two edges on the line `g = 0` would be parallel, but make angle `α ∈ (0,π)`).
Applied with `iβ, iγ` = the corner tile `T` and its point reflection `T2` (`GLCCorner.corner_far_reflection_2a`: `T2` has `γ` where `T` has `β` or conversely), this is
(G1): the second tile on each side starts with `α`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.SectorFill Erdos634.Pi3Cone Erdos634.C2Forward

variable {N : ℕ}

theorem unique_of_cntA (D : CongruentDissection N) {v : Plane} {θ : ℝ} (h : cntA D v θ = 1) {i j : Fin N}
    (hi : (D.tile i).localAngle v = θ) (hj : (D.tile j).localAngle v = θ) : i = j :=
  unique_of_cnt D.toDissection h hi hj

theorem none_of_cntA (D : CongruentDissection N) {v : Plane} {θ : ℝ} (h : cntA D v θ = 0) {i : Fin N}
    (hi : (D.tile i).localAngle v = θ) : False := none_of_cnt D.toDissection h hi

/-- Two vectors at angle `θ ∈ (0,π)` are not parallel. -/
theorem cross_ne_of_angle' {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi) {x y : Plane} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : InnerProductGeometry.angle x y = θ) : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
  intro hc
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm x y
  rw [h] at hcos
  have hxx : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [← real_inner_self_eq_norm_sq, inner_coord]; ring
  have hyy : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by rw [← real_inner_self_eq_norm_sq, inner_coord]; ring
  rw [inner_coord] at hcos
  have hpx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpy : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hlag : (x 0 * y 0 + x 1 * y 1) ^ 2 = (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
    have : (x 0 * y 0 + x 1 * y 1) ^ 2 + (x 0 * y 1 - x 1 * y 0) ^ 2
        = (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by ring
    rw [hc] at this; linarith
  rw [← hcos, ← hxx, ← hyy] at hlag
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 h1
  have hsc := Real.sin_sq_add_cos_sq θ
  have hpos : 0 < (‖x‖ * ‖y‖) ^ 2 := by positivity
  have : (Real.sin θ) ^ 2 * (‖x‖ * ‖y‖) ^ 2 = 0 := by nlinarith
  have := mul_eq_zero.mp this
  rcases this with h' | h'
  · nlinarith
  · linarith

set_option maxHeartbeats 800000 in
theorem forward_tile_2a (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    {P u : Plane} (hP : P ∈ frontier D.target.carrier)
    (hnv : P ∉ Set.range D.target.pts) (hu : u ≠ 0)
    (g : Plane →ₗ[ℝ] ℝ) (hg0 : g ≠ 0) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgu : g u = 0)
    {ε0 : ℝ} (hε0 : 0 < ε0) (hin : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∈ D.target.carrier)
    (iβ iγ : Fin N) (hiβ : (D.tile iβ).localAngle P = Real.pi - 3 * α)
    (hiγ : (D.tile iγ).localAngle P = 2 * α)
    (hnβ : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∉ (D.tile iβ).carrier)
    (hnγ : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∉ (D.tile iγ).carrier) :
    ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = P ∧ (D.tile K).angleAt l = α ∧
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
  have hK0γ : K0 ≠ iγ := by rintro rfl; exact hnγ ε hεpos hεle hyK0
  -- the fan at `P` is `(α, β, γ)`
  obtain ⟨hn2, hfan⟩ := boundary_fan_2alpha D hα hS hP hnv
  have hcβ : 0 < cntA D P (Real.pi - 3 * α) := Finset.card_pos.mpr ⟨iβ, by simp [hiβ]⟩
  have hcγ : 0 < cntA D P (2 * α) := Finset.card_pos.mpr ⟨iγ, by simp [hiγ]⟩
  have hfig : cntA D P α = 1 ∧ cntA D P (Real.pi - 3 * α) = 1 ∧ cntA D P (2 * α) = 1 ∧ cntA D P Real.pi = 0 := by
    rcases hfan with h | h | h <;> omega
  have hvals := Row4.localAngle_mem D hS P K0
  have hne0 := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile K0) hPK0
  have hθ : (D.tile K0).localAngle P = α := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvals
    rcases hvals with h | h | h | h | h | h
    · exact h
    · exact absurd (unique_of_cntA D hfig.2.1 h hiβ) hK0β
    · exact absurd (unique_of_cntA D hfig.2.2.1 h hiγ) hK0γ
    · exact (none_of_cntA D hfig.2.2.2 h).elim
    · exact (none_of_cntA D hn2 h).elim
    · exact absurd h hne0
  obtain ⟨l, hl⟩ := Erdos634.Geometry.vertex_of_localAngle_corner (D.tile K0) hθ hα0.ne' (by intro h; linarith)
    (by intro h; linarith)
  have hangl : (D.tile K0).angleAt l = α := by
    have h1 : (D.tile K0).localAngle ((D.tile K0).pts l) = α := by rw [hl]; exact hθ
    rw [Tri.localAngle_vertex] at h1
    exact h1
  refine ⟨K0, l, hl, hangl, ?_⟩
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
      = α := by
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
      exact cross_ne_of_angle' hα0 (by linarith) he1 he2 hang (cross_zero_of_ker g hg0 h1 h2)

end Erdos634.GLC

#print axioms Erdos634.GLC.forward_tile_2a
