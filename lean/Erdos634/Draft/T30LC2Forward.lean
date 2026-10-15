import Mathlib.Tactic
import Erdos634.Draft.T30LC2Strong
import Erdos634.Draft.T30LSectorFill
import Erdos634.MarchFlank
import Erdos634.CornerAnglePerm
import Erdos634.VertexFigureReal

/-!
# The forward tile at a non-vertex frontier point

`forward_tile`: on a `CongruentDissection` with a `SixtyData` tile and `α ∉ ℚπ`, let `P` be a non-vertex frontier point of the target and `u ≠ 0` a direction
along the target side at `P` (`g` supporting, `g P = cg`, `g u = 0`), with the forward segment `P + εu` (`0 < ε ≤ ε₀`) in the target.  Suppose the tiles `iα, iβ`
present `α` and `β = 2π/3 − α` at `P` and neither contains the forward points.  Then there is a tile `K` with a vertex at `P` of angle `π/3` and one of its two
edges at `P` is on the ray `ℝ≥0 u`.

Method: the point `P + εu`
is covered by a tile `K`; for `ε` small `K` contains `P` (the tiles missing `P` are at positive distance); `K ≠ iα, iβ` (hypothesis), so by the fan count
(`third_is_P`: exactly one tile per `α`, `β`, `π/3`, none straight) `K` is the `π/3` tile; `P + εu` in the cone of `K` at `P` and `g ≤ 0` on `K`'s edges at `P`
(`vertex_dir_nonpos`) force `u` onto an edge (two edges both on the line `g = 0` would be collinear, but they make an angle `π/3`: `cross_ne_of_angle`).
No cone order, no oriented angle.
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.SectorFill Erdos634.Pi3Cone

theorem inner_coord (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  try ring

/-- Two vectors at angle `π/3` are not parallel. -/
theorem cross_ne_of_angle {x y : Plane} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : InnerProductGeometry.angle x y = Real.pi / 3) : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
  intro hc
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm x y
  rw [h, Real.cos_pi_div_three] at hcos
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
  have h4 : (1 / 2 * (‖x‖ * ‖y‖)) ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 / 4 := by ring
  have hpos : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 := by positivity
  linarith

/-- Two vectors in the kernel of a nonzero functional on the plane are parallel. -/
theorem cross_zero_of_ker (g : Plane →ₗ[ℝ] ℝ) (hg : g ≠ 0) {x y : Plane} (hx : g x = 0) (hy : g y = 0) :
    x 0 * y 1 - x 1 * y 0 = 0 := by
  rw [lin_coord g x] at hx
  rw [lin_coord g y] at hy
  have hg' : g (EuclideanSpace.single 0 1) ≠ 0 ∨ g (EuclideanSpace.single 1 1) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hg
    refine LinearMap.ext fun z => ?_
    rw [lin_coord g z, hcon.1, hcon.2]; simp
  rcases hg' with h | h
  · apply mul_left_cancel₀ h
    linear_combination (y 1) * hx - (x 1) * hy
  · apply mul_left_cancel₀ h
    linear_combination (x 0) * hy - (y 0) * hx

theorem unique_of_cnt {N : ℕ} (D : Dissection N) {v : Plane} {θ : ℝ} (h : cnt D v θ = 1) {i j : Fin N}
    (hi : (D.tile i).localAngle v = θ) (hj : (D.tile j).localAngle v = θ) : i = j := by
  unfold cnt at h
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
  have hi' : i ∈ ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)) := by simp [hi]
  have hj' : j ∈ ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)) := by simp [hj]
  rw [hx] at hi' hj'
  simp only [Finset.mem_singleton] at hi' hj'
  rw [hi', hj']

theorem none_of_cnt {N : ℕ} (D : Dissection N) {v : Plane} {θ : ℝ} (h : cnt D v θ = 0) {i : Fin N}
    (hi : (D.tile i).localAngle v = θ) : False := by
  unfold cnt at h
  have := Finset.card_eq_zero.mp h
  have hi' : i ∈ ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)) := by simp [hi]
  rw [this] at hi'
  simp at hi'

theorem forward_tile {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) {P u : Plane} (hP : P ∈ frontier D.target.carrier)
    (hnv : P ∉ Set.range D.target.pts) (hu : u ≠ 0)
    (g : Plane →ₗ[ℝ] ℝ) (hg0 : g ≠ 0) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgu : g u = 0)
    {ε0 : ℝ} (hε0 : 0 < ε0) (hin : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∈ D.target.carrier)
    (iα iβ : Fin N) (hiα : (D.tile iα).localAngle P = α)
    (hiβ : (D.tile iβ).localAngle P = 2 * Real.pi / 3 - α)
    (hnα : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∉ (D.tile iα).carrier)
    (hnβ : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → P + ε • u ∉ (D.tile iβ).carrier) :
    ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = P ∧ (D.tile K).angleAt l = Real.pi / 3 ∧
      (SameRay ℝ u ((D.tile K).pts (l + 1) - P) ∨ SameRay ℝ u ((D.tile K).pts (l + 2) - P)) := by
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
  have hK0α : K0 ≠ iα := by rintro rfl; exact hnα ε hεpos hεle hyK0
  have hK0β : K0 ≠ iβ := by rintro rfl; exact hnβ ε hεpos hεle hyK0
  -- `K0` presents `π/3` at `P`
  have hvals := Erdos634.VertexFigureReal.localAngle_mem D.toDissection α (2 * Real.pi / 3 - α) (Real.pi / 3)
    hP hnv (fun i j => corner_mem D hS i j) K0
  have hfig := third_is_P D hirr hS hP hnv iα hiα iβ hiβ
  have hne0 := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile K0) hPK0
  have hθ : (D.tile K0).localAngle P = Real.pi / 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvals
    rcases hvals with h | h | h | h | h
    · exact absurd (unique_of_cnt D.toDissection hfig.1 h hiα) hK0α
    · exact absurd (unique_of_cnt D.toDissection hfig.2.1 h hiβ) hK0β
    · exact h
    · exact (none_of_cnt D.toDissection hfig.2.2.2 h).elim
    · exact absurd h hne0
  obtain ⟨l, hl⟩ := Erdos634.Geometry.vertex_of_localAngle_corner (D.tile K0) hθ (by linarith) (by linarith)
    (by linarith)
  have hangl : (D.tile K0).angleAt l = Real.pi / 3 := by
    have h1 : (D.tile K0).localAngle ((D.tile K0).pts l) = Real.pi / 3 := by rw [hl]; exact hθ
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
      = Real.pi / 3 := by
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
      exact cross_ne_of_angle he1 he2 hang (cross_zero_of_ker g hg0 h1 h2)

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.forward_tile
