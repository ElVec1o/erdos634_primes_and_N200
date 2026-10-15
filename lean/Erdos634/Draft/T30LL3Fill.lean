import Mathlib.Tactic
import Erdos634.Draft.T30LC2Doubled

/-!
# (L3), second half: the fill after `β` (tile `T₃`) and `α` (first far-chain tile) are placed at `P₂`, conditional on the configuration

`l3_fill`: at a non-vertex frontier point `V` (`= P₂`) of the target, with side direction `u`, suppose

* `T₃ = tile iβ` has vertices `(V, V−u, V+d)` in this cyclic order from `V` (`V−u = P` the previous side vertex, `V+d = Z` the chord midpoint), presenting `β = 2π/3 − α` at `V`;
* `Kc = tile iα` has vertices `(V, V+d, X)`, i.e. an edge `[V, V+d]` along the chord, and presents `α` at `V`.

Then there is a tile `K` with a `π/3` vertex at `V` and an edge along the side, forward from `V` (`u`).  The geometric ingredient is `not_in_cone`: a vector at
(unoriented) angle `> θ` from `d` is not in the cone spanned by `d` and `e` when `angle d e = θ ∈ (0,π)` (via `Pi3Cone.cone_oangle`), applied to `Kc` (the angle from `d`
to `u` is `π − β = π/3 + α > α`); and `u, d` independent for `T₃`.

Hypotheses not derived in this file: (i) `T₃`'s vertex triple `(V, V−u, V+d)` (the SAS step `T₃ = T + a e₁` from `c2_doubled_corner`'s `SideTile`);
(ii) the existence of `Kc` with an edge `[V, V+d]` on the chord, the first tile of the far chain, which needs the endpoint of the far chain at `P₂`
(`LineParam.lineChain_covers_Icc` + `edgeParam_spec`) and the chord clamps/`hwall` for the doubled chord `P₂Q₁` (a union of two tile edges).
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.SectorFill Erdos634.Pi3Cone

theorem exists_pos_orientation' {u1 u2 : Plane} (hu1 : u1 ≠ 0) (hu2 : u2 ≠ 0) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi)
    (h : InnerProductGeometry.angle u1 u2 = θ) :
    ∃ o : Orientation ℝ Plane (Fin 2), (o.oangle u1 u2).sign = 1 := by
  let o0 : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hne : (o0.oangle u1 u2).sign ≠ 0 := by
    intro h0'
    rcases o0.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h0' with h1 | h1 | h1 | h1
    · exact hu1 h1
    · exact hu2 h1
    · rw [h] at h1; linarith
    · rw [h] at h1; linarith
  have hcases : ∀ s : SignType, s ≠ 0 → s = -1 ∨ s = 1 := by decide
  rcases hcases _ hne with hm | hp
  · refine ⟨-o0, ?_⟩
    rw [Orientation.oangle_neg_orientation_eq_neg, Real.Angle.sign_neg, hm]; decide
  · exact ⟨o0, hp⟩

/-- A vector at angle `> θ` from `d` is not in the cone spanned by `d` and `e` when `angle d e = θ ∈ (0,π)`. -/
theorem not_in_cone {d e u : Plane} (hd : d ≠ 0) (he : e ≠ 0) (hu : u ≠ 0) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi)
    (hde : InnerProductGeometry.angle d e = θ) (hdu : θ < InnerProductGeometry.angle d u)
    {s t ε : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hε : 0 < ε) : ε • u ≠ s • d + t • e := by
  intro heq
  obtain ⟨o, ho⟩ := exists_pos_orientation' hd he h0 hπ hde
  have hx : s • d + t • e ≠ 0 := by rw [← heq]; exact smul_ne_zero hε.ne' hu
  have hc := cone_oangle o ho hs ht hx
  rw [← heq] at hc
  have hθ : (o.oangle d e).toReal = θ := by
    rw [o.oangle_eq_angle_of_sign_eq_one ho, hde, Real.Angle.toReal_coe_eq_self_iff]
    constructor <;> linarith
  have hang : InnerProductGeometry.angle d (ε • u) = |(o.oangle d (ε • u)).toReal| :=
    o.angle_eq_abs_oangle_toReal hd (smul_ne_zero hε.ne' hu)
  rw [abs_of_nonneg hc.1] at hang
  have h2 : (o.oangle d (ε • u)).toReal ≤ θ := by rw [← hθ]; exact hc.2
  have h3 : InnerProductGeometry.angle d (ε • u) = InnerProductGeometry.angle d u :=
    InnerProductGeometry.angle_smul_right_of_pos _ _ hε
  rw [h3] at hang
  linarith

/-- Vectors at an angle `θ ∈ (0,π)` are not parallel. -/
theorem cross_ne_of_angle' {x y : Plane} (hx : x ≠ 0) (hy : y ≠ 0) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi)
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
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have h4 : (Real.cos θ * (‖x‖ * ‖y‖)) ^ 2 = Real.cos θ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2) := by ring
  have hpos : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 := by positivity
  have hcs : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by rw [Real.cos_sq']
  have : Real.sin θ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2) = 0 := by nlinarith
  have hs2 : 0 < Real.sin θ ^ 2 := by positivity
  nlinarith

theorem l3_fill {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) {V u d X : Plane} (hu : u ≠ 0)
    (hVfr : V ∈ frontier D.target.carrier) (hVnv : V ∉ Set.range D.target.pts)
    (g : Plane →ₗ[ℝ] ℝ) (hg0 : g ≠ 0) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgV : g V = cg) (hgu : g u = 0)
    {ε0 : ℝ} (hε0 : 0 < ε0) (hin : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → V + ε • u ∈ D.target.carrier)
    (iβ : Fin N) (m : Fin 3) (hm0 : (D.tile iβ).pts m = V)
    (hm : ((D.tile iβ).pts (m + 1) = V - u ∧ (D.tile iβ).pts (m + 2) = V + d) ∨
          ((D.tile iβ).pts (m + 1) = V + d ∧ (D.tile iβ).pts (m + 2) = V - u))
    (iα : Fin N) (n : Fin 3) (hn0 : (D.tile iα).pts n = V)
    (hn : ((D.tile iα).pts (n + 1) = V + d ∧ (D.tile iα).pts (n + 2) = X) ∨
          ((D.tile iα).pts (n + 1) = X ∧ (D.tile iα).pts (n + 2) = V + d))
    (hiα : (D.tile iα).localAngle V = α) (hiβ : (D.tile iβ).localAngle V = 2 * Real.pi / 3 - α) :
    ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = V ∧ (D.tile K).angleAt l = Real.pi / 3 ∧
      (SameRay ℝ u ((D.tile K).pts (l + 1) - V) ∨ SameRay ℝ u ((D.tile K).pts (l + 2) - V)) := by
  have hpi := Real.pi_pos
  -- the two angles at `V` as vector angles
  have hcA : InnerProductGeometry.angle d (X - V) = α := by
    have h1 : (D.tile iα).localAngle ((D.tile iα).pts n) = α := by rw [hn0]; exact hiα
    rw [Tri.localAngle_vertex] at h1
    unfold cornerAngle EuclideanGeometry.angle at h1
    rcases hn with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · simp only [vsub_eq_sub, hn0, h1', h2', add_sub_cancel_left] at h1
      exact h1
    · simp only [vsub_eq_sub, hn0, h1', h2', add_sub_cancel_left] at h1
      rw [InnerProductGeometry.angle_comm]; exact h1
  have hcB : InnerProductGeometry.angle (-u) d = 2 * Real.pi / 3 - α := by
    have h1 : (D.tile iβ).localAngle ((D.tile iβ).pts m) = 2 * Real.pi / 3 - α := by rw [hm0]; exact hiβ
    rw [Tri.localAngle_vertex] at h1
    unfold cornerAngle EuclideanGeometry.angle at h1
    rcases hm with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · simp only [vsub_eq_sub, hm0, h1', h2', add_sub_cancel_left, sub_sub_cancel_left] at h1
      exact h1
    · simp only [vsub_eq_sub, hm0, h1', h2', add_sub_cancel_left, sub_sub_cancel_left] at h1
      rw [InnerProductGeometry.angle_comm]; exact h1
  have hα0 : 0 < α := lt_of_le_of_ne (by rw [← hcA]; exact InnerProductGeometry.angle_nonneg _ _) (d_a0 hirr).symm
  have hαπ : α < Real.pi := lt_of_le_of_ne (by rw [← hcA]; exact InnerProductGeometry.angle_le_pi _ _) (d_ap hirr)
  have hβ0 : 0 < 2 * Real.pi / 3 - α :=
    lt_of_le_of_ne (by rw [← hcB]; exact InnerProductGeometry.angle_nonneg _ _) (d_b0 hirr).symm
  have hβπ : 2 * Real.pi / 3 - α < Real.pi := by linarith
  -- nonzero vectors
  have hd : d ≠ 0 := by
    intro h0; rw [h0] at hcB
    have := InnerProductGeometry.angle_zero_right (-u)
    rw [this] at hcB
    exact hirr ⟨1 / 6, by push_cast; linarith⟩
  have he : X - V ≠ 0 := by
    intro h0; rw [h0] at hcA
    have := InnerProductGeometry.angle_zero_right d
    rw [this] at hcA
    exact hirr ⟨1 / 2, by push_cast; linarith⟩
  -- angle from `d` to `u` is `π − β`
  have hdu : InnerProductGeometry.angle d u = Real.pi - (2 * Real.pi / 3 - α) := by
    have h1 : InnerProductGeometry.angle d (-u) = 2 * Real.pi / 3 - α := by
      rw [InnerProductGeometry.angle_comm]; exact hcB
    have h2 := InnerProductGeometry.angle_neg_right d u
    rw [h1] at h2; linarith
  -- `Kc` does not contain the forward points
  have hnα : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → V + ε • u ∉ (D.tile iα).carrier := by
    intro ε hε _ hmem
    obtain ⟨s, t, hs, ht, hst⟩ := hull_cone (D.tile iα) n _ hmem
    rw [hn0] at hst
    simp only [add_sub_cancel_left] at hst
    rcases hn with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · rw [h1', h2'] at hst
      simp only [add_sub_cancel_left] at hst
      exact not_in_cone hd he hu hα0 hαπ hcA (by rw [hdu]; linarith) hs ht hε hst
    · rw [h1', h2'] at hst
      simp only [add_sub_cancel_left] at hst
      rw [add_comm] at hst
      exact not_in_cone hd he hu hα0 hαπ hcA (by rw [hdu]; linarith) ht hs hε hst
  -- `T₃` does not contain them either
  have hcr := cross_ne_of_angle' (neg_ne_zero.mpr hu) hd hβ0 hβπ hcB
  simp only [PiLp.neg_apply] at hcr
  have hnβ : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → V + ε • u ∉ (D.tile iβ).carrier := by
    intro ε hε _ hmem
    obtain ⟨s, t, hs, ht, hst⟩ := hull_cone (D.tile iβ) m _ hmem
    rw [hm0] at hst
    simp only [add_sub_cancel_left] at hst
    rcases hm with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · rw [h1', h2'] at hst
      simp only [add_sub_cancel_left, sub_sub_cancel_left] at hst
      have h0 := congrArg (fun w : Plane => w 0) hst
      have h1 := congrArg (fun w : Plane => w 1) hst
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.neg_apply, smul_eq_mul] at h0 h1
      have : (ε + s) * (u 0 * d 1 - u 1 * d 0) = 0 := by
        linear_combination (d 1) * h0 - (d 0) * h1
      have hne : ε + s ≠ 0 := by positivity
      have := (mul_eq_zero.mp this).resolve_left hne
      apply hcr; linarith
    · rw [h1', h2'] at hst
      simp only [add_sub_cancel_left, sub_sub_cancel_left] at hst
      have h0 := congrArg (fun w : Plane => w 0) hst
      have h1 := congrArg (fun w : Plane => w 1) hst
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.neg_apply, smul_eq_mul] at h0 h1
      have : (ε + t) * (u 0 * d 1 - u 1 * d 0) = 0 := by
        linear_combination (d 1) * h0 - (d 0) * h1
      have hne : ε + t ≠ 0 := by positivity
      have := (mul_eq_zero.mp this).resolve_left hne
      apply hcr; linarith
  exact forward_tile D hirr hS hVfr hVnv hu g hg0 cg hg hgV hgu hε0 hin iα iβ hiα hiβ hnα hnβ

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.not_in_cone
#print axioms Erdos634.C2Forward.l3_fill
