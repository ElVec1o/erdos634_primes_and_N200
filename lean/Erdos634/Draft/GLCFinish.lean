import Mathlib.Tactic
import Erdos634.Draft.GLCForward

/-!
# The finishing step of G2: no `γ`-tile with a forward edge at `Q₁`, given an `a`-edge `[Q₁, Z]` on the far side

`no_gamma_forward`: on a `CongruentDissection` with `TwoAlphaData α a b c` (`α ∉ ℚπ`), let `Q₁` be a non-vertex frontier point of the target, `w ≠ 0` the forward direction of the side at `Q₁`
and `Z` a point with `∠(Z − Q₁, w) = 3α` (in G2 `Z − Q₁` makes the angle `β = π − 3α` with the backward ray, the tile `iT` across `[Q₁,Z]`).  If a tile `Kc ≠ iT` has the `a`-edge `[Q₁, Z]`,
then no tile `U` has a vertex `Q₁` of angle `γ = 2α` with an edge along the forward ray.
Proof: `Kc` presents `β` or `γ` at `Q₁` (ends of an `a`-edge); `β` is `iT`'s (`angles_differ_2alpha`), so `γ`; then `U = Kc`, whose two edges at `Q₁` are `[Q₁,Z]` and the other one, enclosing `γ = 2α`,
while the forward edge encloses `3α` with `[Q₁,Z]`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3F6

variable {N : ℕ}

theorem angleAt_eq_angle (U : Tri) (m : Fin 3) :
    U.angleAt m = InnerProductGeometry.angle (U.pts (m + 1) - U.pts m) (U.pts (m + 2) - U.pts m) := by
  unfold Tri.angleAt cornerAngle EuclideanGeometry.angle; simp only [vsub_eq_sub]

theorem angle_sameRay_right {x w y : Plane} (hw : w ≠ 0) (hy : y ≠ 0) (h : SameRay ℝ w y) :
    InnerProductGeometry.angle x y = InnerProductGeometry.angle x w := by
  obtain ⟨t, ht, rfl⟩ := rayparam hw hy h
  exact InnerProductGeometry.angle_smul_right_of_pos x w ht

theorem no_gamma_forward (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    {Q1 Z w : Plane} (hQ1fr : Q1 ∈ frontier D.target.carrier) (hQ1nv : Q1 ∉ Set.range D.target.pts)
    (hw : w ≠ 0) (hangZ : InnerProductGeometry.angle (Z - Q1) w = 3 * α)
    (iT : Fin N) (hiT : (D.tile iT).localAngle Q1 = Real.pi - 3 * α)
    (Kc : Fin N) (k : Fin 3)
    (hKc : ((D.tile Kc).pts k = Q1 ∧ (D.tile Kc).pts (k + 1) = Z) ∨
      ((D.tile Kc).pts k = Z ∧ (D.tile Kc).pts (k + 1) = Q1))
    (hKa : dist Q1 Z = a) (hne : Kc ≠ iT)
    (U : Fin N) (l : Fin 3) (hU : (D.tile U).pts l = Q1) (hUang : (D.tile U).angleAt l = 2 * α)
    (hUray : SameRay ℝ w ((D.tile U).pts (l + 1) - Q1) ∨ SameRay ℝ w ((D.tile U).pts (l + 2) - Q1)) :
    False := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D hS
  have hinj : ∀ (V : Fin N) (m n : Fin 3), m ≠ n → (D.tile V).pts m ≠ (D.tile V).pts n :=
    fun V m n h hh => h ((D.tile V).indep.injective hh)
  have n01 : ∀ x : Fin 3, x ≠ x + 1 := by decide
  have n02 : ∀ x : Fin 3, x ≠ x + 2 := by decide
  have e11 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e21 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e22 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e12 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  -- the angles of `Kc` at the ends of its `a`-edge
  have hKd : dist ((D.tile Kc).pts k) ((D.tile Kc).pts (k + 1)) = a := by
    rcases hKc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hKa
    · rw [e1, e2, dist_comm]; exact hKa
  have hth := Erdos634.GLC.third_vertex_a (tile_twoalpha D hS Kc) hab hac k hKd
  -- index `m` of `Q₁` in `Kc`, the other endpoint `Z`, and the angle there
  obtain ⟨m, hm, hmZ, hmang⟩ : ∃ m : Fin 3, (D.tile Kc).pts m = Q1 ∧
      ((D.tile Kc).pts (m + 1) = Z ∨ (D.tile Kc).pts (m + 2) = Z) ∧
      ((D.tile Kc).angleAt m = Real.pi - 3 * α ∨ (D.tile Kc).angleAt m = 2 * α) := by
    rcases hKc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨k, e1, Or.inl e2, ?_⟩
      rcases hth with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · refine ⟨k + 1, e2, Or.inr (by rw [e12]; exact e1), ?_⟩
      rcases hth with ⟨-, h1, -, -⟩ | ⟨-, h1, -, -⟩
      · exact Or.inr h1
      · exact Or.inl h1
  have hKloc : (D.tile Kc).localAngle Q1 = (D.tile Kc).angleAt m := by
    rw [← hm]; exact Tri.localAngle_vertex _ _
  have hUloc : (D.tile U).localAngle Q1 = 2 * α := by
    rw [← hU, Tri.localAngle_vertex]; exact hUang
  -- `Kc` presents `γ` at `Q₁`
  have hKγ : (D.tile Kc).angleAt m = 2 * α := by
    rcases hmang with h | h
    · exfalso
      exact angles_differ_2alpha D hα hS hQ1fr hQ1nv hne (Or.inl (hKloc.trans h)) (by rw [hKloc, h, hiT])
    · exact h
  -- hence `U = Kc`
  have hUK : U = Kc := by
    by_contra hUK
    exact angles_differ_2alpha D hα hS hQ1fr hQ1nv (Ne.symm hUK) (Or.inr (hKloc.trans hKγ))
      (by rw [hKloc, hKγ, hUloc])
  subst hUK
  have hlm : l = m := (D.tile U).indep.injective (hU.trans hm.symm)
  subst hlm
  -- the two edges of `U` at `Q₁`
  have hang := angleAt_eq_angle (D.tile U) l
  rw [hU] at hang
  have hx1 : (D.tile U).pts (l + 1) - Q1 ≠ 0 := by
    rw [sub_ne_zero, ← hU]; exact (hinj U _ _ (n01 l)).symm
  have hx2 : (D.tile U).pts (l + 2) - Q1 ≠ 0 := by
    rw [sub_ne_zero, ← hU]; exact (hinj U _ _ (n02 l)).symm
  have hsplit : ∀ x y : Plane, x ≠ 0 → y ≠ 0 → x = Z - Q1 → SameRay ℝ w y →
      (InnerProductGeometry.angle x y = 2 * α) → False := by
    intro x y hx hy hxZ hr hxy
    rw [angle_sameRay_right hw hy hr, hxZ, hangZ] at hxy
    linarith
  have hpos : 0 < α := hα0
  rcases hmZ with hZ1 | hZ2
  · -- `Z = pts (l+1)`, forward edge along `pts (l+2)` or `pts (l+1)`
    rcases hUray with hr | hr
    · -- forward edge is the `Z`-edge: `SameRay w (Z - Q₁)`, angle `0 ≠ 3α`
      have h0 := angle_sameRay_right (x := (D.tile U).pts (l + 1) - Q1) hw hx1 hr
      rw [InnerProductGeometry.angle_self hx1] at h0
      rw [← hZ1] at hangZ
      linarith
    · exact hsplit _ _ hx1 hx2 (by rw [hZ1]) hr (by rw [← hang]; exact hUang)
  · rcases hUray with hr | hr
    · refine hsplit _ _ hx2 hx1 (by rw [hZ2]) hr ?_
      rw [InnerProductGeometry.angle_comm, ← hang]; exact hUang
    · have h0 := angle_sameRay_right (x := (D.tile U).pts (l + 2) - Q1) hw hx2 hr
      rw [InnerProductGeometry.angle_self hx2] at h0
      rw [← hZ2] at hangZ
      linarith

end Erdos634.GLC

#print axioms Erdos634.GLC.no_gamma_forward
