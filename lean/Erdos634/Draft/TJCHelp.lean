-- T-junction point-level helpers. No sorry/native_decide.
-- Generic helpers: a linear functional constant/bounded on the endpoints of a segment, on a triangle, and
-- "no interior point of a set lying in {f ≤ c} lies on {f = c}".  Used by TJCHand.lean and TJCC1.lean.
import Erdos634.WallChain
import Erdos634.EdgeChain
import Erdos634.Draft.FluxBoundary
import Erdos634.CertGeom
import Erdos634.CertCoord
import Erdos634.CellCoord
import Erdos634.InteriorCoord
import Erdos634.AreaDet

namespace Erdos634.Draft.TJCHelp

open Erdos634.Geometry

theorem seg_eq {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {p q y : Plane} (hp : f p = c) (hq : f q = c)
    (hy : y ∈ segment ℝ p q) : f y = c := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [map_add, map_smul, map_smul, hp, hq, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]

theorem seg_le {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {p q y : Plane} (hp : f p ≤ c) (hq : f q ≤ c)
    (hy : y ∈ segment ℝ p q) : f y ≤ c := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h1 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hb]

/-- a linear functional bounded above at the three vertices is bounded on the carrier -/
theorem carrier_le (T : Tri) {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} (h : ∀ k, f (T.pts k) ≤ c) :
    ∀ x ∈ T.carrier, f x ≤ c :=
  Erdos634.CertGeom.le_of_forall_pts_le (t := T) f.toAffineMap (c := c) h

theorem carrier_ge (T : Tri) {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} (h : ∀ k, c ≤ f (T.pts k)) :
    ∀ x ∈ T.carrier, c ≤ f x := by
  intro x hx
  have := carrier_le T (f := -f) (c := -c) (fun k => by simpa using h k) x hx
  simpa using this

/-- an interior point of a set contained in `{f ≤ c}` is not on the line `{f = c}` -/
theorem not_interior_on_line {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} {A : Set Plane}
    (hA : ∀ y ∈ A, f y ≤ c) {y : Plane} (hy : y ∈ interior A) (hfy : f y = c) : False := by
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane c - f.toAffineMap with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : (AffineMap.const ℝ Plane c).linear - f.toAffineMap.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane c).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g y = 0 := by simp [hg, hfy]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
  obtain ⟨z, hz, hzneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hzA : z ∈ A := hball hz
  have : c < f z := by
    have hgz : g z = c - f z := rfl
    rw [hgz] at hzneg
    linarith
  exact absurd (hA z hzA) (not_le.mpr this)

theorem not_interior_on_line_ge {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} {A : Set Plane}
    (hA : ∀ y ∈ A, c ≤ f y) {y : Plane} (hy : y ∈ interior A) (hfy : f y = c) : False :=
  not_interior_on_line (f := -f) (neg_ne_zero.mpr hf) (c := -c) (A := A)
    (fun y hy => by simpa using hA y hy) hy (by simpa using hfy)



open Erdos634.CertCoord

theorem interior_of_pos (T : Tri) {x : Plane} (hpos : ∀ i, 0 < T.basis.coord i x) :
    x ∈ interior T.carrier := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  exact mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

theorem mkPt_sub (a b c d : ℝ) : mkPt a b - mkPt c d = mkPt (a - c) (b - d) := by
  ext i; fin_cases i <;> simp

theorem mkPt_smul (t a b : ℝ) : t • mkPt a b = mkPt (t * a) (t * b) := by
  ext i; fin_cases i <;> simp

theorem mkPt_add (a b c d : ℝ) : mkPt a b + mkPt c d = mkPt (a + c) (b + d) := by
  ext i; fin_cases i <;> simp

theorem mkPt_inj {a b c d : ℝ} (h : mkPt a b = mkPt c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun p : Plane => p 0) h
  have h1 := congrArg (fun p : Plane => p 1) h
  simpa using And.intro h0 h1

theorem mkPt_mem_segment (a b c d t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    mkPt ((1 - t) * a + t * c) ((1 - t) * b + t * d) ∈ segment ℝ (mkPt a b) (mkPt c d) := by
  refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
  rw [mkPt_smul, mkPt_smul, mkPt_add]

theorem mkPt_mem_openSegment (a b c d t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    mkPt ((1 - t) * a + t * c) ((1 - t) * b + t * d) ∈ openSegment ℝ (mkPt a b) (mkPt c d) := by
  refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
  rw [mkPt_smul, mkPt_smul, mkPt_add]

/-- coordinate linear functional `v ↦ a v₀ + b v₁` -/
noncomputable def lin (a b : ℝ) : Plane →ₗ[ℝ] ℝ where
  toFun v := a * v 0 + b * v 1
  map_add' := by intro v w; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c v; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem lin_mkPt (a b x y : ℝ) : lin a b (mkPt x y) = a * x + b * y := by
  simp [lin]

theorem lin_ne_zero {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : lin a b ≠ 0 := by
  intro hz
  rcases h with h | h
  · apply h
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g (mkPt 1 0)) hz
    simpa using this
  · apply h
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g (mkPt 0 1)) hz
    simpa using this

theorem det_mkTri (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (h : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h).det = det3 x₀ y₀ x₁ y₁ x₂ y₂ := by
  unfold Tri.det
  simp only [mkTri_pts, det3]
  simp [mkPt_sub]
  ring

theorem leftDir_mkTri_pos (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (h : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0)
    (hp : 0 < det3 x₀ y₀ x₁ y₁ x₂ y₂) (k : Fin 3) :
    (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h).leftDir k =
      (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h).pts (k + 1) - (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h).pts k := by
  unfold Tri.leftDir
  rw [det_mkTri, if_pos hp]

theorem norm_mkPt_x (c : ℝ) : ‖mkPt c 0‖ = |c| := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

theorem norm_mkPt_y (c : ℝ) : ‖mkPt 0 c‖ = |c| := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

/-- a vertex of a tile is never an `OnEdge` point of that tile -/
theorem vertex_not_onEdge {N : ℕ} (D : Dissection N) (i : Fin N) (k : Fin 3) :
    ¬ OnEdge D ((D.tile i).pts k) i := by
  rintro ⟨m, hm, ho⟩
  have hex : ∀ m k : Fin 3, ∃ j : Fin 3, j ≠ m ∧ j ≠ k := by decide
  obtain ⟨j, hjm, hjk⟩ := hex m k
  have := ho j hjm
  have h0 : (D.tile i).basis.coord j ((D.tile i).pts k) = 0 := (D.tile i).basis.coord_apply_ne hjk
  linarith

end Erdos634.Draft.TJCHelp
