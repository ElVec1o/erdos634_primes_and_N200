import Erdos634.ReflS.SoundC

/-! ReflS/SoundCR.lean -- `ConjHyp` when the conjugation flips `√Dn` (radicand `K = Dn`, e.g. `K = Dn = 3`).

The coordinatewise `ψ`-image of a dissection of the target `(X, Y√Dn)` is then a dissection of the target reflected in
the x-axis; composing with the reflection `reflX` gives a dissection of the same target whose tiles are the conjugate
checker triangles `cjTri t` (conjugation of the coefficients in `ℤ[√K]`, the factor `√Dn` kept).  Text of
`SoundC.conj_carr` / `conjHyp_of_field` with one sign changed. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness Erdos634.SixPlacements
open Erdos634.Geometry (Plane cross)

namespace ReflS

/-- the reflection `(x, y) ↦ (x, −y)` -/
noncomputable def reflX : Plane ≃ᵢ Plane where
  toFun x := WithLp.toLp 2 ![x 0, -x 1]
  invFun x := WithLp.toLp 2 ![x 0, -x 1]
  left_inv x := by
    ext i; fin_cases i
    · rfl
    · show - - x 1 = x 1
      ring
  right_inv x := by
    ext i; fin_cases i
    · rfl
    · show - - x 1 = x 1
      ring
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    have h1 := Erdos634.H1hCT.dist_sq_plane (WithLp.toLp 2 ![x 0, -x 1]) (WithLp.toLp 2 ![y 0, -y 1])
    have h2 := Erdos634.H1hCT.dist_sq_plane x y
    have h3 : dist (WithLp.toLp 2 ![x 0, -x 1] : Plane) (WithLp.toLp 2 ![y 0, -y 1]) ^ 2 = dist x y ^ 2 := by
      rw [h1, h2]
      show (x 0 - y 0) ^ 2 + (-x 1 - -y 1) ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2
      ring
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h3

theorem reflX_apply0 (x : Plane) : reflX x 0 = x 0 := rfl
theorem reflX_apply1 (x : Plane) : reflX x 1 = -x 1 := rfl

/-- `psi_re` when `ψ √Dn = −√Dn`, for the reflected image -/
theorem psi_re_neg (F : Subfield ℝ) (ψ : F →+* ℝ) (hK : Real.sqrt ((K : ℤ) : ℝ) ∈ F)
    (hψK : ψ ⟨Real.sqrt ((K : ℤ) : ℝ), hK⟩ = -Real.sqrt ((K : ℤ) : ℝ))
    (Dn : ℝ) (hs : sr Dn ∈ F) (hψs : ψ ⟨sr Dn, hs⟩ = -sr Dn)
    (p : Pt) (P Q : Plane) (hP : P = p.re Dn) (h0 : P 0 ∈ F) (h1 : P 1 ∈ F)
    (hQ0 : Q 0 = ψ ⟨P 0, h0⟩) (hQ1 : Q 1 = -ψ ⟨P 1, h1⟩) : Q = (cjPt p).re Dn := by
  subst hP
  have e0 : (p.re Dn) 0 = p.X := rp_zero _ _ _
  have e1 : (p.re Dn) 1 = p.Y * sr Dn := rp_one _ _ _
  refine Erdos634.PlacementCompleteness.plane_ext ?_ ?_
  · rw [hQ0, psi_congr F ψ h0 (X_mem F hK p) e0, psi_X F ψ hK hψK]
    exact (rp_zero _ _ _).symm
  · have hm : p.Y * sr Dn ∈ F := F.mul_mem (Y_mem F hK p) hs
    have e : (⟨p.Y * sr Dn, hm⟩ : F) = ⟨p.Y, Y_mem F hK p⟩ * ⟨sr Dn, hs⟩ := Subtype.ext rfl
    rw [hQ1, psi_congr F ψ h1 hm e1, e, map_mul, psi_Y F ψ hK hψK, hψs]
    show _ = rp Dn (cjPt p).X (cjPt p).Y 1
    rw [rp_one]
    ring

/-- `conj_carr` when `ψ √Dn = −√Dn`: the corners of `T'` are the coordinatewise `ψ`-images of those of `T`, reflected
in the x-axis. -/
theorem conj_carr_neg (F : Subfield ℝ) (ψ : F →+* ℝ) (hK : Real.sqrt ((K : ℤ) : ℝ) ∈ F)
    (hψK : ψ ⟨Real.sqrt ((K : ℤ) : ℝ), hK⟩ = -Real.sqrt ((K : ℤ) : ℝ))
    (Dn : ℝ) (hD : 0 < Dn) (hs : sr Dn ∈ F) (hψs : ψ ⟨sr Dn, hs⟩ = -sr Dn)
    (T T' : Erdos634.Geometry.Tri) (hT : ∀ k v, T.pts k v ∈ F)
    (hT'0 : ∀ k, T'.pts k 0 = ψ ⟨T.pts k 0, hT k 0⟩) (hT'1 : ∀ k, T'.pts k 1 = -ψ ⟨T.pts k 1, hT k 1⟩)
    (t : Tri) (ht : t.ok = true) (hct : (cjTri t).ok = true) (hc : T.carrier = t.carr Dn) :
    T'.carrier = (cjTri t).carr Dn := by
  obtain ⟨k0, k1, k2, h01, h02, h12, h0, h1, h2⟩ := verts_of_carrier Dn hD T t ht hc
  have c0 : T'.pts k0 = (cjPt t.a).re Dn :=
    psi_re_neg F ψ hK hψK Dn hs hψs t.a _ _ h0 (hT k0 0) (hT k0 1) (hT'0 k0) (hT'1 k0)
  have c1 : T'.pts k1 = (cjPt t.b).re Dn :=
    psi_re_neg F ψ hK hψK Dn hs hψs t.b _ _ h1 (hT k1 0) (hT k1 1) (hT'0 k1) (hT'1 k1)
  have c2 : T'.pts k2 = (cjPt t.c).re Dn :=
    psi_re_neg F ψ hK hψK Dn hs hψs t.c _ _ h2 (hT k2 0) (hT k2 1) (hT'0 k2) (hT'1 k2)
  unfold cjTri at hct ⊢
  split_ifs at hct ⊢ with hdet
  · obtain ⟨hp', hcar'⟩ := Tri.ok_sem Dn hD _ hct
    rw [hcar']
    exact carrier_eq_rtri_of_pts hD T' h01 h02 h12 c0 c1 c2 hp'
  · obtain ⟨hp', hcar'⟩ := Tri.ok_sem Dn hD _ hct
    rw [hcar']
    exact carrier_eq_rtri_of_pts hD T' h02 h01 (Ne.symm h12) c0 c2 c1 hp'


open Erdos634.Geometry in
/-- **`ConjHyp` from a field with a conjugation that flips `√Dn`** (the case `K = Dn`): the coordinatewise image is a
dissection of the reflected target, and `reflX` brings it back. -/
theorem conjHyp_of_field_refl (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (M : Erdos634.Geometry.Tri) (htok : I.tgt.ok = true)
    (hrat : I.tgtRat = true) (ha0 : I.tgt.a.re Dn = 0) (hb1 : (I.tgt.b.re Dn) 1 = 0)
    (F : Subfield ℝ) (ψ : F →+* ℝ) (hK : Real.sqrt ((K : ℤ) : ℝ) ∈ F)
    (hψK : ψ ⟨Real.sqrt ((K : ℤ) : ℝ), hK⟩ = -Real.sqrt ((K : ℤ) : ℝ))
    (hs : sr Dn ∈ F) (hψs : ψ ⟨sr Dn, hs⟩ = -sr Dn)
    (hMd : ∀ j l, dist (M.pts j) (M.pts l) ∈ F) (hMdet : |M.det| ∈ F) : ConjHyp Dn I M := by
  intro N D htg hm
  obtain ⟨k0, k1, -, h01, -, -, h0, h1, -⟩ := verts_of_carrier Dn hD D.target I.tgt htok htg
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm k0 k1 h01
  set D1 := D.relabelTarget' σ with hD1
  have t0 : D1.target.pts 0 = 0 := by
    show D.target.pts (σ 0) = 0
    rw [hσ0, h0]; exact ha0
  have t1 : D1.target.pts 1 1 = 0 := by
    show (D.target.pts (σ 1)) 1 = 0
    rw [hσ1, h1]; exact hb1
  have hd : ∀ j l, dist (D1.model.pts j) (D1.model.pts l) ∈ F := by
    intro j l
    obtain ⟨τ, hτ⟩ := hm.dist_eq
    show dist (D.model.pts j) (D.model.pts l) ∈ F
    rw [hτ]; exact hMd _ _
  have hdet : |D1.model.det| ∈ F := by
    show |D.model.det| ∈ F
    rw [Erdos634.KConj.abs_det_congr hm]; exact hMdet
  obtain ⟨hKt, hKT⟩ := Erdos634.H1gPos.L1 D1 F hd hdet t0 t1
  obtain ⟨D0, e1', e2', -⟩ := Erdos634.H1hCT.conj_congruentDissection_subfield D1 F ψ hKt hKT
  set D' := Erdos634.NormalPosition.normalizeC D0 reflX 1 with hD'
  have t'0 : ∀ i k, (D'.tile i).pts k 0 = ψ ⟨(D1.tile i).pts k 0, hKt i k 0⟩ := fun i k => e1' i k 0
  have t'1 : ∀ i k, (D'.tile i).pts k 1 = -ψ ⟨(D1.tile i).pts k 1, hKt i k 1⟩ := fun i k => by
    show -((D0.tile i).pts k 1) = _
    rw [e1' i k 1]
  have g'0 : ∀ k, D'.target.pts k 0 = ψ ⟨D1.target.pts k 0, hKT k 0⟩ := fun k => e2' k 0
  have g'1 : ∀ k, D'.target.pts k 1 = -ψ ⟨D1.target.pts k 1, hKT k 1⟩ := fun k => by
    show -(D0.target.pts k 1) = _
    rw [e2' k 1]
  have hD1c : D1.target.carrier = I.tgt.carr Dn := by
    show (Erdos634.NormalPosition.relabelTri D.target σ).carrier = _
    rw [Erdos634.NormalPosition.relabelTri_carrier, htg]
  refine ⟨D', ?_, ?_⟩
  · -- the target is fixed by the conjugation
    have hfix : ∀ k, D'.target.pts k = D1.target.pts k := by
      intro k
      simp only [Inst.tgtRat, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hrat
      obtain ⟨ra, rb, rc⟩ := hrat
      rcases pts_of_carrier Dn D1.target I.tgt hD1c k with h | h | h
      · rw [psi_re_neg F ψ hK hψK Dn hs hψs I.tgt.a _ _ h (hKT k 0) (hKT k 1) (g'0 k) (g'1 k), h]
        exact cjPt_re_of_rat Dn _ ra
      · rw [psi_re_neg F ψ hK hψK Dn hs hψs I.tgt.b _ _ h (hKT k 0) (hKT k 1) (g'0 k) (g'1 k), h]
        exact cjPt_re_of_rat Dn _ rb
      · rw [psi_re_neg F ψ hK hψK Dn hs hψs I.tgt.c _ _ h (hKT k 0) (hKT k 1) (g'0 k) (g'1 k), h]
        exact cjPt_re_of_rat Dn _ rc
    have hpts : D'.target.pts = D1.target.pts := funext hfix
    rw [← hD1c]
    show convexHull ℝ (Set.range D'.target.pts) = convexHull ℝ (Set.range D1.target.pts)
    rw [hpts]
  · intro i t ht hct hc
    exact conj_carr_neg F ψ hK hψK Dn hD hs hψs (D1.tile i) (D'.tile i) (hKt i) (t'0 i) (t'1 i) t ht hct hc

end ReflS

#print axioms ReflS.conjHyp_of_field_refl
