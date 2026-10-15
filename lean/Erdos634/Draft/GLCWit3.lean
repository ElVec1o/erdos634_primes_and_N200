import Mathlib.Tactic
import Erdos634.Draft.GLCG2
import Erdos634.Draft.GLCWit

/-!
# Witness for `corner_G2` on the real 1125-tiling (`k = 2`, tile `(4,5,6)·16`), including the `(c,c)` antecedent

The real certified tiling `G3GControl.D` (target `(0,0),(3600,0),(1800,600)` on the lattice `(X, v√7)`, tile `(0,0),(96,0),(60,20)`): the corner tile at the target corner `0` is leaf `841 = ((0,0),(96,0),(60,20))`
(its `c`-edge `[(0,0),(96,0)]` lies on the base, `b = 80`), the second tile on the base is leaf `846 = ((96,0),(192,0),(156,20))` with `α` at `(96,0)` and a side edge of length `96 = c` (the `(c,c)` antecedent, discharged
here from the certificate), `Q₁ = (192,0)`.  `witness_corner_G2`: every antecedent of `corner_G2` holds, and its conclusion (no `γ`-tile at `Q₁` with a forward edge) is obtained from `corner_G2` itself.
`ctl_gamma_forward_exists`: at the base point `(1840,0)` leaf `208 = ((1840,0),(1920,0),(1848,24))` DOES have `γ` with a forward edge, so the conclusion is not vacuous (it is false at points not forced to be `Q₁`).
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Draft.G3GControl Erdos634.Draft.G3CAng Erdos634.Draft.G3GCert Erdos634.EdgeWordConversion
open Erdos634.Draft.G3GTiling1125 (cert cert_len cert_ok)

theorem tile_pts_eq (i : Fin cert.leaves.length) (k : Fin 3) :
    (D.tile i).pts k = toPt (vtx cert.leaves[i.1] k) := by
  show (triOf cert.leaves[i.1] (pos_of_mem cert_ok (List.getElem_mem i.isLt))).pts k = _
  rw [triOf_pts]

theorem target_pts_eq (k : Fin 3) : D.target.pts k = toPt (vtx cert.target k) := by
  rw [show D.target = _ from cd_target cert cert_ok, triOf_pts]

theorem leaf841 : cert.leaves[841]'(by rw [cert_len]; norm_num) = ((0, 0), (96, 0), (60, 20)) := by
  decide +kernel

theorem leaf846 : cert.leaves[846]'(by rw [cert_len]; norm_num) = ((96, 0), (192, 0), (156, 20)) := by
  decide +kernel

theorem leaf208 : cert.leaves[208]'(by rw [cert_len]; norm_num) = ((1840, 0), (1920, 0), (1848, 24)) := by
  decide +kernel

def i0 : Fin cert.leaves.length := ⟨841, by rw [cert_len]; norm_num⟩
def iK : Fin cert.leaves.length := ⟨846, by rw [cert_len]; norm_num⟩
def iG : Fin cert.leaves.length := ⟨208, by rw [cert_len]; norm_num⟩

theorem toPt_sub (p q p' q' : LP) (h1 : p.1 - q.1 = p'.1 - q'.1) (h2 : p.2 - q.2 = p'.2 - q'.2) :
    toPt p - toPt q = toPt p' - toPt q' := by
  have e1 : (p.1 : ℝ) - q.1 = p'.1 - q'.1 := by exact_mod_cast h1
  have e2 : (p.2 : ℝ) - q.2 = p'.2 - q'.2 := by exact_mod_cast h2
  ext i
  fin_cases i
  · simp [toPt, rx, Erdos634.CertCoord.mkPt_zero]; linarith
  · simp [toPt, ry, Erdos634.CertCoord.mkPt_one]
    have : (p.2 : ℝ) * Real.sqrt 7 - q.2 * Real.sqrt 7 = (p'.2 * Real.sqrt 7 - q'.2 * Real.sqrt 7) := by
      rw [← sub_mul, ← sub_mul, e2]
    linarith


theorem tile_angle_alpha (i : Fin cert.leaves.length) (t : LT) (ht : cert.leaves[i.1] = t) (j : Fin 3)
    (h1 : d2 (vtx t (j + 1)) (vtx t (j + 2)) = 64 ^ 2)
    (h2 : (d2 (vtx t (j + 2)) (vtx t j) = 80 ^ 2 ∧
           d2 (vtx t j) (vtx t (j + 1)) = 96 ^ 2) ∨
          (d2 (vtx t (j + 2)) (vtx t j) = 96 ^ 2 ∧
           d2 (vtx t j) (vtx t (j + 1)) = 80 ^ 2)) :
    (D.tile i).angleAt j = α := by
  have hpts : ∀ k, (D.tile i).pts k = toPt (vtx t k) := by intro k; rw [tile_pts_eq, ht]
  have e1 : j + 1 + 1 = j + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) j
  have e2 : j + 1 + 2 = j := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) j
  have e3 : j + 2 + 1 = j := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) j
  have e4 : j + 2 + 2 = j + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) j
  have hopp : ∀ m, (D.tile i).oppLen m =
      dist (toPt (vtx t (m + 1))) (toPt (vtx t (m + 2))) := by
    intro m; unfold Tri.oppLen; rw [hpts, hpts]
  have o0 : (D.tile i).oppLen j = 64 := by
    rw [hopp]; have := Erdos634.Draft.G3GControl.dist_toPt_nat (vtx t (j + 1)) (vtx t (j + 2)) 64 (by simpa using h1)
    rw [this]; norm_num
  have hcosα : Real.cos ((D.model).angleAt 0) = 3 / 4 := cos_α
  rcases h2 with ⟨x1, x2⟩ | ⟨x1, x2⟩
  · have o1 : (D.tile i).oppLen (j + 1) = 80 := by
      rw [hopp, e1, e2]
      have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 80 (by simpa using x1)
      rw [this]; norm_num
    have o2 : (D.tile i).oppLen (j + 2) = 96 := by
      rw [hopp, e3, e4]
      have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 96 (by simpa using x2)
      rw [this]; norm_num
    have hc := cos_angleAt_opp (D.tile i) j (by rw [o1]; norm_num) (by rw [o2]; norm_num)
    rw [o0, o1, o2] at hc
    exact angle_eq_of_cos (T := D.tile i) (U := D.model) j 0 (by rw [hc, hcosα]; norm_num)
  · have o1 : (D.tile i).oppLen (j + 1) = 96 := by
      rw [hopp, e1, e2]
      have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 96 (by simpa using x1)
      rw [this]; norm_num
    have o2 : (D.tile i).oppLen (j + 2) = 80 := by
      rw [hopp, e3, e4]
      have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 80 (by simpa using x2)
      rw [this]; norm_num
    have hc := cos_angleAt_opp (D.tile i) j (by rw [o1]; norm_num) (by rw [o2]; norm_num)
    rw [o0, o1, o2] at hc
    exact angle_eq_of_cos (T := D.tile i) (U := D.model) j 0 (by rw [hc, hcosα]; norm_num)

theorem tile_angle_gamma (i : Fin cert.leaves.length) (t : LT) (ht : cert.leaves[i.1] = t) (j : Fin 3)
    (h1 : d2 (vtx t (j + 1)) (vtx t (j + 2)) = 96 ^ 2)
    (h2 : (d2 (vtx t (j + 2)) (vtx t j) = 64 ^ 2 ∧
           d2 (vtx t j) (vtx t (j + 1)) = 80 ^ 2) ∨
          (d2 (vtx t (j + 2)) (vtx t j) = 80 ^ 2 ∧
           d2 (vtx t j) (vtx t (j + 1)) = 64 ^ 2)) :
    (D.tile i).angleAt j = 2 * α := by
  have hpts : ∀ k, (D.tile i).pts k = toPt (vtx t k) := by intro k; rw [tile_pts_eq, ht]
  have e1 : j + 1 + 1 = j + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) j
  have e2 : j + 1 + 2 = j := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) j
  have e3 : j + 2 + 1 = j := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) j
  have e4 : j + 2 + 2 = j + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) j
  have hopp : ∀ m, (D.tile i).oppLen m =
      dist (toPt (vtx t (m + 1))) (toPt (vtx t (m + 2))) := by
    intro m; unfold Tri.oppLen; rw [hpts, hpts]
  have o0 : (D.tile i).oppLen j = 96 := by
    rw [hopp]; have := Erdos634.Draft.G3GControl.dist_toPt_nat (vtx t (j + 1)) (vtx t (j + 2)) 96 (by simpa using h1)
    rw [this]; norm_num
  have hcosγ : Real.cos ((D.model).angleAt 2) = 1 / 8 := cos_γ
  have key : (D.tile i).angleAt j = D.model.angleAt 2 := by
    rcases h2 with ⟨x1, x2⟩ | ⟨x1, x2⟩
    · have o1 : (D.tile i).oppLen (j + 1) = 64 := by
        rw [hopp, e1, e2]
        have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 64 (by simpa using x1)
        rw [this]; norm_num
      have o2 : (D.tile i).oppLen (j + 2) = 80 := by
        rw [hopp, e3, e4]
        have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 80 (by simpa using x2)
        rw [this]; norm_num
      have hc := cos_angleAt_opp (D.tile i) j (by rw [o1]; norm_num) (by rw [o2]; norm_num)
      rw [o0, o1, o2] at hc
      exact angle_eq_of_cos (T := D.tile i) (U := D.model) j 2 (by rw [hc, hcosγ]; norm_num)
    · have o1 : (D.tile i).oppLen (j + 1) = 80 := by
        rw [hopp, e1, e2]
        have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 80 (by simpa using x1)
        rw [this]; norm_num
      have o2 : (D.tile i).oppLen (j + 2) = 64 := by
        rw [hopp, e3, e4]
        have := Erdos634.Draft.G3GControl.dist_toPt_nat _ _ 64 (by simpa using x2)
        rw [this]; norm_num
      have hc := cos_angleAt_opp (D.tile i) j (by rw [o1]; norm_num) (by rw [o2]; norm_num)
      rw [o0, o1, o2] at hc
      exact angle_eq_of_cos (T := D.tile i) (U := D.model) j 2 (by rw [hc, hcosγ]; norm_num)
  rw [key, γ_eq]

theorem tile_pts_leaf (i : Fin cert.leaves.length) (t : LT) (ht : cert.leaves[i.1] = t) (k : Fin 3) :
    (D.tile i).pts k = toPt (vtx t k) := by rw [tile_pts_eq, ht]

theorem hP0 : (D.tile i0).pts 0 = toPt (0, 0) := tile_pts_leaf i0 _ leaf841 0
theorem hP1 : (D.tile i0).pts 1 = toPt (96, 0) := tile_pts_leaf i0 _ leaf841 1
theorem hP2 : (D.tile i0).pts 2 = toPt (60, 20) := tile_pts_leaf i0 _ leaf841 2
theorem hK0 : (D.tile iK).pts 0 = toPt (96, 0) := tile_pts_leaf iK _ leaf846 0
theorem hK1 : (D.tile iK).pts 1 = toPt (192, 0) := tile_pts_leaf iK _ leaf846 1
theorem hG0 : (D.tile iG).pts 0 = toPt (1840, 0) := tile_pts_leaf iG _ leaf208 0
theorem hG1 : (D.tile iG).pts 1 = toPt (1920, 0) := tile_pts_leaf iG _ leaf208 1
theorem hT0 : D.target.pts 0 = toPt (0, 0) := target_pts_eq 0

theorem hsides_1125 : ∀ i : Fin 3, sideLen D i = 64 ∨ sideLen D i = 80 ∨ sideLen D i = 96 :=
  sideLen_mem_2a D data

theorem hw1_1125 : ∀ x y z : ℕ, (x : ℝ) * 64 + y * 80 + z * 96 = 64 → x = 1 ∧ y = 0 ∧ z = 0 := by
  intro x y z h
  exact hword_a_full 2 le_rfl (s := 16) (by norm_num) x y z (by push_cast; linarith)

theorem hw2_1125 : ∀ x y z : ℕ, (x : ℝ) * 64 + y * 80 + z * 96 = 2 * 64 → x = 2 ∧ y = 0 ∧ z = 0 := by
  intro x y z h
  exact hword_2a_real 2 le_rfl (s := 16) (by norm_num) x y z (by push_cast; linarith)

theorem hwc_1125 : ∀ x y z : ℕ, (x : ℝ) * 64 + y * 80 + z * 96 = 96 → x = 0 ∧ y = 0 ∧ z = 1 := by
  intro x y z h
  exact hword_c_real 2 le_rfl (s := 16) (by norm_num) x y z (by push_cast; linarith)

theorem nonvertex_double (P : Plane) (s : ℝ) (hs : 0 < s) (hd : dist (D.target.pts 0) P = s)
    (h1 : 2 * s ≠ 3600) (h2 : 2 * s ≠ 2400) :
    ∀ v' : Fin 3, D.target.pts v' ≠ P + (P - D.target.pts 0) := by
  intro v' h
  have hn : ‖P - D.target.pts 0‖ = s := by rw [← dist_eq_norm, dist_comm]; exact hd
  have hdQ : dist (D.target.pts 0) (P + (P - D.target.pts 0)) = 2 * s := by
    rw [dist_eq_norm]
    have : D.target.pts 0 - (P + (P - D.target.pts 0)) = (-2 : ℝ) • (P - D.target.pts 0) := by module
    rw [this, norm_smul, hn]
    have : ‖(-2 : ℝ)‖ = 2 := by norm_num
    rw [this]
  have e1 : D.target.pts 1 = D.target.pts (0 + 1) := rfl
  have e2 : D.target.pts 2 = D.target.pts (0 + 2) := rfl
  fin_cases v'
  · simp only [Fin.zero_eta, Fin.isValue] at h
    rw [← h, dist_self] at hdQ; linarith
  · simp only [Fin.mk_one, Fin.isValue] at h
    rw [← h, e1, dist01] at hdQ; exact h1 hdQ.symm
  · simp only [Fin.reduceFinMk, Fin.isValue] at h
    rw [← h, e2, dist02] at hdQ; exact h2 hdQ.symm

theorem hdO1 : dist (D.target.pts 0) ((D.tile i0).pts 1) = 96 := by
  rw [hT0, hP1]
  have := Erdos634.Draft.G3GControl.dist_toPt_nat (0, 0) (96, 0) 96 (by decide)
  rw [this]; norm_num

theorem hdO2 : dist (D.target.pts 0) ((D.tile i0).pts 2) = 80 := by
  rw [hT0, hP2]
  have := Erdos634.Draft.G3GControl.dist_toPt_nat (0, 0) (60, 20) 80 (by decide)
  rw [this]; norm_num

theorem hdXY : dist ((D.tile iK).pts 0) ((D.tile iK).pts 1) = 96 := by
  rw [hK0, hK1]
  have := Erdos634.Draft.G3GControl.dist_toPt_nat (96, 0) (192, 0) 96 (by decide)
  rw [this]; norm_num

theorem hang0 : (D.tile i0).angleAt 0 = α :=
  tile_angle_alpha i0 _ leaf841 0 (by decide) (Or.inl ⟨by decide, by decide⟩)

theorem hangK : (D.tile iK).angleAt 0 = α :=
  tile_angle_alpha iK _ leaf846 0 (by decide) (Or.inl ⟨by decide, by decide⟩)

theorem hangG : (D.tile iG).angleAt 0 = 2 * α :=
  tile_angle_gamma iG _ leaf208 0 (by decide) (Or.inl ⟨by decide, by decide⟩)

theorem hKray : SameRay ℝ ((D.tile i0).pts 1 - D.target.pts 0) ((D.tile iK).pts (0 + 1) - (D.tile i0).pts 1) := by
  have e : (0 : Fin 3) + 1 = 1 := rfl
  rw [e, hK1, hP1, hT0]
  have : toPt (192, 0) - toPt (96, 0) = toPt (96, 0) - toPt (0, 0) :=
    toPt_sub _ _ _ _ (by norm_num) (by norm_num)
  rw [this]

/-- **WITNESS.**  On the real 1125-tiling every antecedent of `corner_G2` holds for the corner tile (leaf 841) and its second tile on the base
(leaf 846, `α` at `(96,0)`, a base edge of length `96 = c`: the `(c,c)` antecedent, read off the certificate), and `corner_G2` gives its conclusion. -/
theorem witness_corner_G2 : ∃ (i K : Fin cert.leaves.length) (j l m1 m2 : Fin 3),
    (D.tile i).pts j = D.target.pts 0 ∧ (D.tile i).angleAt j = α ∧
    ((m1 = j + 1 ∧ m2 = j + 2) ∨ (m1 = j + 2 ∧ m2 = j + 1)) ∧
    dist (D.target.pts 0) ((D.tile i).pts m1) = 96 ∧ dist (D.target.pts 0) ((D.tile i).pts m2) = 80 ∧
    (D.tile K).pts l = (D.tile i).pts m1 ∧ (D.tile K).angleAt l = α ∧
    ((SameRay ℝ ((D.tile i).pts m1 - D.target.pts 0) ((D.tile K).pts (l + 1) - (D.tile i).pts m1) ∧
        dist ((D.tile i).pts m1) ((D.tile K).pts (l + 1)) = 96) ∨
      (SameRay ℝ ((D.tile i).pts m1 - D.target.pts 0) ((D.tile K).pts (l + 2) - (D.tile i).pts m1) ∧
        dist ((D.tile i).pts m1) ((D.tile K).pts (l + 2)) = 96)) ∧
    (¬ ∃ (U : Fin cert.leaves.length) (l' : Fin 3),
      (D.tile U).pts l' = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts 0) ∧
      (D.tile U).angleAt l' = 2 * α ∧
      (SameRay ℝ ((D.tile i).pts m1 - D.target.pts 0)
          ((D.tile U).pts (l' + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts 0))) ∨
       SameRay ℝ ((D.tile i).pts m1 - D.target.pts 0)
          ((D.tile U).pts (l' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts 0))))) ∧
    ∃ (K' : Fin cert.leaves.length) (l'' : Fin 3),
      (D.tile K').pts l'' = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts 0) ∧ (D.tile K').angleAt l'' = α ∧
      (SameRay ℝ ((D.tile i).pts m1 - D.target.pts 0)
          ((D.tile K').pts (l'' + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts 0))) ∨
       SameRay ℝ ((D.tile i).pts m1 - D.target.pts 0)
          ((D.tile K').pts (l'' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts 0)))) := by
  have hP0T : (D.tile i0).pts 0 = D.target.pts 0 := hP0.trans hT0.symm
  have hKP1 : (D.tile iK).pts 0 = (D.tile i0).pts 1 := hK0.trans hP1.symm
  have hdK : dist ((D.tile i0).pts 1) ((D.tile iK).pts (0 + 1)) = 96 := by
    have e : (0 : Fin 3) + 1 = 1 := rfl
    rw [e, hP1, hK1]
    have := Erdos634.Draft.G3GControl.dist_toPt_nat (96, 0) (192, 0) 96 (by decide)
    rw [this]; norm_num
  refine ⟨i0, iK, 0, 0, 1, 2, hP0T, hang0, Or.inl ⟨by decide, by decide⟩, hdO1, hdO2, hKP1, hangK,
    Or.inl ⟨hKray, hdK⟩, ?_⟩
  obtain ⟨i, j, hj, hang, hall⟩ := corner_G2 D (fun h => α_irr h) data (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hsides_1125 hword_1125 hw1_1125 hw2_1125 hwc_1125 0 t_ang0
    (by rw [dist01]; norm_num) (by rw [dist01]; norm_num) (by rw [dist02]; norm_num) (by rw [dist02]; norm_num)
  obtain ⟨hc1, -, -, -, -⟩ := corner_has_alpha_tile D (fun h => α_irr h) data t_ang0
  have hli : (D.tile i).localAngle (D.target.pts 0) = α := by
    rw [← hj, Tri.localAngle_vertex]; exact hang
  have hli0 : (D.tile i0).localAngle (D.target.pts 0) = α := by
    rw [← hP0T, Tri.localAngle_vertex]; exact hang0
  have hii : i = i0 := unique_of_cntA D hc1 hli hli0
  subst hii
  have hj0 : j = 0 := (D.tile i0).indep.injective (hj.trans hP0T.symm)
  subst hj0
  exact hall 1 2 (Or.inl ⟨by decide, by decide⟩) hdO1 hdO2
    (nonvertex_double _ 96 (by norm_num) hdO1 (by norm_num) (by norm_num))
    (nonvertex_double _ 80 (by norm_num) hdO2 (by norm_num) (by norm_num)) iK 0 hKP1 hangK
    (Or.inl ⟨hKray, hdK⟩)

/-- The conclusion of G2 is NOT true at an arbitrary base point: at `(1840,0)` leaf `208` has `γ = 2α` with an edge along the base, forward. -/
theorem ctl_gamma_forward_exists : ∃ (U : Fin cert.leaves.length) (l : Fin 3), (D.tile U).pts l = toPt (1840, 0) ∧
    (D.tile U).angleAt l = 2 * α ∧
    SameRay ℝ ((D.tile i0).pts 1 - D.target.pts 0) ((D.tile U).pts (l + 1) - toPt (1840, 0)) := by
  refine ⟨iG, 0, hG0, hangG, ?_⟩
  have e : (0 : Fin 3) + 1 = 1 := rfl
  rw [e, hG1, hP1, hT0]
  have : toPt (1920, 0) - toPt (1840, 0) = (5 / 6 : ℝ) • (toPt (96, 0) - toPt (0, 0)) := by
    ext i
    fin_cases i
    · simp [toPt, rx, Erdos634.CertCoord.mkPt_zero]; norm_num
    · simp [toPt, ry, Erdos634.CertCoord.mkPt_one]
  rw [this]
  exact SameRay.sameRay_pos_smul_right _ (by norm_num)

end Erdos634.GLC

#print axioms Erdos634.GLC.witness_corner_G2
#print axioms Erdos634.GLC.ctl_gamma_forward_exists
