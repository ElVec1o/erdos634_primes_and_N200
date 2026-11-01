-- Draft/Collar23A.lean -- (2,3) collar, part A: the skew frame of the tile (4,5,6) (cos alpha = 3/4), the triangle `TT`,
-- the separation lemma, translation of region tilings.  UNAUDITED.  No sorry, no native_decide.  NOT imported by All.
-- Credit: B. Herdt (the 1125-tiling by (4,5,6): seed template), Beeson-Rosu (tilings of an isosceles triangle, skew frames),
-- Paliy (collar idea); the strip / cap / slice structure is the project's AI assistant's proposal P1 (internal working notes), found by
-- engine tilings of S2/S2V.  This file is infrastructure only.
import Erdos634.Draft.S2LCore
import Erdos634.Draft.CollarParam
import Erdos634.Draft.RegionTiling
import Erdos634.CertCoord
import Erdos634.SssCongruent

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)

namespace Erdos634.Draft.Collar23

noncomputable def s7 : ℝ := Real.sqrt 7
theorem s7_pos : 0 < s7 := Real.sqrt_pos.mpr (by norm_num)
theorem s7_sq : s7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)

/-- Skew coordinates: `Phi (x,y) = x e1 + y e2`, `e1 = (1,0)`, `e2 = (3/4, sqrt 7 / 4)`; unit vectors, `cos alpha = 3/4`. -/
noncomputable def Phi (p : ℝ × ℝ) : Plane := mkPt (p.1 + 3 / 4 * p.2) (s7 / 4 * p.2)

theorem Phi_apply0 (p : ℝ × ℝ) : Phi p 0 = p.1 + 3 / 4 * p.2 := by simp [Phi]
theorem Phi_apply1 (p : ℝ × ℝ) : Phi p 1 = s7 / 4 * p.2 := by simp [Phi]

noncomputable def Psi (q : Plane) : ℝ × ℝ := (q 0 - 3 * q 1 / s7, 4 * q 1 / s7)

theorem Psi_Phi (p : ℝ × ℝ) : Psi (Phi p) = p := by
  have h := s7_pos.ne'
  ext
  · simp only [Psi, Phi_apply0, Phi_apply1]; field_simp; ring
  · simp only [Psi, Phi_apply1]; field_simp

theorem Phi_Psi (q : Plane) : Phi (Psi q) = q := by
  have h := s7_pos.ne'
  ext i
  fin_cases i
  · show Phi (Psi q) 0 = q 0
    rw [Phi_apply0]; simp only [Psi]; field_simp; ring
  · show Phi (Psi q) 1 = q 1
    rw [Phi_apply1]; simp only [Psi]; field_simp

theorem Phi_cont : Continuous Phi := by
  unfold Phi mkPt
  have h : Continuous fun p : ℝ × ℝ => (![p.1 + 3 / 4 * p.2, s7 / 4 * p.2] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp h

theorem Psi_cont : Continuous Psi := by
  unfold Psi
  have h0 : Continuous fun q : Plane => q 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun q : Plane => q 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  fun_prop

noncomputable def PhiH : (ℝ × ℝ) ≃ₜ Plane where
  toFun := Phi
  invFun := Psi
  left_inv := Psi_Phi
  right_inv := Phi_Psi
  continuous_toFun := Phi_cont
  continuous_invFun := Psi_cont

theorem interior_image (S : Set (ℝ × ℝ)) : interior (Phi '' S) = Phi '' interior S :=
  (PhiH.image_interior S).symm

theorem disjoint_image {A B : Set (ℝ × ℝ)} (h : Disjoint (interior A) (interior B)) :
    Disjoint (interior (Phi '' A)) (interior (Phi '' B)) := by
  rw [interior_image, interior_image]
  exact (Set.disjoint_image_iff PhiH.injective).mpr h

theorem Phi_add (p q : ℝ × ℝ) : Phi (p + q) = Phi p + Phi q := by
  ext i; fin_cases i
  · show Phi (p + q) 0 = (Phi p + Phi q) 0
    simp only [PiLp.add_apply, Phi_apply0, Prod.fst_add, Prod.snd_add]; ring
  · show Phi (p + q) 1 = (Phi p + Phi q) 1
    simp only [PiLp.add_apply, Phi_apply1, Prod.snd_add]; ring

/-- `Phi` as a linear map (for `image_convexHull`). -/
noncomputable def PhiL : (ℝ × ℝ) →ₗ[ℝ] Plane where
  toFun := Phi
  map_add' := Phi_add
  map_smul' := by
    intro c p
    ext i; fin_cases i
    · show Phi (c • p) 0 = (c • Phi p) 0
      simp only [PiLp.smul_apply, Phi_apply0, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    · show Phi (c • p) 1 = (c • Phi p) 1
      simp only [PiLp.smul_apply, Phi_apply1, Prod.smul_snd, smul_eq_mul]; ring

theorem PhiL_eq (p : ℝ × ℝ) : PhiL p = Phi p := rfl

/-! ## Separation by a line -/

/-- Closed half-planes on opposite sides of a non-constant affine function have disjoint interiors. -/
theorem interior_disj_lin {S T : Set (ℝ × ℝ)} (A B c : ℝ) (hAB : 0 < A ^ 2 + B ^ 2)
    (hS : ∀ p ∈ S, c ≤ A * p.1 + B * p.2) (hT : ∀ p ∈ T, A * p.1 + B * p.2 ≤ c) :
    Disjoint (interior S) (interior T) := by
  rw [Set.disjoint_left]
  intro p hpS hpT
  obtain ⟨ε, hε, hballS⟩ := Metric.isOpen_iff.mp isOpen_interior p hpS
  obtain ⟨δ, hδ, hballT⟩ := Metric.isOpen_iff.mp isOpen_interior p hpT
  set m := min ε δ with hm
  have hmpos : 0 < m := lt_min hε hδ
  set K := |A| + |B| + 1 with hK
  have hKpos : 0 < K := by positivity
  set r := m / (2 * K) with hr
  have hrpos : 0 < r := by positivity
  have hAr : |r * A| < m := by
    rw [abs_mul, abs_of_pos hrpos, hr]
    have : |A| ≤ K := by linarith [abs_nonneg B]
    calc m / (2 * K) * |A| ≤ m / (2 * K) * K := by gcongr
      _ = m / 2 := by field_simp
      _ < m := by linarith
  have hBr : |r * B| < m := by
    rw [abs_mul, abs_of_pos hrpos, hr]
    have : |B| ≤ K := by linarith [abs_nonneg A]
    calc m / (2 * K) * |B| ≤ m / (2 * K) * K := by gcongr
      _ = m / 2 := by field_simp
      _ < m := by linarith
  have hd1 : dist (p.1 + r * A, p.2 + r * B) p < m := by
    rw [Prod.dist_eq]; simp [Real.dist_eq]
    exact ⟨by rwa [abs_mul] at hAr, by rwa [abs_mul] at hBr⟩
  have hd2 : dist (p.1 - r * A, p.2 - r * B) p < m := by
    rw [Prod.dist_eq]; simp [Real.dist_eq]
    exact ⟨by rwa [abs_mul] at hAr, by rwa [abs_mul] at hBr⟩
  have h1 := hS _ (interior_subset (hballS (lt_of_lt_of_le hd2 (min_le_left _ _))))
  have h2 := hT _ (interior_subset (hballT (lt_of_lt_of_le hd1 (min_le_right _ _))))
  simp only at h1 h2
  nlinarith [mul_pos hrpos hAB]

/-! ## Triangles -/

/-- twice the signed area (in skew coordinates, up to the fixed factor). -/
def cr (o a b : ℝ × ℝ) : ℝ := (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

theorem det3_Phi (p q r : ℝ × ℝ) :
    det3 (p.1 + 3 / 4 * p.2) (s7 / 4 * p.2) (q.1 + 3 / 4 * q.2) (s7 / 4 * q.2)
      (r.1 + 3 / 4 * r.2) (s7 / 4 * r.2) = s7 / 4 * cr p q r := by
  simp only [det3, cr]; ring

/-- The triangle with skew-coordinate vertices `p q r`. -/
noncomputable def TT (p q r : ℝ × ℝ) (h : cr p q r ≠ 0) : Tri :=
  mkTri (p.1 + 3 / 4 * p.2) (s7 / 4 * p.2) (q.1 + 3 / 4 * q.2) (s7 / 4 * q.2)
    (r.1 + 3 / 4 * r.2) (s7 / 4 * r.2) (by
      rw [det3_Phi]; exact mul_ne_zero (by have := s7_pos; positivity) h)

theorem TT_pts (p q r : ℝ × ℝ) (h : cr p q r ≠ 0) :
    (TT p q r h).pts = ![Phi p, Phi q, Phi r] := rfl

theorem TT_carrier (p q r : ℝ × ℝ) (h : cr p q r ≠ 0) :
    (TT p q r h).carrier = Phi '' convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)) := by
  have hr : Set.range (TT p q r h).pts = Phi '' ({p, q, r} : Set (ℝ × ℝ)) := by
    rw [TT_pts]
    ext x
    simp only [Set.mem_range, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k
      · left; rfl
      · right; left; rfl
      · right; right; rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [Tri.carrier, hr]
  have := PhiL.image_convexHull ({p, q, r} : Set (ℝ × ℝ))
  simp only [PhiL_eq] at this
  rw [← this]

/-- Squared distance in skew coordinates: `|dx e1 + dy e2|^2 = dx^2 + (3/2) dx dy + dy^2`. -/
theorem dist_sq_Phi (p q : ℝ × ℝ) :
    dist (Phi p) (Phi q) ^ 2 = (p.1 - q.1) ^ 2 + 3 / 2 * (p.1 - q.1) * (p.2 - q.2) + (p.2 - q.2) ^ 2 := by
  have h7 := s7_sq
  unfold Phi
  rw [dist_sq_mkPt]
  nlinarith [h7]

theorem eq_of_sq_eq' {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (h : d ^ 2 = v ^ 2) : d = v := by
  nlinarith [sq_nonneg (d - v), sq_nonneg (d + v)]

/-- SSS congruence of two skew triangles from the three squared side lengths, in the order (01,12,20). -/
theorem TT_congruent (p q r p' q' r' : ℝ × ℝ) (h : cr p q r ≠ 0) (h' : cr p' q' r' ≠ 0)
    (h01 : (p.1 - q.1) ^ 2 + 3 / 2 * (p.1 - q.1) * (p.2 - q.2) + (p.2 - q.2) ^ 2 =
      (p'.1 - q'.1) ^ 2 + 3 / 2 * (p'.1 - q'.1) * (p'.2 - q'.2) + (p'.2 - q'.2) ^ 2)
    (h12 : (q.1 - r.1) ^ 2 + 3 / 2 * (q.1 - r.1) * (q.2 - r.2) + (q.2 - r.2) ^ 2 =
      (q'.1 - r'.1) ^ 2 + 3 / 2 * (q'.1 - r'.1) * (q'.2 - r'.2) + (q'.2 - r'.2) ^ 2)
    (h20 : (r.1 - p.1) ^ 2 + 3 / 2 * (r.1 - p.1) * (r.2 - p.2) + (r.2 - p.2) ^ 2 =
      (r'.1 - p'.1) ^ 2 + 3 / 2 * (r'.1 - p'.1) * (r'.2 - p'.2) + (r'.2 - p'.2) ^ 2) :
    (TT p q r h).Congruent (TT p' q' r' h') := by
  have d : ∀ (a b c : ℝ × ℝ) (hh : cr a b c ≠ 0) (i j : Fin 3),
      dist ((TT a b c hh).pts i) ((TT a b c hh).pts j) = dist (![Phi a, Phi b, Phi c] i) (![Phi a, Phi b, Phi c] j) :=
    fun a b c hh i j => by rw [TT_pts]
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [d, d]
    refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [dist_sq_Phi, dist_sq_Phi]; exact h01
  · rw [d, d]
    refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    rw [dist_sq_Phi, dist_sq_Phi]; exact h12
  · rw [d, d]
    refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    rw [dist_sq_Phi, dist_sq_Phi]; exact h20

/-! ## Translation of region tilings in skew coordinates -/

def Sh (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | p - v ∈ S}

theorem image_shift (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    (fun x : Plane => x + Phi v) '' (Phi '' S) = Phi '' Sh v S := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p + v, ?_, by rw [Phi_add]⟩
    show p + v - v ∈ S; simpa using hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Phi (p - v), ⟨p - v, hp, rfl⟩, ?_⟩
    show Phi (p - v) + Phi v = Phi p
    rw [← Phi_add]; simp

/-- Translate a region tiling by `v` in skew coordinates. -/
noncomputable def shiftR {S : Set (ℝ × ℝ)} {M : Tri} {N : ℕ}
    (R : RTiling (Phi '' S) M N) (v : ℝ × ℝ) : RTiling (Phi '' Sh v S) M N :=
  RTiling.cast (image_shift v S) (Erdos634.Draft.RegionTiling.map R (IsometryEquiv.addRight (Phi v)))

end Erdos634.Draft.Collar23
