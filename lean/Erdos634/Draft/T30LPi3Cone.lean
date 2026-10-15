import Mathlib.Tactic
import Erdos634.WedgeExtremal
import Erdos634.PinPlumbing
import Erdos634.BaseSelection
import Erdos634.Draft.T30LPi3Tile

/-!
# `Pi3Cone`: the cone / oriented-angle dictionary and the corner tile's edges on the target sides

* `cone_oangle` (the dictionary): if `(o.oangle u₁ u₂).sign = 1` and `x = s u₁ + t u₂` with `s, t ≥ 0`, `x ≠ 0`, then the oriented angle
  `o.oangle u₁ x` has `toReal` in `[0, toReal (o.oangle u₁ u₂)]`.  (Proof: signs by `oangle_sign_smul_add_smul_*`, additivity `oangle_add`,
  and the `2π` bookkeeping.)  This is exactly the hypothesis `hφm, hψm` of `WedgeExtremal.corner_on_wedge_sides` / `SectorFill.sector_step_pi3`.
* `hull_cone`: a point of a triangle's carrier lies in the cone `v + ℝ≥0 (A−v) + ℝ≥0 (B−v)` at a vertex `v`.
* `corner_tile_on_sides`: on any `CongruentDissection` with `SixtyData` and `α ∉ ℚπ`, at a target corner of angle `π/3` there is a tile `i` with a vertex at the
  corner whose two edges there are on the two target sides (`SameRay`), in one order or the other.  Uses `corner_fan_real` (a `π/3` tile exists),
  `localAngle_cases` (it is a vertex), `hull_cone` + `cone_oangle` (edge directions in the wedge), `corner_on_wedge_sides` (extremality).
* Witness: `witness_corner_on_sides`, instantiated on the 1440-tiling `G3CSixtyControl.D` at every corner.
-/

namespace Erdos634.Pi3Cone

open Erdos634.Geometry Erdos634.Pi3Tile

theorem cone_oangle (o : Orientation ℝ Plane (Fin 2)) {u1 u2 : Plane} (hs : (o.oangle u1 u2).sign = 1)
    {s t : ℝ} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hx : s • u1 + t • u2 ≠ 0) :
    0 ≤ (o.oangle u1 (s • u1 + t • u2)).toReal ∧
      (o.oangle u1 (s • u1 + t • u2)).toReal ≤ (o.oangle u1 u2).toReal := by
  have hu1 : u1 ≠ 0 := o.left_ne_zero_of_oangle_sign_eq_one hs
  have hu2 : u2 ≠ 0 := o.right_ne_zero_of_oangle_sign_eq_one hs
  set x := s • u1 + t • u2 with hxdef
  have ha : 0 ≤ (o.oangle u1 x).sign := by
    rw [hxdef, o.oangle_sign_smul_add_smul_right, hs, mul_one]
    exact sign_nonneg_iff.mpr ht0
  have hb : 0 ≤ (o.oangle x u2).sign := by
    rw [hxdef, o.oangle_sign_smul_add_smul_left, hs, mul_one]
    exact sign_nonneg_iff.mpr hs0
  have ha' := Real.Angle.toReal_nonneg_iff_sign_nonneg.mpr ha
  have hb' := Real.Angle.toReal_nonneg_iff_sign_nonneg.mpr hb
  have hadd : o.oangle u1 x + o.oangle x u2 = o.oangle u1 u2 := o.oangle_add hu1 hx hu2
  have hθ0 : 0 ≤ (o.oangle u1 u2).toReal := Real.Angle.toReal_nonneg_iff_sign_nonneg.mpr (by rw [hs]; decide)
  have hθne : (o.oangle u1 u2).toReal ≠ 0 := by
    intro h
    have := Real.Angle.toReal_eq_zero_iff.mp h
    rw [this] at hs
    simp at hs
  have hθpos : 0 < (o.oangle u1 u2).toReal := lt_of_le_of_ne hθ0 (Ne.symm hθne)
  have hθle := Real.Angle.toReal_le_pi (o.oangle u1 u2)
  have hale := Real.Angle.toReal_le_pi (o.oangle u1 x)
  have hble := Real.Angle.toReal_le_pi (o.oangle x u2)
  have hcoe : (((o.oangle u1 x).toReal + (o.oangle x u2).toReal : ℝ) : Real.Angle)
      = (((o.oangle u1 u2).toReal : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_toReal, Real.Angle.coe_toReal, hadd]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hcoe
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < k := by nlinarith
  have hk0 : k = 0 := by
    have h1 : k < 1 := by exact_mod_cast hk1
    have h2 : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0] at hk
  simp at hk
  exact ⟨ha', by linarith⟩

theorem hull_cone (T : Tri) (k : Fin 3) :
    ∀ x ∈ T.carrier, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      x - T.pts k = s • (T.pts (k + 1) - T.pts k) + t • (T.pts (k + 2) - T.pts k) := by
  have hconv : Convex ℝ {x : Plane | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      x - T.pts k = s • (T.pts (k + 1) - T.pts k) + t • (T.pts (k + 2) - T.pts k)} := by
    intro x hx y hy a b ha hb hab
    obtain ⟨s, t, hs, ht, hx⟩ := hx
    obtain ⟨s', t', hs', ht', hy⟩ := hy
    refine ⟨a * s + b * s', a * t + b * t', by positivity, by positivity, ?_⟩
    have e : a • x + b • y - T.pts k = a • (x - T.pts k) + b • (y - T.pts k) := by
      have : T.pts k = (a + b) • T.pts k := by rw [hab, one_smul]
      conv_lhs => rw [this]
      simp only [smul_sub, add_smul]; abel
    rw [e, hx, hy]
    simp only [smul_add, smul_smul, add_smul]; abel
  have hsub : T.carrier ⊆ {x : Plane | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      x - T.pts k = s • (T.pts (k + 1) - T.pts k) + t • (T.pts (k + 2) - T.pts k)} := by
    refine convexHull_min ?_ hconv
    rintro z ⟨i, rfl⟩
    have h3 : ∀ k i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide
    rcases h3 k i with rfl | rfl | rfl
    · exact ⟨0, 0, le_refl _, le_refl _, by simp⟩
    · exact ⟨1, 0, zero_le_one, le_refl _, by simp⟩
    · exact ⟨0, 1, le_refl _, zero_le_one, by simp⟩
  exact fun x hx => hsub hx

theorem exists_pos_orientation {u1 u2 : Plane} (hu1 : u1 ≠ 0) (hu2 : u2 ≠ 0)
    (h : InnerProductGeometry.angle u1 u2 = Real.pi / 3) :
    ∃ o : Orientation ℝ Plane (Fin 2), (o.oangle u1 u2).sign = 1 := by
  let o0 : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hne : (o0.oangle u1 u2).sign ≠ 0 := by
    intro h0
    rcases o0.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h0 with h1 | h1 | h1 | h1
    · exact hu1 h1
    · exact hu2 h1
    · rw [h] at h1; have := Real.pi_pos; linarith
    · rw [h] at h1; have := Real.pi_pos; linarith
  have hcases : ∀ s : SignType, s ≠ 0 → s = -1 ∨ s = 1 := by decide
  rcases hcases _ hne with hm | hp
  · refine ⟨-o0, ?_⟩
    rw [Orientation.oangle_neg_orientation_eq_neg, Real.Angle.sign_neg, hm]; decide
  · exact ⟨o0, hp⟩

theorem sameRay_of_angle_zero {x y : Plane} (o : Orientation ℝ Plane (Fin 2)) (h : o.oangle x y = 0) :
    SameRay ℝ x y := (Orientation.oangle_eq_zero_iff_sameRay o).mp h

/-- **The corner tile's edges are on the target sides.** -/
theorem corner_tile_on_sides {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (k : Fin 3) (hk : D.target.angleAt k = Real.pi / 3) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k ∧ (D.tile i).angleAt j = Real.pi / 3 ∧
      ((SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k)) ∨
       (SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k))) := by
  classical
  have hpi := Real.pi_pos
  set O := D.target.pts k with hO
  obtain ⟨-, -, hc, -⟩ := corner_fan_real D hirr hS k hk
  obtain ⟨i, hi⟩ : ∃ i : Fin N, (D.tile i).localAngle O = Real.pi / 3 := by
    have hc' : cnt D.toDissection O (Real.pi / 3) = 1 := hc
    have : 0 < cnt D.toDissection O (Real.pi / 3) := by omega
    unfold cnt at this
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, by simpa using hi⟩
  obtain ⟨j, hj, hjang⟩ : ∃ j : Fin 3, O = (D.tile i).pts j ∧
      (D.tile i).localAngle O = cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) := by
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) O with h | h | h | h
    · exact h
    · rw [hi] at h; linarith
    · rw [hi] at h; linarith
    · rw [hi] at h; linarith
  refine ⟨i, j, hj.symm, by rw [← hi, hjang]; rfl, ?_⟩
  set A := D.target.pts (k + 1)
  set B := D.target.pts (k + 2)
  set P := (D.tile i).pts (j + 1)
  set Q := (D.tile i).pts (j + 2)
  have hcorner : cornerAngle P O Q = Real.pi / 3 := by rw [← hi, hjang, ← hj]
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1 : (D.tile i).pts j ≠ (D.tile i).pts (j + 1) := hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)
  have hj2 : (D.tile i).pts j ≠ (D.tile i).pts (j + 2) := hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)
  have hP : P - O ≠ 0 := by rw [sub_ne_zero, hj]; exact hj1.symm
  have hQ : Q - O ≠ 0 := by rw [sub_ne_zero, hj]; exact hj2.symm
  have hAO : A ≠ O := fun h => by
    have := D.target.indep.injective h
    exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k this
  have hBO : B ≠ O := fun h => by
    have := D.target.indep.injective h
    exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k this
  have hu1 : A - O ≠ 0 := sub_ne_zero.mpr hAO
  have hu2 : B - O ≠ 0 := sub_ne_zero.mpr hBO
  have hang : InnerProductGeometry.angle (A - O) (B - O) = Real.pi / 3 := by
    rw [← hk]; unfold Tri.angleAt cornerAngle EuclideanGeometry.angle; simp only [vsub_eq_sub]; rfl
  obtain ⟨o, ho⟩ := exists_pos_orientation hu1 hu2 hang
  have hθ : (o.oangle (A - O) (B - O)).toReal = Real.pi / 3 := by
    rw [o.oangle_eq_angle_of_sign_eq_one ho, hang, Real.Angle.toReal_coe_eq_self_iff]
    constructor <;> linarith
  -- the tile's vertices are in the target cone
  have hconeP : ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ P - O = s • (A - O) + t • (B - O) :=
    hull_cone D.target k P (Erdos634.BaseSelection.tile_subset_target D.toDissection i
      (subset_convexHull ℝ _ ⟨j + 1, rfl⟩))
  have hconeQ : ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ Q - O = s • (A - O) + t • (B - O) :=
    hull_cone D.target k Q (Erdos634.BaseSelection.tile_subset_target D.toDissection i
      (subset_convexHull ℝ _ ⟨j + 2, rfl⟩))
  obtain ⟨sP, tP, hsP, htP, ePQ⟩ := hconeP
  obtain ⟨sQ, tQ, hsQ, htQ, eQ⟩ := hconeQ
  have dP := cone_oangle o ho hsP htP (by rw [← ePQ]; exact hP)
  have dQ := cone_oangle o ho hsQ htQ (by rw [← eQ]; exact hQ)
  rw [← ePQ, hθ] at dP
  rw [← eQ, hθ] at dQ
  have key := Erdos634.WedgeExtremal.Dissection.corner_on_wedge_sides o (A := O) (P := P) (Q := Q) (u := A - O)
    hu1 hP hQ (by linarith) rfl rfl ⟨dP.1, dP.2⟩ ⟨dQ.1, dQ.2⟩ hcorner
  -- helper: toReal = 0 gives same ray; toReal = π/3 gives same ray as `B - O`
  have h0 : ∀ y : Plane, y ≠ 0 → (o.oangle (A - O) y).toReal = 0 → SameRay ℝ (A - O) y := fun y _ h =>
    sameRay_of_angle_zero o (Real.Angle.toReal_eq_zero_iff.mp h)
  have h3 : ∀ y : Plane, y ≠ 0 → (o.oangle (A - O) y).toReal = Real.pi / 3 → SameRay ℝ (B - O) y := by
    intro y hy h
    have e1 : o.oangle (A - O) y = o.oangle (A - O) (B - O) := by
      rw [← Real.Angle.coe_toReal (o.oangle (A - O) y), ← Real.Angle.coe_toReal (o.oangle (A - O) (B - O)), h, hθ]
    have := o.oangle_add hu1 hu2 hy
    have e2 : o.oangle (B - O) y = 0 := by
      have h' : o.oangle (A - O) (B - O) + o.oangle (B - O) y = o.oangle (A - O) (B - O) := by
        rw [this, e1]
      simpa using h'
    exact sameRay_of_angle_zero o e2
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h0 _ hP h1, h3 _ hQ h2⟩
  · right; exact ⟨h3 _ hP h1, h0 _ hQ h2⟩

section witness

open Erdos634.Draft.G3CSixtyControl

/-- **WITNESS (real dissection).**  `corner_tile_on_sides` on the certified 1440-tiling `G3CSixtyControl.D` (equilateral side 240, tile
`(5,8,7)`, `α ∉ ℚπ`) at each target corner: all hypotheses (`Irr α`, `SixtyData`, corner angle `π/3`) are discharged by the existing control. -/
theorem witness_corner_on_sides (k : Fin 3) :
    ∃ i j, (D.tile i).pts j = D.target.pts k ∧ (D.tile i).angleAt j = Real.pi / 3 ∧
      ((SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k)) ∨
       (SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k))) :=
  corner_tile_on_sides D (hirr := α_irr) data k (t_angle k)

end witness

#print axioms cone_oangle
#print axioms hull_cone
#print axioms exists_pos_orientation
#print axioms corner_tile_on_sides
#print axioms witness_corner_on_sides

end Erdos634.Pi3Cone
