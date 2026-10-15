/-
Draft/PgramE1Full.lean -- the unit parallelogram at `e = 1`, for every `f ≥ 2`.

`e = 1`, tile `(a, b, c) = (f, f² − 1, f²)`, `N₁ = 3f² − 1`.  The parallelogram `P₁` has sides `Y₁ = 3f² − 1` (base
direction `u`) and `X₁ = f³` (leg direction `w`), with included angle `β` (`cos β = (3f² − 1)/(2f³)`).

`thm_pgram_e1`: there are unit vectors `u`, `w` and a triangle `M` with sides `f² − 1`, `f`, `f²` such that the angle
between `u` and `w` is the angle of `M` opposite its side `f² − 1` (that is `β`), and the parallelogram
`{s u + t w : 0 ≤ s ≤ 3f² − 1, 0 ≤ t ≤ f³}` is tiled by `2(3f² − 1)` triangles congruent to `M`.

Construction.  In the skew frame `Phi f` of `WFrameF` (unit vectors
`g1`, `g2` at angle `α + β`), `X₁ w = f² g1 + A g2` with `A = f(f² − 1)`, so `P₁` is the set
`{0 ≤ t ≤ A, f² t ≤ A s ≤ A (3f² − 1) + f² t}`.  The lines `s = f²`, `s = 2f² − 1`, `s = 3f² − 1` cut it into
* `Λ`: the triangle `(0,0), (f², 0), (f², A)` = the tile scaled by `f` (`f²` tiles, ladder);
* `Σ`: `[f², 2f² − 1] × [0, A]`, one column of `f² − 1` two-tile bricks (`2(f² − 1)` tiles);
* `[2f² − 1, 3f² − 1] × [0, A]`, an `f × f` grid of the other brick (`2f²` tiles);
* the triangle `(C, 0), (C, A), (C + f², A)`, `C = 3f² − 1`, again the tile scaled by `f` (`f²` tiles).
Total `f² + 2(f² − 1) + 2f² + f² = 2(3f² − 1)`.  No sorry, no native_decide.
-/
import Erdos634.Draft.WPgramWrap
import Erdos634.Draft.WGridF

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN Sh_Rect interior_disj_fst)

namespace Erdos634.Draft.PgramE1Full

open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.BrickGridF
open Erdos634.Draft.WPgramF Erdos634.Draft.WtoDeltaF Erdos634.Draft.WPgramWrap
open Erdos634.Draft.WGridF (A_pos)

/-- close a field identity: clear denominators, then `ring` -/
local macro "fsr" : tactic => `(tactic| first | (field_simp; ring) | field_simp | ring)

/-- `P₁` in skew coordinates `(s, t)` -/
def P1set (F : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ F * (F ^ 2 - 1) ∧ F ^ 2 * p.2 ≤ F * (F ^ 2 - 1) * p.1 ∧
    F * (F ^ 2 - 1) * p.1 ≤ F * (F ^ 2 - 1) * (3 * F ^ 2 - 1) + F ^ 2 * p.2}

theorem mem_P1set {F : ℝ} {p : ℝ × ℝ} : p ∈ P1set F ↔ 0 ≤ p.2 ∧ p.2 ≤ F * (F ^ 2 - 1) ∧
    F ^ 2 * p.2 ≤ F * (F ^ 2 - 1) * p.1 ∧
    F * (F ^ 2 - 1) * p.1 ≤ F * (F ^ 2 - 1) * (3 * F ^ 2 - 1) + F ^ 2 * p.2 := Iff.rfl

/-- the decomposition of `P₁` by the lines `s = f²` and `s = 3f² − 1` -/
theorem P1_union {F : ℝ} (hF : 1 < F) :
    (LT (F ^ 2) (F * (F ^ 2 - 1)) ∪ Rect (F ^ 2) (3 * F ^ 2 - 1) 0 (F * (F ^ 2 - 1))) ∪
      Sh (3 * F ^ 2 - 1, 0) (UT (F ^ 2) (F * (F ^ 2 - 1))) = P1set F := by
  have hF0 : (0 : ℝ) < F := by linarith
  have hA : (0 : ℝ) < F * (F ^ 2 - 1) := by
    have : (0 : ℝ) < F ^ 2 - 1 := by nlinarith
    positivity
  have hF2 : (0 : ℝ) < F ^ 2 := by positivity
  have hC : F ^ 2 ≤ 3 * F ^ 2 - 1 := by nlinarith
  ext p
  obtain ⟨s, t⟩ := p
  simp only [P1set, WBrickF.LT, WBrickF.UT, Rect, Sh, Set.mem_union, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3, h4⟩)
    · have ht : t ≤ F * (F ^ 2 - 1) := by
        by_contra hcon
        push Not at hcon
        nlinarith [mul_lt_mul_of_pos_right hcon hF2, mul_le_mul_of_nonneg_right h2 hA.le]
      refine ⟨h3, ht, by linarith, ?_⟩
      nlinarith [mul_le_mul_of_nonneg_left (le_trans h2 hC) hA.le, mul_nonneg hF2.le h3]
    · refine ⟨h3, h4, ?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left h4 hF2.le, mul_le_mul_of_nonneg_left h1 hA.le]
      · nlinarith [mul_le_mul_of_nonneg_left h2 hA.le, mul_nonneg hF2.le h3]
    · refine ⟨h1, h2, ?_, by linarith⟩
      have hs : 3 * F ^ 2 - 1 ≤ s := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hF2.le, mul_le_mul_of_nonneg_left (le_trans hC hs) hA.le]
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hs1 : s ≤ F ^ 2
    · left; left
      have hs0 : 0 ≤ s := by
        by_contra hcon
        push Not at hcon
        nlinarith [mul_neg_of_pos_of_neg hA hcon, mul_nonneg hF2.le h1]
      exact ⟨hs0, hs1, h1, by linarith⟩
    · push Not at hs1
      by_cases hs2 : s ≤ 3 * F ^ 2 - 1
      · left; right
        exact ⟨hs1.le, hs2, h1, h2⟩
      · push Not at hs2
        right
        exact ⟨h1, h2, by linarith, by linarith⟩

/-- the ladder triangle of the model tile at scale `f` -/
theorem ladder_target (f : ℕ) (hf : 2 ≤ f) :
    (ladderCD (MF (f : ℝ) (hF f hf)) f (by omega)).target
      = Erdos634.Subdivision.bigTri _ _ _ (indep_eta (MF (f : ℝ) (hF f hf))) f (by omega) := rfl

/-- `Λ`: the triangle `(f², A), (f², 0), (0, 0)` (vertices in the order of the ladder triangle) -/
noncomputable def lamTri (f : ℕ) (hf : 2 ≤ f) : Tri :=
  triC (f : ℝ) (hF f hf) ((f : ℝ) ^ 2, (f : ℝ) * ((f : ℝ) ^ 2 - 1)) ((f : ℝ) ^ 2, 0) (0, 0) (by
    have h1 := hF f hf
    have hA := A_pos f hf
    intro h
    have hp := mul_pos (by positivity : (0 : ℝ) < (f : ℝ) ^ 2) hA
    dsimp only at h
    linarith)

/-- the right triangle `(0, 0), (0, A), (f², A)` (to be shifted by `(3f² − 1, 0)`) -/
noncomputable def upTri (f : ℕ) (hf : 2 ≤ f) : Tri :=
  triC (f : ℝ) (hF f hf) (0, 0) (0, (f : ℝ) * ((f : ℝ) ^ 2 - 1)) ((f : ℝ) ^ 2, (f : ℝ) * ((f : ℝ) ^ 2 - 1)) (by
    have h1 := hF f hf
    have hA := A_pos f hf
    intro h
    have hp := mul_pos (by positivity : (0 : ℝ) < (f : ℝ) ^ 2) hA
    dsimp only at h
    linarith)

theorem lam_congruent (f : ℕ) (hf : 2 ≤ f) :
    ((ladderCD (MF (f : ℝ) (hF f hf)) f (by omega)).target).Congruent (lamTri f hf) := by
  have h1 := hF f hf
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  rw [ladder_target f hf]
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [big_d01]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [lamTri, triC_pts, MF_pts, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    dsimp only
    fsr
  · rw [big_d12]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [lamTri, triC_pts, MF_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    dsimp only
    fsr
  · rw [big_d20]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [lamTri, triC_pts, MF_pts, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    dsimp only
    fsr

theorem up_congruent (f : ℕ) (hf : 2 ≤ f) :
    ((ladderCD (MF (f : ℝ) (hF f hf)) f (by omega)).target).Congruent (upTri f hf) := by
  have h1 := hF f hf
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  rw [ladder_target f hf]
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [big_d01]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [upTri, triC_pts, MF_pts, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    dsimp only
    fsr
  · rw [big_d12]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [upTri, triC_pts, MF_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    dsimp only
    fsr
  · rw [big_d20]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [upTri, triC_pts, MF_pts, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    dsimp only
    fsr

/-- `Λ` is tiled by `f²` tiles -/
theorem lam_tiling (f : ℕ) (hf : 2 ≤ f) :
    Nonempty (RTiling (Phi (f : ℝ) '' LT ((f : ℝ) ^ 2) ((f : ℝ) * ((f : ℝ) ^ 2 - 1)))
      (MF (f : ℝ) (hF f hf)) (f * f)) := by
  have h1 := hF f hf
  obtain ⟨R⟩ := seed_of_cd (ladderCD (MF (f : ℝ) h1) f (by omega)) (lamTri f hf) (MF (f : ℝ) h1)
    (lam_congruent f hf) (Tri.Congruent.refl _)
  refine ⟨RTiling.cast ?_ R⟩
  unfold lamTri
  rw [carrier_triC]
  have hset : ({((f : ℝ) ^ 2, (f : ℝ) * ((f : ℝ) ^ 2 - 1)), ((f : ℝ) ^ 2, 0), ((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))
      = {((0 : ℝ), (0 : ℝ)), ((f : ℝ) ^ 2, 0), ((f : ℝ) ^ 2, (f : ℝ) * ((f : ℝ) ^ 2 - 1))} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset, hull_LT _ _ (by positivity) (A_pos f hf)]

/-- the right triangle is tiled by `f²` tiles -/
theorem up_tiling (f : ℕ) (hf : 2 ≤ f) :
    Nonempty (RTiling (Phi (f : ℝ) '' UT ((f : ℝ) ^ 2) ((f : ℝ) * ((f : ℝ) ^ 2 - 1)))
      (MF (f : ℝ) (hF f hf)) (f * f)) := by
  have h1 := hF f hf
  obtain ⟨R⟩ := seed_of_cd (ladderCD (MF (f : ℝ) h1) f (by omega)) (upTri f hf) (MF (f : ℝ) h1)
    (up_congruent f hf) (Tri.Congruent.refl _)
  refine ⟨RTiling.cast ?_ R⟩
  unfold upTri
  rw [carrier_triC, hull_UT _ _ (by positivity) (A_pos f hf)]

/-- **`P₁` in skew coordinates is tiled by `2(3f² − 1)` tiles.** -/
theorem P1_tiling (f : ℕ) (hf : 2 ≤ f) :
    Nonempty (RTiling (Phi (f : ℝ) '' P1set (f : ℝ)) (MF (f : ℝ) (hF f hf)) (2 * (3 * f ^ 2 - 1))) := by
  have h1 := hF f hf
  have c1 := cast_f1 f hf
  have c2 := cast_f2 f hf
  have hA := A_pos f hf
  have hF2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hf4 : 4 ≤ f ^ 2 := by nlinarith
  obtain ⟨Lam⟩ := lam_tiling f hf
  obtain ⟨Up⟩ := up_tiling f hf
  -- `Σ`: one column of `f² − 1` bricks of width `f² − 1`
  have Sig := shift_rect (gridA h1 0 (f ^ 2 - 2)) ((f : ℝ) ^ 2) 0 (2 * (f : ℝ) ^ 2 - 1)
    ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) (by push_cast; ring) (by rw [c2, add_zero])
  -- the `f × f` grid of the other brick
  have Gr := shift_rect (gridB h1 (f - 1) (f - 1)) (2 * (f : ℝ) ^ 2 - 1) 0 (3 * (f : ℝ) ^ 2 - 1)
    ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) (by rw [c1]; ring) (by rw [c1]; ring)
  have Mid := hstack h1 (by nlinarith : (f : ℝ) ^ 2 ≤ 2 * (f : ℝ) ^ 2 - 1)
    (by nlinarith : 2 * (f : ℝ) ^ 2 - 1 ≤ 3 * (f : ℝ) ^ 2 - 1) Sig Gr
  -- the shifted right triangle
  have UpS := shiftR Up (3 * (f : ℝ) ^ 2 - 1, 0)
  -- `Λ ∪ middle`
  have d1 : Disjoint (interior (Phi (f : ℝ) '' LT ((f : ℝ) ^ 2) ((f : ℝ) * ((f : ℝ) ^ 2 - 1))))
      (interior (Phi (f : ℝ) '' Rect ((f : ℝ) ^ 2) (3 * (f : ℝ) ^ 2 - 1) 0 ((f : ℝ) * ((f : ℝ) ^ 2 - 1)))) :=
    disjoint_image h1 (interior_disj_fst ((f : ℝ) ^ 2) (fun p hp => hp.2.1) (fun p hp => hp.1))
  have U1 := union Lam Mid d1
  rw [← Set.image_union] at U1
  have d2 : Disjoint (interior (Phi (f : ℝ) '' (LT ((f : ℝ) ^ 2) ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) ∪
        Rect ((f : ℝ) ^ 2) (3 * (f : ℝ) ^ 2 - 1) 0 ((f : ℝ) * ((f : ℝ) ^ 2 - 1)))))
      (interior (Phi (f : ℝ) '' Sh (3 * (f : ℝ) ^ 2 - 1, 0) (UT ((f : ℝ) ^ 2) ((f : ℝ) * ((f : ℝ) ^ 2 - 1))))) := by
    refine disjoint_image h1 (interior_disj_fst (3 * (f : ℝ) ^ 2 - 1) ?_ ?_)
    · rintro p (hp | hp)
      · have : p.1 ≤ (f : ℝ) ^ 2 := hp.2.1
        nlinarith [h1]
      · exact hp.2.1
    · intro p hp
      have : 0 ≤ (p - ((3 * (f : ℝ) ^ 2 - 1, (0 : ℝ)))).1 := hp.2.2.1
      simp only [Prod.fst_sub] at this
      linarith
  have U2 := union U1 UpS d2
  rw [← Set.image_union, P1_union h1] at U2
  refine ⟨RTiling.castN ?_ U2⟩
  have e1 : f - 1 + 1 = f := by omega
  have e2 : f ^ 2 - 2 + 1 = f ^ 2 - 1 := by omega
  rw [e1, e2]
  zify [show 1 ≤ f ^ 2 by omega, show 1 ≤ 3 * f ^ 2 by omega]
  ring

/-! ## The statement in terms of the parallelogram -/

/-- the leg direction: the unit vector along `f² g1 + A g2` -/
noncomputable def wdir (F : ℝ) : Plane := (1 / F ^ 3) • (F ^ 2 • g1 + (F * (F ^ 2 - 1)) • g2 F)

theorem inner_g1_g2 {F : ℝ} (hF : 1 < F) : inner ℝ g1 (g2 F) = 1 / (2 * F) := by
  have hF0 : (0 : ℝ) < F := by linarith
  have h := sq_Phi hF (1, 0) (0, 1)
  rw [Phi_10, Phi_01, dist_eq_norm, norm_sub_sq_real, norm_g1 hF, norm_g2 hF] at h
  dsimp only at h
  have h3 : inner ℝ g1 (g2 F) = 1 / F / 2 := by linear_combination (-1 / 2 : ℝ) * h
  rw [h3]
  ring

theorem leg_vec_norm {F : ℝ} (hF : 1 < F) : ‖F ^ 2 • g1 + (F * (F ^ 2 - 1)) • g2 F‖ = F ^ 3 := by
  have hF0 : (0 : ℝ) < F := by linarith
  have h := sq_Phi hF (F ^ 2, F * (F ^ 2 - 1)) (0, 0)
  rw [Phi_zero, dist_zero_right] at h
  have e : Phi F (F ^ 2, F * (F ^ 2 - 1)) = F ^ 2 • g1 + (F * (F ^ 2 - 1)) • g2 F := rfl
  rw [e] at h
  refine Erdos634.Draft.SumTwoSquares.eqsq (norm_nonneg _) (by positivity) ?_
  rw [h]
  dsimp only
  fsr

theorem norm_wdir {F : ℝ} (hF : 1 < F) : ‖wdir F‖ = 1 := by
  have hF0 : (0 : ℝ) < F := by linarith
  unfold wdir
  rw [norm_smul, leg_vec_norm hF, Real.norm_of_nonneg (by positivity)]
  fsr

/-- the angle between the base direction and the leg direction is the angle of the tile opposite its side `f² − 1` -/
theorem angle_g1_wdir {F : ℝ} (hF : 1 < F) :
    InnerProductGeometry.angle g1 (wdir F) = (MF F hF).angleAt 2 := by
  have hF0 : (0 : ℝ) < F := by linarith
  have hA : (0 : ℝ) < F ^ 2 - 1 := by nlinarith
  have hi := inner_g1_g2 hF
  have n1 := norm_g1 hF
  have n2 := norm_g2 hF
  have i11 : inner ℝ g1 g1 = 1 := by rw [real_inner_self_eq_norm_sq, n1]; norm_num
  have i22 : inner ℝ (g2 F) (g2 F) = 1 := by rw [real_inner_self_eq_norm_sq, n2]; norm_num
  have i21 : inner ℝ (g2 F) g1 = 1 / (2 * F) := by rw [real_inner_comm]; exact hi
  -- left side
  have hL : InnerProductGeometry.angle g1 (wdir F)
      = Real.arccos ((3 * F ^ 2 - 1) / (2 * F ^ 3)) := by
    unfold wdir
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ (by positivity : (0 : ℝ) < 1 / F ^ 3)]
    unfold InnerProductGeometry.angle
    rw [leg_vec_norm hF, n1, inner_add_right, real_inner_smul_right, real_inner_smul_right, i11, hi]
    congr 1
    fsr
  -- right side
  have e02 : (MF F hF).pts 0 -ᵥ (MF F hF).pts 2 = -((F ^ 2 - 1) • g1 + F • g2 F) := by
    rw [MF_p0 hF, MF_p2 hF, vsub_eq_sub]
    unfold Phi
    dsimp only
    module
  have e12 : (MF F hF).pts 1 -ᵥ (MF F hF).pts 2 = -(F • g2 F) := by
    rw [MF_p1 hF, MF_p2 hF, vsub_eq_sub]
    unfold Phi
    dsimp only
    module
  have nd : ‖(F ^ 2 - 1) • g1 + F • g2 F‖ = F ^ 2 := by
    have h := (MF_sides hF).2.2
    rw [MF_p0 hF, MF_p2 hF, dist_comm, dist_eq_norm] at h
    have e : Phi F (F ^ 2 - 1, F) - Phi F (0, 0) = (F ^ 2 - 1) • g1 + F • g2 F := by
      unfold Phi
      dsimp only
      module
    rw [e] at h
    exact h
  have hR : (MF F hF).angleAt 2 = Real.arccos ((3 * F ^ 2 - 1) / (2 * F ^ 3)) := by
    unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
    rw [show ((2 : Fin 3) + 1) = 0 from rfl, show ((2 : Fin 3) + 2) = 1 from rfl, e02, e12,
      InnerProductGeometry.angle_neg_neg,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hF0]
    unfold InnerProductGeometry.angle
    rw [nd, n2, inner_add_left, real_inner_smul_left, real_inner_smul_left, i22, hi]
    congr 1
    fsr
  rw [hL, hR]

/-- `P₁` as the parallelogram spanned by `g1` (base direction) and `wdir` (leg direction), tiled by `2(3f² − 1)`
copies of `MF f` -/
theorem P1_pgram (f : ℕ) (hf : 2 ≤ f) :
    Nonempty (RTiling {p : Plane | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 3 * (f : ℝ) ^ 2 - 1 ∧ 0 ≤ t ∧
        t ≤ (f : ℝ) ^ 3 ∧ p = s • g1 + t • wdir (f : ℝ)} (MF (f : ℝ) (hF f hf)) (2 * (3 * f ^ 2 - 1))) := by
  have h1 := hF f hf
  have hF0 : (0 : ℝ) < (f : ℝ) := by linarith
  have hA := A_pos f hf
  obtain ⟨R⟩ := P1_tiling f hf
  refine ⟨?_⟩
  refine RTiling.cast ?_ R
  have hF3 : (0 : ℝ) < (f : ℝ) ^ 3 := by positivity
  have hF0' : (f : ℝ) ≠ 0 := hF0.ne'
  have hq : (f : ℝ) ^ 2 - 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hA
    exact lt_irrefl _ hA
  ext p
  constructor
  · rintro ⟨⟨s, t⟩, hst, rfl⟩
    obtain ⟨a1, a2, a3, a4⟩ := mem_P1set.1 hst
    dsimp only at a1 a2 a3 a4
    -- `(s, t) ↦ (s − f² t / A) g1 + (f³ t / A) w`
    refine ⟨s - (f : ℝ) ^ 2 * t / ((f : ℝ) * ((f : ℝ) ^ 2 - 1)),
      (f : ℝ) ^ 3 * t / ((f : ℝ) * ((f : ℝ) ^ 2 - 1)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [sub_nonneg, div_le_iff₀ hA]
      linarith
    · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hA]
      linarith
    · exact div_nonneg (mul_nonneg hF3.le a1) hA.le
    · rw [div_le_iff₀ hA]
      nlinarith [mul_le_mul_of_nonneg_left a2 hF3.le]
    · show (s, t).1 • g1 + (s, t).2 • g2 (f : ℝ) = _
      unfold wdir
      dsimp only
      match_scalars <;> fsr
  · rintro ⟨s, t, a1, a2, a3, a4, rfl⟩
    have e : (f : ℝ) ^ 2 * (t * ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) / (f : ℝ) ^ 3)
        = (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (t / (f : ℝ)) := by fsr
    refine ⟨(s + t / (f : ℝ), t * ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) / (f : ℝ) ^ 3),
      mem_P1set.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · dsimp only
      exact div_nonneg (mul_nonneg a3 hA.le) hF3.le
    · dsimp only
      rw [div_le_iff₀ hF3]
      nlinarith [mul_le_mul_of_nonneg_right a4 hA.le]
    · dsimp only
      linarith [e, mul_nonneg hA.le a1]
    · dsimp only
      linarith [e, mul_le_mul_of_nonneg_left a2 hA.le]
    · show (s + t / (f : ℝ), t * ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) / (f : ℝ) ^ 3).1 • g1 +
          (s + t / (f : ℝ), t * ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) / (f : ℝ) ^ 3).2 • g2 (f : ℝ) = _
      unfold wdir
      dsimp only
      match_scalars <;> fsr

/-- **`thm:pgram-e1`.**  For `f ≥ 2` the parallelogram `P₁` with sides `3f² − 1` and `f³` and included angle `β` is
tiled by `2(3f² − 1)` copies of the tile `(f, f² − 1, f²)`. -/
theorem thm_pgram_e1 (f : ℕ) (hf : 2 ≤ f) :
    ∃ (u w : Plane) (M : Tri), ‖u‖ = 1 ∧ ‖w‖ = 1 ∧
      dist (M.pts 0) (M.pts 1) = (f : ℝ) ^ 2 - 1 ∧ dist (M.pts 1) (M.pts 2) = f ∧
      dist (M.pts 0) (M.pts 2) = (f : ℝ) ^ 2 ∧
      InnerProductGeometry.angle u w = M.angleAt 2 ∧
      Nonempty (RTiling {p : Plane | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 3 * (f : ℝ) ^ 2 - 1 ∧ 0 ≤ t ∧
          t ≤ (f : ℝ) ^ 3 ∧ p = s • u + t • w} M (2 * (3 * f ^ 2 - 1))) := by
  have h1 := hF f hf
  obtain ⟨s1, s2, s3⟩ := MF_sides h1
  exact ⟨g1, wdir (f : ℝ), MF (f : ℝ) h1, norm_g1 h1, norm_wdir h1, s1, s2, s3, angle_g1_wdir h1, P1_pgram f hf⟩

end Erdos634.Draft.PgramE1Full

#print axioms Erdos634.Draft.PgramE1Full.P1_tiling
#print axioms Erdos634.Draft.PgramE1Full.thm_pgram_e1
