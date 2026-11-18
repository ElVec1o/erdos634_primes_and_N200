/-
Draft/WGapRL15a.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 step (6) at `i = 1`).
Not imported by any aggregate.  No sorry, no native_decide.
Lattice facts at `A_1 = p(1,j+1)` for step (6) (module WGapRL15): the points `pA1, pB0, pA0, pC0, p2j, p1j, p0j1` (literal forms of the hypotheses of `rl_one`), their distances,
crosses and off-ray facts.
-/
import Erdos634.Draft.WGapRL14

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

noncomputable abbrev pA1 (e f x : ℝ) (j : ℕ) : Plane := lpG e f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)
noncomputable abbrev pB0 (e f x : ℝ) (j : ℕ) : Plane := lpG e f 1 x ((0 : ℝ) + 1 - nuG e f) ((j : ℝ) + 2 + nuG e f)
noncomputable abbrev pA0 (e f x : ℝ) (j : ℕ) : Plane := lpG e f 1 x 0 ((j : ℝ) + 1 + 1)
noncomputable abbrev pC0 (e f x : ℝ) (j : ℕ) : Plane := lpG e f 1 x (0 - nuG e f) ((j : ℝ) + 1 + 2 + nuG e f)
noncomputable abbrev p2j (e f x : ℝ) (j : ℕ) : Plane := lpG e f 1 x ((0 : ℝ) + 1 + 1) (j : ℝ)
noncomputable abbrev p1j (e f x : ℝ) (j : ℕ) : Plane := lpG e f 1 x ((0 : ℝ) + 1) (j : ℝ)
noncomputable abbrev p0j1 (e f x : ℝ) (j : ℕ) : Plane := lpG e f 1 x 0 ((j : ℝ) + 1)

section rl15a

variable {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ)

include he hef

theorem s6_dAB : dist (pA1 e f x j) (pB0 e f x j) = f ^ 2 - e ^ 2 := by
  rw [dist_comm]; exact dist_N_GG he hef (by norm_num) ((0 : ℝ) + 1) (j : ℝ)

theorem s6_d2B : dist (p2j e f x j) (pB0 e f x j) = f ^ 2 := by
  rw [dist_comm]; exact dist_N_VG he hef (by norm_num) ((0 : ℝ) + 1) (j : ℝ)

theorem s6_d2A : dist (p2j e f x j) (pA1 e f x j) = e * f :=
  dist_step_aG he hef (by norm_num) ((0 : ℝ) + 1) (j : ℝ)

theorem s6_dAA : dist (pA1 e f x j) (pA0 e f x j) = e * f :=
  dist_step_aG he hef (by norm_num) (0 : ℝ) ((j : ℝ) + 1)

theorem s6_dAC : dist (pA1 e f x j) (pC0 e f x j) = f ^ 2 := by
  rw [dist_comm]; exact dist_N_VG he hef (by norm_num) (0 : ℝ) ((j : ℝ) + 1)

theorem s6_dA0C : dist (pA0 e f x j) (pC0 e f x j) = f ^ 2 - e ^ 2 := by
  rw [dist_comm]; exact dist_N_GG he hef (by norm_num) (0 : ℝ) ((j : ℝ) + 1)

theorem s6_dBC : dist (pB0 e f x j) (pC0 e f x j) = e * f := by
  have hν := nuG_spec he hef
  have hf0 : (0 : ℝ) < f := he.trans hef
  refine dist_lp_nu he hef (mul_pos he hf0).le ?_
  linear_combination (-(f ^ 2)) * hν

theorem s6_cr_B2 : cross (pB0 e f x j - pA1 e f x j) (p2j e f x j - pA1 e f x j) = -kapG e f := by
  unfold pB0 pA1 p2j; rw [cross_lpG]; ring

theorem s6_cr_BC : cross (pB0 e f x j - pA1 e f x j) (pC0 e f x j - pA1 e f x j) = kapG e f := by
  unfold pB0 pA1 pC0; rw [cross_lpG]; ring

theorem s6_cr_B1j : cross (pB0 e f x j - pA1 e f x j) (p1j e f x j - pA1 e f x j) = kapG e f * nuG e f := by
  unfold pB0 pA1 p1j; rw [cross_lpG]; ring

theorem s6_cr_B01 : cross (pB0 e f x j - pA1 e f x j) (p0j1 e f x j - pA1 e f x j) = kapG e f * (1 + nuG e f) := by
  unfold pB0 pA1 p0j1; rw [cross_lpG]; ring

theorem s6_cr_BA0 : cross (pB0 e f x j - pA1 e f x j) (pA0 e f x j - pA1 e f x j) = kapG e f := by
  unfold pB0 pA1 pA0; rw [cross_lpG]; ring

theorem s6_cr_A01 : cross (pA0 e f x j - pA1 e f x j) (p0j1 e f x j - pA1 e f x j) = kapG e f := by
  unfold pA0 pA1 p0j1; rw [cross_lpG]; ring

theorem s6_cr_A0C : cross (pA0 e f x j - pA1 e f x j) (pC0 e f x j - pA1 e f x j) = -kapG e f := by
  unfold pA0 pA1 pC0; rw [cross_lpG]; ring

theorem s6_cr_A0B : cross (pA0 e f x j - pA1 e f x j) (pB0 e f x j - pA1 e f x j) = -kapG e f := by
  unfold pA0 pA1 pB0; rw [cross_lpG]; ring

theorem s6_cr_A01j : cross (pA0 e f x j - pA1 e f x j) (p1j e f x j - pA1 e f x j) = kapG e f := by
  unfold pA0 pA1 p1j; rw [cross_lpG]; ring

theorem s6_neg2 : p2j e f x j - pA1 e f x j = (-1 : ℝ) • (pA0 e f x j - pA1 e f x j) := by
  unfold p2j pA1 pA0 lpG
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring

theorem s6_XY_B : pA1 e f x j ≠ pB0 e f x j := by
  intro h
  have := s6_dAB he hef x j
  rw [h, dist_self] at this
  have hb := b_posG he hef
  linarith

theorem s6_XY_A0 : pA1 e f x j ≠ pA0 e f x j := by
  intro h
  have := s6_dAA he hef x j
  rw [h, dist_self] at this
  have := mul_pos he (he.trans hef)
  linarith

theorem s6_offneg {X Y P : Plane} (hXY : X ≠ Y) (h : P - X = (-1 : ℝ) • (Y - X)) :
    ∀ s : ℝ, 0 < s → P ≠ AffineMap.lineMap X Y s := by
  refine off_ray_of_dot_neg ?_
  have h0 : P 0 - X 0 = -(Y 0 - X 0) := by
    have := congrArg (fun v : Plane => v 0) h
    simpa using this
  have h1 : P 1 - X 1 = -(Y 1 - X 1) := by
    have := congrArg (fun v : Plane => v 1) h
    simpa using this
  rw [h0, h1]
  have hne : (Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2 ≠ 0 := by
    intro hz
    apply hXY
    have a0 : Y 0 - X 0 = 0 := by nlinarith [sq_nonneg (Y 0 - X 0), sq_nonneg (Y 1 - X 1)]
    have a1 : Y 1 - X 1 = 0 := by nlinarith [sq_nonneg (Y 0 - X 0), sq_nonneg (Y 1 - X 1)]
    apply plane_ext
    · linarith
    · linarith
  have hpos : 0 < (Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hne)
  nlinarith [hpos]

theorem s6_PIR_A1 : PIR e f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = pA1 e f x j := by
  rw [PIR_lp1 he hef]; exact lpG_congr (by push_cast; ring) (by push_cast; ring)

theorem s6_B0_sub : pB0 e f x j - pA1 e f x j = nuG e f • dcvec e f x := by
  have h1 : pB0 e f x j = PIR e f x j 1 1 1 := by
    rw [PIR_lp1 he hef]; exact lpG_congr (by ring) (by ring)
  have h0 : pA1 e f x j = PIR e f x j 1 1 0 := by
    rw [PIR_lp1 he hef]; exact lpG_congr (by ring) (by ring)
  rw [h1, h0, PIR_aff e f x j 1 1 1, one_smul, wvec_eq]
  abel

end rl15a

#print axioms s6_dBC
#print axioms s6_cr_A01j
#print axioms s6_neg2
#print axioms s6_offneg

end Erdos634.Draft.WGapStmt
