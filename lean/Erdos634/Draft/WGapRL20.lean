/-
Draft/WGapRL20.lean -- written 16 November 2026 (session 13).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2 for `i = 2`, `t = 0`).
Not imported by any aggregate.  No sorry, no native_decide.
General-`i` lattice helpers (`off_PIRg`, `cross_PIRg`) and `rl_two_B12`: the first layer (m = 0) of Lemma RL at `i = 2`, `t = 0`.
At `A_2 = p(2,j+1)` and `A_1 = p(1,j+2)` the wedge fill (`rl_gamma_fill2`) gives `Gamma_2`, `Gamma_1` (each `gamma(t,0)` or FLIPPED);
`Gamma_2` flipped: `rl_close` (tau = 2, m = 0).  `Gamma_2 = gamma(2,0)`, `Gamma_1` flipped: one-edge chord `[B_0, pi(1,1)]` (`chord_a_step`), `nu(1,1)`, `rl_close` (tau = 1, m = 1).
CONCLUSION of `rl_two_B12`: both are non-flipped, i.e. `gamma(2,0)` and `gamma(1,0)` are tiles (branch B3: two-edge chord, not in this module).
-/
import Erdos634.Draft.WGapRL19

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

variable {N : ℕ} {D : CongruentDissection N}

theorem off_PIRg {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t0 m0 t1 m1 t m : ℝ)
    (h : ((t1 - m1 * nuG e f) - (t0 - m0 * nuG e f)) *
        (((j : ℝ) + i + 1 - t + m * (1 + nuG e f)) - ((j : ℝ) + i + 1 - t0 + m0 * (1 + nuG e f))) -
      (((j : ℝ) + i + 1 - t1 + m1 * (1 + nuG e f)) - ((j : ℝ) + i + 1 - t0 + m0 * (1 + nuG e f))) *
        ((t - m * nuG e f) - (t0 - m0 * nuG e f)) ≠ 0) :
    ∀ s : ℝ, 0 < s → PIR e f x j i t m ≠ AffineMap.lineMap (PIR e f x j i t0 m0) (PIR e f x j i t1 m1) s := by
  rw [PIR_lp he hef, PIR_lp he hef, PIR_lp he hef]
  exact off_lat he hef x _ _ _ _ _ _ h

theorem cross_PIRg {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t1 m1 t2 m2 t3 m3 t4 m4 : ℝ) :
    cross (PIR e f x j i t1 m1 - PIR e f x j i t2 m2) (PIR e f x j i t3 m3 - PIR e f x j i t4 m4) =
      kapG e f * (((t1 - m1 * nuG e f) - (t2 - m2 * nuG e f)) *
        (((j : ℝ) + i + 1 - t3 + m3 * (1 + nuG e f)) - ((j : ℝ) + i + 1 - t4 + m4 * (1 + nuG e f))) -
        (((j : ℝ) + i + 1 - t1 + m1 * (1 + nuG e f)) - ((j : ℝ) + i + 1 - t2 + m2 * (1 + nuG e f))) *
          ((t3 - m3 * nuG e f) - (t4 - m4 * nuG e f))) := by
  rw [PIR_lp he hef, PIR_lp he hef, PIR_lp he hef, PIR_lp he hef, cross_lpG]

section rl20

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem rl_two_B12 (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 2 + 1 ≤ f - 1)
    {tDa tUa tUb tNb tNa tDc tUc tNc : Fin N}
    -- the five lattice tiles at `A_2` (`a = 1`, `eta = j`)
    (hDa : HasV D tDa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUa : HasV D tUa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUb : HasV D tUb (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1 + 1)))
    (hNb : HasV D tNb (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x (1 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)))
    (hNa : HasV D tNa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f)))
    -- the extra tiles at `A_1` (`a = 0`, `eta = j + 1`): `D(0,j+1)`, `U(0,j+2)`, `N^0`
    (hDc : HasV D tDc (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1)))
    (hUc : HasV D tUc (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1 + 1)))
    (hNc : HasV D tNc (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1 + 1))
      (lpG (e : ℝ) f 1 x (0 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 1 + 2 + nuG (e : ℝ) f)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) < 0)
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))) :
    ∃ t2 t1 : Fin N,
      HasV D t2 (PIR (e : ℝ) f x j 2 2 0) (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 1) ∧
      HasV D t1 (PIR (e : ℝ) f x j 2 1 0) (PIR (e : ℝ) f x j 2 1 1) (PIR (e : ℝ) f x j 2 0 1) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hν := nuG_spec he0 hef
  have hν0 := nuG_pos he0 hef
  have hκ := kapG_pos he0 hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  -- PIR forms of the known tiles
  have hNa' : HasV D tNa (PIR (e : ℝ) f x j 2 3 0) (PIR (e : ℝ) f x j 2 2 0) (PIR (e : ℝ) f x j 2 2 1) :=
    hasV_PIR he0 hef hNa (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)
  have hNb' : HasV D tNb (PIR (e : ℝ) f x j 2 2 0) (PIR (e : ℝ) f x j 2 1 0) (PIR (e : ℝ) f x j 2 1 1) :=
    hasV_PIR he0 hef hNb (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)
  have hNc' : HasV D tNc (PIR (e : ℝ) f x j 2 1 0) (PIR (e : ℝ) f x j 2 0 0) (PIR (e : ℝ) f x j 2 0 1) :=
    hasV_PIR he0 hef hNc (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)
  -- the point identifications
  have hO2 : ptO (e : ℝ) f x 1 ((j : ℝ) + 1) = PIR (e : ℝ) f x j 2 2 0 := by
    rw [PIR_lp he0 hef]; unfold ptO; exact lpG_congr (by push_cast; ring) (by push_cast; ring)
  have hY2 : ptY (e : ℝ) f x 1 ((j : ℝ) + 1) = PIR (e : ℝ) f x j 2 1 1 := by
    rw [PIR_lp he0 hef]; unfold ptY; exact lpG_congr (by push_cast; ring) (by push_cast; ring)
  have hB2 : PIR (e : ℝ) f x j 2 2 1 = ptO (e : ℝ) f x 1 ((j : ℝ) + 1) + nuG (e : ℝ) f •
      (ptV (e : ℝ) f x 1 ((j : ℝ) + 1) - ptO (e : ℝ) f x 1 ((j : ℝ) + 1)) := by
    rw [PIR_aff (e : ℝ) f x j 2 2 1, one_smul, wvec_eq, ptVO_dc, hO2]
  have hO1 : ptO (e : ℝ) f x 0 ((j : ℝ) + 1 + 1) = PIR (e : ℝ) f x j 2 1 0 := by
    rw [PIR_lp he0 hef]; unfold ptO; exact lpG_congr (by push_cast; ring) (by push_cast; ring)
  have hY1 : ptY (e : ℝ) f x 0 ((j : ℝ) + 1 + 1) = PIR (e : ℝ) f x j 2 0 1 := by
    rw [PIR_lp he0 hef]; unfold ptY; exact lpG_congr (by push_cast; ring) (by push_cast; ring)
  have hB1 : PIR (e : ℝ) f x j 2 1 1 = ptO (e : ℝ) f x 0 ((j : ℝ) + 1 + 1) + nuG (e : ℝ) f •
      (ptV (e : ℝ) f x 0 ((j : ℝ) + 1 + 1) - ptO (e : ℝ) f x 0 ((j : ℝ) + 1 + 1)) := by
    rw [PIR_aff (e : ℝ) f x j 2 1 1, one_smul, wvec_eq, ptVO_dc, hO1]
  -- the two wedge fills
  have hfill2 := rl_gamma_fill2 S x 1 (j : ℝ) hDa hUa hUb hNb hNa
  have hUl1 : HasV D tUb (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1)) :=
    hasV_congr hUb (lpG_congr (by ring) rfl) (lpG_congr (by ring) rfl) (lpG_congr (by ring) rfl)
  have hN1 : HasV D tNb (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)) :=
    hasV_congr hNb (lpG_congr (by ring) rfl) (lpG_congr (by ring) rfl) (lpG_congr (by ring) rfl)
  have hfill1 := rl_gamma_fill2 S x 0 ((j : ℝ) + 1) hDc hUl1 hUc hNc hN1
  -- wrappers
  have hnuA0 : ∀ m' : ℕ, m' ≤ 0 → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') m')
        (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
    intro m' hm'
    obtain rfl : m' = 0 := by omega
    exact ⟨tNa, hasV_congr hNa' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num))⟩
  rcases hfill2 with ⟨τ2, R2, hτ2, hcr2, hR2⟩ | ⟨τ2, R2, hτ2, hcr2, hR2⟩
  · -- `Gamma_2` is `gamma(2,0)`
    have hRC : R2 = PIR (e : ℝ) f x j 2 1 1 := hR2.trans hY2
    have hΓ2 : HasV D τ2 (PIR (e : ℝ) f x j 2 2 0) (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 1) :=
      hasV_congr hτ2 hO2 hB2.symm hRC
    rcases hfill1 with ⟨τ1, R1, hτ1, hcr1, hR1⟩ | ⟨τ1, R1, hτ1, hcr1, hR1⟩
    · have hRC1 : R1 = PIR (e : ℝ) f x j 2 0 1 := hR1.trans hY1
      exact ⟨τ2, τ1, hΓ2, hasV_congr hτ1 hO1 hB1.symm hRC1⟩
    · -- `Gamma_1` flipped: one-edge chord `[B_0, pi(1,1)]`
      exfalso
      have e10 : PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = PIR (e : ℝ) f x j 2 1 0 :=
        PIR_congr (by norm_num) (by norm_num)
      have hleft1 : ∃ (F : Fin N) (R' : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
          HasV D F (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R' ∧
          0 < cross (dcvec (e : ℝ) f x) (R' - PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
        refine ⟨τ1, ptO (e : ℝ) f x 0 ((j : ℝ) + 1 + 1) + nuG (e : ℝ) f •
          (ptY (e : ℝ) f x 0 ((j : ℝ) + 1 + 1) - ptO (e : ℝ) f x 0 ((j : ℝ) + 1 + 1)), 1, Or.inr rfl, ?_, ?_⟩
        · rw [e10, ← hO1]
          refine hasV_congr hτ1.rot.rot.swap rfl ?_ rfl
          rw [one_smul, ← ptVO_dc _ _ x 0 ((j : ℝ) + 1 + 1), ← hR1]; abel
        · rw [e10, ← hO1, ← ptVO_dc _ _ x 0 ((j : ℝ) + 1 + 1), add_sub_cancel_left, cross_smul_right']
          exact mul_pos hν0 (cross_V_Y_pos he0 hef x 0 ((j : ℝ) + 1 + 1))
      have hnuB1 : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
          HasV D T (PIR (e : ℝ) f x j 2 (((1 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) m')
            (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
        intro m' _ hm'
        obtain rfl : m' = 0 := by omega
        exact ⟨tNb, hasV_congr hNb' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      have Zc := rl_beta S x j 2 1 0 0 (by omega) (by omega) hi hnuB1 hleft1
      have e11 : PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) (((0 : ℕ) : ℝ) + 1) = PIR (e : ℝ) f x j 2 1 1 :=
        PIR_congr (by norm_num) (by norm_num)
      rw [e11] at Zc
      have Aα := rl_alpha S x j 2 0 hi (by omega) hnuA0 hP4
      have hcast : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
      have hB0e : PIR (e : ℝ) f x j 2 2 1 = lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j + (((0 + 1 : ℕ) : ℝ)) •
          (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) := by
        rw [hcast]; exact PIR_on_L3 he0 hef x j 2 1 2 (by norm_num)
      have hΞ : EdgeCoverS D (PIR (e : ℝ) f x j 2 2 1)
          (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) (-1) := by
        rw [hB0e]; exact Aα
      -- distances and crosses
      have d1 : dist (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 1) = (e : ℝ) * f := by
        have := dPIR_a he0 hef x j 2 1 1
        rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this
      have d2 : dist (PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 2 1) = (f : ℝ) ^ 2 := by
        have := dPIR_c he0 hef x j 2 1 1
        rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
        rw [dist_comm]; exact this
      have d3 : dist (PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 1 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        have := dPIR_b he0 hef x j 2 1 1
        rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
        rw [dist_comm]; exact this
      have dNa : dist (PIR (e : ℝ) f x j 2 3 0) (PIR (e : ℝ) f x j 2 2 0) = (e : ℝ) * f := by
        have := dPIR_a he0 hef x j 2 2 0
        rwa [show (2 : ℝ) + 1 = 3 by norm_num] at this
      have dCO : dist (PIR (e : ℝ) f x j 2 1 1) (PIR (e : ℝ) f x j 2 2 0) = (f : ℝ) ^ 2 := by
        have := dPIR_c he0 hef x j 2 1 0
        rw [show (1 : ℝ) + 1 = 2 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at this
        rw [dist_comm]; exact this
      have hXY : PIR (e : ℝ) f x j 2 2 1 ≠ PIR (e : ℝ) f x j 2 1 1 := by
        intro h
        rw [h, dist_self] at d1
        linarith
      have hz : 0 < cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 0 - PIR (e : ℝ) f x j 2 2 1) := by
        have : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 0 - PIR (e : ℝ) f x j 2 2 1) = kapG (e : ℝ) f := by
          rw [cross_PIRg he0 hef]; push_cast; ring
        rw [this]; exact hκ
      have hW0 : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 2 - PIR (e : ℝ) f x j 2 2 1) < 0 := by
        have : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 2 - PIR (e : ℝ) f x j 2 2 1) = -kapG (e : ℝ) f := by
          rw [cross_PIRg he0 hef]; push_cast; ring
        rw [this]; linarith
      have aG : (D.tile τ2).localAngle (PIR (e : ℝ) f x j 2 2 1) = γ :=
        (hΓ2.rot.anglesG S.tile S.hM).2.2 dCO
      have aN : (D.tile tNa).localAngle (PIR (e : ℝ) f x j 2 2 1) = α :=
        (hNa'.rot.rot.anglesG S.tile S.hM).1 dNa
      have hcr : 0 < cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
          (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) := by
        have : cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
            (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) = kapG (e : ℝ) f := by
          rw [PIR_lp he0 hef, PIR_lp he0 hef, cross_lpG]; push_cast; ring
        rw [this]; exact hκ
      have hNray := known_off_ray hXY hNa'.rot.rot
        (off_PIRg he0 hef x j 2 2 1 1 1 3 0 (by intro h; nlinarith [h]))
        (off_PIRg he0 hef x j 2 2 1 1 1 2 0 (by intro h; nlinarith [h]))
      have hwcr : 0 < cross (wvec (e : ℝ) f x) (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) := by
        have h := cross_wvec_step he0 hef x j 2 1 1
        rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
        have e1 : PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1 = (-1 : ℝ) • (PIR (e : ℝ) f x j 2 2 1 - PIR (e : ℝ) f x j 2 1 1) := by
          rw [neg_one_smul]; abel
        rw [e1, cross_smul_right', h]; linarith
      obtain ⟨τν, hν11⟩ := chord_a_step S (X := PIR (e : ℝ) f x j 2 2 1) (Y := PIR (e : ℝ) f x j 2 1 1)
        (Z := PIR (e : ℝ) f x j 2 2 0) (W0 := PIR (e : ℝ) f x j 2 1 2) (wv := wvec (e : ℝ) f x) (tG := τ2) (tN := tNa)
        hXY hΓ2.rot hz aG aN hΞ hcr hNray Zc hwcr d1 d2 d3 hW0
      have hnuA1 : ∀ m' : ℕ, m' ≤ 1 → ∃ T : Fin N,
          HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') m')
            (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
        intro m' hm'
        interval_cases m'
        · exact ⟨tNa, hasV_congr hNa' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
            (PIR_congr (by norm_num) (by norm_num))⟩
        · exact ⟨τν, hasV_congr hν11 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
            (PIR_congr (by norm_num) (by norm_num))⟩
      have hnuB2 : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 1 → ∃ T : Fin N,
          HasV D T (PIR (e : ℝ) f x j 2 (((1 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) m')
            (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
        intro m' _ hm'
        interval_cases m'
        · exact ⟨tNb, hasV_congr hNb' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
            (PIR_congr (by norm_num) (by norm_num))⟩
        · exact ⟨τν, hasV_congr hν11 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
            (PIR_congr (by norm_num) (by norm_num))⟩
      exact rl_close S x j 2 1 0 1 (by omega) (by omega) hi (by omega) hnuA1 hP4 hnuB2 hleft1
  · -- `Gamma_2` flipped: `rl_close` with `tau = 2`, `m = 0`
    exfalso
    have e20 : PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = PIR (e : ℝ) f x j 2 2 0 :=
      PIR_congr (by norm_num) (by norm_num)
    have hleft' : ∃ (F : Fin N) (R' : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
        HasV D F (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R' ∧
        0 < cross (dcvec (e : ℝ) f x) (R' - PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
      refine ⟨τ2, ptO (e : ℝ) f x 1 ((j : ℝ) + 1) + nuG (e : ℝ) f •
        (ptY (e : ℝ) f x 1 ((j : ℝ) + 1) - ptO (e : ℝ) f x 1 ((j : ℝ) + 1)), 1, Or.inr rfl, ?_, ?_⟩
      · rw [e20, ← hO2]
        refine hasV_congr hτ2.rot.rot.swap rfl ?_ rfl
        rw [one_smul, ← ptVO_dc _ _ x 1 ((j : ℝ) + 1), ← hR2]; abel
      · rw [e20, ← hO2, ← ptVO_dc _ _ x 1 ((j : ℝ) + 1), add_sub_cancel_left, cross_smul_right']
        exact mul_pos hν0 (cross_V_Y_pos he0 hef x 1 ((j : ℝ) + 1))
    have hnuB0 : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨tNa, hasV_congr hNa' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    exact rl_close S x j 2 2 0 0 (by omega) (by omega) hi (by omega) hnuA0 hP4 hnuB0 hleft'

end rl20

#print axioms rl_two_B12

end Erdos634.Draft.WGapStmt
