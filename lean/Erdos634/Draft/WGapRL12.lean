/-
Draft/WGapRL12.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2 for `i = 1`, `t = 0`: the two-layer case of Lemma RL).
Not imported by any aggregate.  No sorry, no native_decide.
`rl_one` = `lemma_RL` for `i = 1`, `t = 0`: the five lattice tiles at `A_1 = p(1, j+1)` (`D(0,j)`, `U(1,j)`, `U(0,j+1)`, `N_0(j+1)`, `N_1(j)`), `Pi4` and the left tile `r3` at `A_0` give False.
Route: `rl_gamma_fill2` at `A_1`; flipped tile => `rl_close` (tau = 1, m = 0); else `rl_alpha` / `rl_beta` / `rl_beta_fill_abs` at `B_0`, the `beta` tile has its `a`-edge on `[B_0, C_0]`
(the `c`-edge would pass through `C_0` against the cover of `rl_beta`), `same_third` gives `nu(0,1)`, `rl_close` (tau = 0, m = 1).
-/
import Erdos634.Draft.WGapRL12a

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

theorem ptVO_dc (e f x a η0 : ℝ) : ptV e f x a η0 - ptO e f x a η0 = dcvec e f x := by
  unfold ptV ptO dcvec
  have h1 : lpG e f 1 x a (η0 + sMir e f) = lpG e f 1 x ((a + 1) + (-1)) (η0 + sMir e f) :=
    lpG_congr (by ring) rfl
  rw [h1, lpG_add]
  abel

section rl12

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 8000000 in
theorem rl_one (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 1 + 1 ≤ f - 1)
    {tUi tDL tUl tN tN2 : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 + 1) (j : ℝ))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x (0 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)))
    (hN2 : HasV D tN2 (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j) < 0)
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hν := nuG_spec he0 hef
  have hν0 := nuG_pos he0 hef
  have hκ := kapG_pos he0 hef
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := b_posG he0 hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  have hA := S.hA
  -- PIR forms of the known tiles
  have hN1 : ∃ T : Fin N, HasV D T (PIR (e : ℝ) f x j 1 (1 + 1) 0) (PIR (e : ℝ) f x j 1 1 0) (PIR (e : ℝ) f x j 1 1 1) :=
    ⟨tN2, hasV_PIR he0 hef hN2 (by ring) (by push_cast; ring) (by ring) (by push_cast; ring) (by ring) (by push_cast; ring)⟩
  have hN0 : ∃ T : Fin N, HasV D T (PIR (e : ℝ) f x j 1 1 0) (PIR (e : ℝ) f x j 1 0 0) (PIR (e : ℝ) f x j 1 0 1) :=
    ⟨tN, hasV_PIR he0 hef hN (by ring) (by push_cast; ring) (by ring) (by push_cast; ring) (by ring) (by push_cast; ring)⟩
  obtain ⟨T1, hT1⟩ := hN1
  obtain ⟨T0, hT0⟩ := hN0
  -- wrappers for the hypotheses of rl_alpha / rl_beta / rl_close
  have hnuA0 : ∀ m' : ℕ, m' ≤ 0 → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m') m')
        (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
    intro m' hm'
    obtain rfl : m' = 0 := by omega
    exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num))⟩
  have hnuB0 : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j 1 (((0 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) m')
        (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
    intro m' _ hm'
    obtain rfl : m' = 0 := by omega
    exact ⟨T0, hasV_congr hT0 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num))⟩
  -- identifications of the output of rl_gamma_fill2
  have hO1 : ptO (e : ℝ) f x 0 ((j : ℝ) + 1) = PIR (e : ℝ) f x j 1 1 0 := by
    rw [PIR_lp1 he0 hef]; unfold ptO; exact lpG_congr (by ring) (by ring)
  have hYp : ptY (e : ℝ) f x 0 ((j : ℝ) + 1) = PIR (e : ℝ) f x j 1 0 1 := by
    rw [PIR_lp1 he0 hef]; unfold ptY; exact lpG_congr (by ring) (by ring)
  have hB0 : PIR (e : ℝ) f x j 1 1 1 = ptO (e : ℝ) f x 0 ((j : ℝ) + 1) + nuG (e : ℝ) f • (ptV (e : ℝ) f x 0 ((j : ℝ) + 1) - ptO (e : ℝ) f x 0 ((j : ℝ) + 1)) := by
    rw [PIR_aff (e : ℝ) f x j 1 1 1, one_smul, wvec_eq, ptVO_dc, hO1]
  have hXY : PIR (e : ℝ) f x j 1 1 1 ≠ PIR (e : ℝ) f x j 1 0 1 := by
    intro h
    have := rl12_dBC he0 hef x j
    rw [h, dist_self] at this
    linarith
  have hfill := rl_gamma_fill2 S x 0 (j : ℝ) hDL hUl hUi hN hN2
  rcases hfill with ⟨τ, R, hτ, hcrR, hRY⟩ | ⟨τ, R, hτ, hcrR, hRV⟩
  · -- non-flipped: the gamma tile (O1, B0, C0)
    have hRC : R = PIR (e : ℝ) f x j 1 0 1 := hRY.trans hYp
    have hΓ : HasV D τ (PIR (e : ℝ) f x j 1 1 0) (PIR (e : ℝ) f x j 1 1 1) (PIR (e : ℝ) f x j 1 0 1) :=
      hasV_congr hτ hO1 hB0.symm hRC
    have hz : 0 < cross (PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1) (PIR (e : ℝ) f x j 1 1 0 - PIR (e : ℝ) f x j 1 1 1) := by
      have : cross (PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1) (PIR (e : ℝ) f x j 1 1 0 - PIR (e : ℝ) f x j 1 1 1) =
          nuG (e : ℝ) f * cross (ptV (e : ℝ) f x 0 ((j : ℝ) + 1) - ptO (e : ℝ) f x 0 ((j : ℝ) + 1)) (R - ptO (e : ℝ) f x 0 ((j : ℝ) + 1)) := by
        rw [hB0, ← hO1, ← hRC]
        exact cross_aux _ _ _ _
      rw [this]; exact mul_pos hν0 hcrR
    have aG : (D.tile τ).localAngle (PIR (e : ℝ) f x j 1 1 1) = γ :=
      (hΓ.rot.anglesG S.tile S.hM).2.2 (rl12_dCO he0 hef x j)
    have aN : (D.tile T1).localAngle (PIR (e : ℝ) f x j 1 1 1) = α :=
      (hT1.rot.rot.anglesG S.tile S.hM).1 (rl12_dNa he0 hef x j)
    -- the cover of the right of Lambda_3 at B0
    have Aα := rl_alpha S x j 1 0 hi (by omega) hnuA0 hP4
    have hB0e : PIR (e : ℝ) f x j 1 1 1 = lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j + (((0 + 1 : ℕ) : ℝ)) •
        (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j) := by
      rw [PIR_lp1 he0 hef, lp_add_smul]
      exact lpG_congr (by push_cast; ring) (by push_cast; ring)
    have hΞ : EdgeCoverS D (PIR (e : ℝ) f x j 1 1 1)
        (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j) (-1) := by
      rw [hB0e]; exact Aα
    have hcr : 0 < cross (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)
        (PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1) := by
      have : cross (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)
          (PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1) = kapG (e : ℝ) f := by
        rw [PIR_lp1 he0 hef, PIR_lp1 he0 hef, cross_lpG]
        push_cast; ring
      rw [this]; exact hκ
    have hNray := known_off_ray hXY hT1.rot.rot
      (off_PIR he0 hef x j 1 1 0 1 (1 + 1) 0 (by intro h; nlinarith [h]))
      (off_PIR he0 hef x j 1 1 0 1 1 0 (by intro h; nlinarith [h]))
    obtain ⟨τ', P, W, hV, ⟨s, hs0, hPs⟩, hW, hang, hPW, hsides⟩ :=
      rl_beta_fill_abs S hXY hΓ.rot hz aG aN hΞ hcr hNray
    have hdXP : dist (PIR (e : ℝ) f x j 1 1 1) P = s * ((e : ℝ) * f) := by
      rw [hPs, dist_left_lineMap, Real.norm_of_nonneg hs0.le, rl12_dBC he0 hef x j]
    -- the known tiles N^1, N^0
    have hnuA1 : ∀ m' : ℕ, m' ≤ 1 → (HasV D τ' (PIR (e : ℝ) f x j 1 1 1) (PIR (e : ℝ) f x j 1 0 1) (PIR (e : ℝ) f x j 1 0 (1 + 1))) →
        ∃ T : Fin N, HasV D T (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m') m')
          (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
      intro m' hm' hnu01
      interval_cases m'
      · exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      · exact ⟨τ', hasV_congr hnu01 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
    have hnuB1 : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 1 → (HasV D τ' (PIR (e : ℝ) f x j 1 1 1) (PIR (e : ℝ) f x j 1 0 1) (PIR (e : ℝ) f x j 1 0 (1 + 1))) →
        ∃ T : Fin N, HasV D T (PIR (e : ℝ) f x j 1 (((0 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm' hnu01
      interval_cases m'
      · exact ⟨T0, hasV_congr hT0 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      · exact ⟨τ', hasV_congr hnu01 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
    rcases hsides with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- a-edge on the chord: P = C0, W = pi(0,2)
      have hs1 : s = 1 := by
        rw [h1] at hdXP
        have : (s - 1) * ((e : ℝ) * f) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h hef0.ne'
      have hP : P = PIR (e : ℝ) f x j 1 0 1 := by rw [hPs, hs1, AffineMap.lineMap_apply_one]
      have hWeq : PIR (e : ℝ) f x j 1 0 (1 + 1) = W := by
        refine same_third hXY ?_ ?_ (rl12_cross_Z he0 hef x j) hW
        · rw [rl12_dZB he0 hef x j, dist_comm W, h2]
        · have hZC : dist (PIR (e : ℝ) f x j 1 0 (1 + 1)) (PIR (e : ℝ) f x j 1 0 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
            rw [dist_comm]; exact rl12_dCZ he0 hef x j
          have hWC : dist W (PIR (e : ℝ) f x j 1 0 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
            rw [← hP, dist_comm]; exact hPW
          rw [hZC, hWC]
      have hnu01 : HasV D τ' (PIR (e : ℝ) f x j 1 1 1) (PIR (e : ℝ) f x j 1 0 1) (PIR (e : ℝ) f x j 1 0 (1 + 1)) :=
        hasV_congr hV rfl hP hWeq.symm
      exact rl_close S x j 1 0 0 1 (by omega) (by omega) hi (by omega) (fun m' hm' => hnuA1 m' hm' hnu01) hP4
        (fun m' h0 hm' => hnuB1 m' h0 hm' hnu01) hleft
    · -- c-edge on the chord: contradiction with the cover at C0
      have hsgt : 1 < s := by
        rw [h1] at hdXP
        have h3 : (e : ℝ) * f < (f : ℝ) ^ 2 := by nlinarith
        nlinarith
      have Zc := rl_beta S x j 1 0 0 0 (by omega) (by omega) hi hnuB0 hleft
      simp only [Nat.cast_zero, zero_add] at Zc
      obtain ⟨φ, hφm, hφang, hφpush⟩ := Zc
      have hwcr : cross (wvec (e : ℝ) f x) (PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1) = kapG (e : ℝ) f := by
        have h := cross_wvec_step he0 hef x j 1 0 1
        rw [zero_add] at h
        have e1 : PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1 = (-1 : ℝ) • (PIR (e : ℝ) f x j 1 1 1 - PIR (e : ℝ) f x j 1 0 1) := by
          rw [neg_one_smul]; abel
        rw [e1, cross_smul_right', h]; ring
      obtain ⟨ε₀, hε₀, hεall⟩ := hφpush (PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1) (by rw [hwcr]; linarith)
      set ε' : ℝ := min ε₀ (s - 1) / 2 with hε'
      have hεpos : 0 < ε' := by rw [hε']; have := lt_min hε₀ (sub_pos.2 hsgt); linarith
      have hεa : ε' < ε₀ := by rw [hε']; have := min_le_left ε₀ (s - 1); linarith [lt_min hε₀ (sub_pos.2 hsgt)]
      have hεb : ε' < s - 1 := by rw [hε']; have := min_le_right ε₀ (s - 1); linarith [lt_min hε₀ (sub_pos.2 hsgt)]
      have hyint := hεall ε' hεpos hεa
      obtain ⟨k, m, jj, hkm, hkj, hmj, hk, hm, hj⟩ := hV
      have hy : PIR (e : ℝ) f x j 1 0 1 + ε' • (PIR (e : ℝ) f x j 1 0 1 - PIR (e : ℝ) f x j 1 1 1) ∈
          segment ℝ ((D.tile τ').pts k) ((D.tile τ').pts m) := by
        rw [hk, hm, hPs]
        refine ⟨1 - (1 + ε') / s, (1 + ε') / s, ?_, ?_, by ring, ?_⟩
        · have : (1 + ε') / s ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          linarith
        · positivity
        · have hs' : s ≠ 0 := by linarith
          ext i
          simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          field_simp
          ring
      exact seg_wall D.toDissection hkm hy φ hyint
  · -- flipped: rl_close with tau = 1, m = 0
    have hR' : R = PIR (e : ℝ) f x j 1 1 0 + 1 • dcvec (e : ℝ) f x := by
      rw [hRV, one_smul, ← hO1, ← ptVO_dc _ _ x 0 ((j : ℝ) + 1)]; abel
    have hleft' : ∃ (F : Fin N) (R' : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
        HasV D F (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R' ∧
        0 < cross (dcvec (e : ℝ) f x) (R' - PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
      have e10 : PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = PIR (e : ℝ) f x j 1 1 0 := PIR_congr (by norm_num) (by norm_num)
      refine ⟨τ, ptO (e : ℝ) f x 0 ((j : ℝ) + 1) + nuG (e : ℝ) f • (ptY (e : ℝ) f x 0 ((j : ℝ) + 1) - ptO (e : ℝ) f x 0 ((j : ℝ) + 1)), 1, Or.inr rfl, ?_, ?_⟩
      · rw [e10, ← hO1]
        refine hasV_congr hτ.rot.rot.swap rfl ?_ rfl
        rw [one_smul, ← ptVO_dc _ _ x 0 ((j : ℝ) + 1), ← hRV]; abel
      · rw [e10, ← hO1, ← ptVO_dc _ _ x 0 ((j : ℝ) + 1), add_sub_cancel_left, cross_smul_right']
        exact mul_pos hν0 (cross_V_Y_pos he0 hef x 0 ((j : ℝ) + 1))
    have hnuA : ∀ m' : ℕ, m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m') m')
          (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := hnuA0
    have hnuB : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 1 (((1 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    exact rl_close S x j 1 1 0 0 (by omega) (by omega) hi (by omega) hnuA hP4 hnuB hleft'

end rl12

#print axioms rl_one

end Erdos634.Draft.WGapStmt
