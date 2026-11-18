/-
Draft/WGapRL9.lean -- written 16 November 2026 (session 11).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, the wedge fill at `A_{t'}` with the third vertex IDENTIFIED).
Not imported by any aggregate.  No sorry, no native_decide.
* `dich_conv2`: `dich_conv` with the identification `R = Y` (the `c`-edge on the ray: tile `(O, W, Y)`) resp. `R = V = O + dcvec` (the `b`-edge on the ray: tile `(O, P, V)`).
* `rl_gamma_fill2`: `rl_gamma_fill` (m = 0 wedge fill) with the identification, output in `ptO/ptV/ptY` form.
-/
import Erdos634.Draft.WGapRL8
import Erdos634.Draft.WGapRL5

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

section rl9

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem dich_conv2 (S : SetupG D e f α β γ L ax ay) (x a η0 : ℝ) {τ : Fin N} {P W : Plane}
    (hV : HasV D τ (ptO e f x a η0) P W)
    (hP : ∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap (ptO e f x a η0) (ptY e f x a η0) s)
    (hW : cross (ptY e f x a η0 - ptO e f x a η0) (W - ptO e f x a η0) < 0)
    (hPW : dist P W = (e : ℝ) * f)
    (hs : (dist (ptO e f x a η0) P = (f : ℝ) ^ 2 ∧ dist (ptO e f x a η0) W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
      (dist (ptO e f x a η0) P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (ptO e f x a η0) W = (f : ℝ) ^ 2)) :
    (∃ R, HasV D τ (ptO e f x a η0) (ptO e f x a η0 + nuG e f • (ptV e f x a η0 - ptO e f x a η0)) R ∧
        0 < cross (ptV e f x a η0 - ptO e f x a η0) (R - ptO e f x a η0) ∧ R = ptY e f x a η0) ∨
    (∃ R, HasV D τ (ptO e f x a η0) (ptO e f x a η0 + nuG e f • (ptY e f x a η0 - ptO e f x a η0)) R ∧
        cross (ptY e f x a η0 - ptO e f x a η0) (R - ptO e f x a η0) < 0 ∧ R = ptV e f x a η0) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hb' : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ 0 := hb.ne'
  have hf2' : (f : ℝ) ^ 2 ≠ 0 := hf2.ne'
  obtain ⟨s, hs0, hPs⟩ := hP
  obtain ⟨hid1, hid2, hid3⟩ := dich_ids he0 hef
  have hOY := dist_ptO_ptY he0 hef x a η0
  have hdOP : dist (ptO e f x a η0) P = s * (f : ℝ) ^ 2 := by
    rw [hPs, dist_left_lineMap, Real.norm_eq_abs, abs_of_pos hs0, hOY]
  have hκ := kapG_pos he0 hef
  have hnu := nuG_spec he0 hef
  have hnu0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos hb hf2
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `c` on the ray: `F_c`
    have hs1 : s = 1 := by
      rw [hdOP] at h1
      have : (s - 1) * (f : ℝ) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hf2.ne'
    have hPY : P = ptY e f x a η0 := by rw [hPs, hs1, AffineMap.lineMap_apply_one]
    have hW0 : ptO e f x a η0 + nuG (e : ℝ) f • (ptV e f x a η0 - ptO e f x a η0) =
        lpG (e : ℝ) f 1 x (a + 1 + nuG (e : ℝ) f * (a - (a + 1))) (η0 + nuG (e : ℝ) f * (η0 + sMir (e : ℝ) f - η0)) :=
      lp_add_smul _ _ _ _ _ _ _ _
    have hXP : ptO e f x a η0 ≠ P := by
      intro h; rw [← h, dist_self] at h1; exact hf2.ne h1
    have hz : cross (P - ptO e f x a η0) (ptO e f x a η0 + nuG (e : ℝ) f • (ptV e f x a η0 - ptO e f x a η0) - ptO e f x a η0) < 0 := by
      rw [hW0, hPY]
      unfold ptO ptY
      rw [cross_lpG]
      have : (a - nuG (e : ℝ) f - (a + 1)) * (η0 + nuG (e : ℝ) f * (η0 + sMir (e : ℝ) f - η0) - η0) -
          (η0 + 2 + nuG (e : ℝ) f - η0) * (a + 1 + nuG (e : ℝ) f * (a - (a + 1)) - (a + 1)) = -1 := by
        have h3 := hid3
        have hnr : nuG (e : ℝ) f * (f : ℝ) ^ 2 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [mul_comm]; exact hnu
        have key : nuG (e : ℝ) f * (2 + nuG (e : ℝ) f - sMir (e : ℝ) f * (1 + nuG (e : ℝ) f)) = -1 := by
          have : 2 + nuG (e : ℝ) f - sMir (e : ℝ) f * (1 + nuG (e : ℝ) f) = -((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
            linarith
          rw [this]
          unfold nuG
          field_simp
        linear_combination key
      rw [this]; linarith
    have hdW0O : dist (lpG (e : ℝ) f 1 x (a + 1 + nuG (e : ℝ) f * (a - (a + 1)))
        (η0 + nuG (e : ℝ) f * (η0 + sMir (e : ℝ) f - η0))) (ptO e f x a η0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      unfold ptO
      refine dist_lpG he0 hef hε hb.le ?_
      have e1 : a + 1 + nuG (e : ℝ) f * (a - (a + 1)) - (a + 1) = -nuG (e : ℝ) f := by ring
      have e2 : η0 + nuG (e : ℝ) f * (η0 + sMir (e : ℝ) f - η0) - η0 = nuG (e : ℝ) f * sMir (e : ℝ) f := by ring
      rw [e1, e2]
      unfold QfG
      have hsm := sMir_mul he0 hef
      have hnr : nuG (e : ℝ) f * (f : ℝ) ^ 2 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [mul_comm]; exact hnu
      linear_combination (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (nuG (e : ℝ) f) ^ 2 * sMir (e : ℝ) f) * hsm +
        (nuG (e : ℝ) f * (f : ℝ) ^ 2 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hnr
    have hdW0Y : dist (lpG (e : ℝ) f 1 x (a + 1 + nuG (e : ℝ) f * (a - (a + 1)))
        (η0 + nuG (e : ℝ) f * (η0 + sMir (e : ℝ) f - η0))) (ptY e f x a η0) = (e : ℝ) * f := by
      unfold ptY
      refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
      have e1 : a + 1 + nuG (e : ℝ) f * (a - (a + 1)) - (a - nuG (e : ℝ) f) = 1 := by ring
      have e2 : η0 + nuG (e : ℝ) f * (η0 + sMir (e : ℝ) f - η0) - (η0 + 2 + nuG (e : ℝ) f) = -1 := by
        have : η0 + nuG (e : ℝ) f * (η0 + sMir (e : ℝ) f - η0) - (η0 + 2 + nuG (e : ℝ) f) =
            nuG (e : ℝ) f * sMir (e : ℝ) f - 2 - nuG (e : ℝ) f := by ring
        rw [this]; exact hid2
      rw [e1, e2]
      unfold QfG
      ring
    have hW0eq : ptO e f x a η0 + nuG (e : ℝ) f • (ptV e f x a η0 - ptO e f x a η0) = W := by
      refine same_third hXP ?_ ?_ hz (by rw [hPY]; exact hW)
      · rw [hW0, hdW0O, dist_comm W, h2]
      · rw [hW0, hPY, hdW0Y, ← hPY, dist_comm W P, hPW]
    left
    refine ⟨P, ?_, ?_, hPY⟩
    · rw [hW0eq]; exact hV.swap.rot
    · rw [hPY]
      unfold ptV ptO ptY
      rw [cross_lpG]
      have : (a - (a + 1)) * (η0 + 2 + nuG (e : ℝ) f - η0) - (η0 + sMir (e : ℝ) f - η0) * (a - nuG (e : ℝ) f - (a + 1)) =
          (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
        rw [← hid3]; ring
      rw [this]
      exact mul_pos hκ (div_pos hf2 hb)
  · -- `b` on the ray: `F_b`
    have hsν : s = nuG (e : ℝ) f := by
      rw [hdOP] at h1
      have h' : s * (f : ℝ) ^ 2 = nuG (e : ℝ) f * (f : ℝ) ^ 2 := by rw [h1, mul_comm]; exact hnu.symm
      exact mul_right_cancel₀ hf2.ne' h'
    have hPν : P = ptO e f x a η0 + nuG (e : ℝ) f • (ptY e f x a η0 - ptO e f x a η0) := by
      rw [hPs, hsν, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    right
    refine ⟨W, by rw [← hPν]; exact hV, hW, ?_⟩
    -- identification `W = V = O + dcvec`
    have hPO : P - ptO e f x a η0 = nuG (e : ℝ) f • (ptY e f x a η0 - ptO e f x a η0) := by
      rw [hPν]; abel
    have hPlp : P = lpG (e : ℝ) f 1 x (a + 1 + nuG (e : ℝ) f * ((a - nuG (e : ℝ) f) - (a + 1)))
        (η0 + nuG (e : ℝ) f * ((η0 + 2 + nuG (e : ℝ) f) - η0)) := by
      rw [hPν]; unfold ptO ptY; exact lp_add_smul _ _ _ _ _ _ _ _
    have hXP : ptO e f x a η0 ≠ P := by
      intro h; rw [← h, dist_self] at h1; exact hb.ne h1
    have hdVO : dist (ptV e f x a η0) (ptO e f x a η0) = (f : ℝ) ^ 2 := by
      unfold ptV ptO
      refine dist_lpG he0 hef hε hf2.le ?_
      have e1 : a - (a + 1) = -1 := by ring
      have e2 : η0 + sMir (e : ℝ) f - η0 = sMir (e : ℝ) f := by ring
      rw [e1, e2]
      unfold QfG
      have hsm := sMir_mul he0 hef
      linear_combination (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
    have hdVP : dist (ptV e f x a η0) P = (e : ℝ) * f := by
      rw [hPlp]; unfold ptV
      refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
      unfold QfG nuG sMir
      field_simp
      ring
    have hzV : cross (P - ptO e f x a η0) (ptV e f x a η0 - ptO e f x a η0) < 0 := by
      rw [hPlp]; unfold ptV ptO
      rw [cross_lpG]
      have : (a + 1 + nuG (e : ℝ) f * ((a - nuG (e : ℝ) f) - (a + 1)) - (a + 1)) * (η0 + sMir (e : ℝ) f - η0) -
          (η0 + nuG (e : ℝ) f * ((η0 + 2 + nuG (e : ℝ) f) - η0) - η0) * (a - (a + 1)) = -1 := by
        unfold nuG sMir
        field_simp
        ring
      rw [this]
      linarith
    have hzW : cross (P - ptO e f x a η0) (W - ptO e f x a η0) < 0 := by
      rw [hPO, cross_smul_left']
      exact mul_neg_of_pos_of_neg hnu0 hW
    refine same_third hXP ?_ ?_ hzW hzV
    · rw [dist_comm W, h2]; exact hdVO.symm
    · rw [dist_comm W P, hPW]; exact hdVP.symm


set_option maxHeartbeats 4000000 in
theorem rl_gamma_fill2 (S : SetupG D e f α β γ L ax ay) (x a η : ℝ)
    {tUi tDL tUl tN tN2 : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1))
      (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f)))
    (hN2 : HasV D tN2 (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1))
      (lpG (e : ℝ) f 1 x (a + 1 - nuG (e : ℝ) f) (η + 2 + nuG (e : ℝ) f))) :
    (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f x a (η + 1)) (ptO e f x a (η + 1) + nuG (e : ℝ) f • (ptV e f x a (η + 1) - ptO e f x a (η + 1))) R ∧
        0 < cross (ptV e f x a (η + 1) - ptO e f x a (η + 1)) (R - ptO e f x a (η + 1)) ∧ R = ptY e f x a (η + 1)) ∨
    (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f x a (η + 1)) (ptO e f x a (η + 1) + nuG (e : ℝ) f • (ptY e f x a (η + 1) - ptO e f x a (η + 1))) R ∧
        cross (ptY e f x a (η + 1) - ptO e f x a (η + 1)) (R - ptO e f x a (η + 1)) < 0 ∧ R = ptV e f x a (η + 1)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA := S.hA
  have hnu0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos hb (by positivity)
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have aDL := (D_anglesG S hε hDL).2.2
  have aUl := (U_anglesG S hε hUl).2.2
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  have aN2 := (N_anglesG S hε hN2).2
  -- geometric distinctness
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) 1 p ≤ -lvG (e : ℝ) (f : ℝ) 1 x (a + (η + 1) + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) 1) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have nUlN2 : tN2 ≠ tUl := by
    obtain ⟨k, hk⟩ := hasV_third hN2
    refine HasV.ne_of_vertex hUl hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  have n12 : tDL ≠ tUl := ne_of_angle (by rw [aDL, aUl]; exact hαγ)
  have n13 : tDL ≠ tUi := ne_of_angle (by rw [aDL, aUi]; exact hαβ)
  have n14 : tDL ≠ tN := ne_of_angle (by rw [aDL, aN]; exact hαβ)
  have n15 : tDL ≠ tN2 := ne_of_angle (by rw [aDL, aN2]; exact hαγ)
  have n23 : tUl ≠ tUi := ne_of_angle (by rw [aUl, aUi]; exact hβγ.symm)
  have n24 : tUl ≠ tN := ne_of_angle (by rw [aUl, aN]; exact hβγ.symm)
  have n25 : tUl ≠ tN2 := nUlN2.symm
  have n34 : tUi ≠ tN := nUiN
  have n35 : tUi ≠ tN2 := ne_of_angle (by rw [aUi, aN2]; exact hβγ)
  have n45 : tN ≠ tN2 := ne_of_angle (by rw [aN, aN2]; exact hβγ)
  set O := lpG (e : ℝ) f 1 x (a + 1) (η + 1) with hOdef
  set Y := lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f) with hYdef
  have hOint : O ∈ interior D.target.carrier := by
    refine interior_of_four D n12 n14 n15 n24 n25 n45 ?_
    rw [aDL, aUl, aN, aN2]
    have hr := hA.hrel
    have hg := hA.hγdef
    have h1 := hA.hα
    have h2 := hA.hβ
    linarith
  set K : Finset (Fin N) := {tDL, tUl, tUi, tN, tN2} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle O = 2 * Real.pi - α := by
    rw [hKdef, sum_five _ n12 n13 n14 n15 n23 n24 n25 n34 n35 n45, aDL, aUl, aUi, aN, aN2]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have hΩ : ∑ i, (D.tile i).localAngle O = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq O
    rw [this, D.target.localAngle_interior hOint]
  have hXY : O ≠ Y := by
    intro h
    have := lpG_eta_eq he0 hef h
    linarith
  have hYt : Y ∈ D.target.carrier := hN.mem₃
  have hint := openSeg_interior D.toDissection hOint hYt
  have hP' : cross (Y - O) ((O - (Y - O)) - O) = 0 := by
    simp [cross]; ring
  have hXP : O ∈ openSegment ℝ (O - (Y - O)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle O < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [aDL]; exact hαπ
    · rw [aUl]; exact hγπ
    · rw [aUi]; exact hβπ
    · rw [aN]; exact hβπ
    · rw [aN2]; exact hγπ
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) hKsum hαπ hKlt
  have hZ : 0 < cross (Y - O) (lpG (e : ℝ) f 1 x a (η + 1 + 1) - O) := by
    rw [hOdef, hYdef, cross_lpG]
    have := kapG_pos he0 hef
    have e1 : (a - nuG (e : ℝ) f - (a + 1)) * (η + 1 + 1 - (η + 1)) -
        (η + 1 + 2 + nuG (e : ℝ) f - (η + 1)) * (a - (a + 1)) = 1 := by ring
    rw [e1]; linarith
  have hKray : ∀ k ∈ K, k ≠ tN → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap O Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    have off : ∀ ξ η' : ℝ, (a - nuG (e : ℝ) f - (a + 1)) * (η' - (η + 1)) -
        (η + 1 + 2 + nuG (e : ℝ) f - (η + 1)) * (ξ - (a + 1)) ≠ 0 →
        ∀ s : ℝ, 0 < s → lpG (e : ℝ) f 1 x ξ η' ≠ AffineMap.lineMap O Y s :=
      fun ξ η' h => off_lat he0 hef x (a + 1) (η + 1) (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f) ξ η' h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · refine known_off_ray hXY hDL.rot.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hUl.rot.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hUi.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · exact absurd rfl hkt
    · refine known_off_ray hXY hN2.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
  obtain ⟨τ, hτK, P, W, hV, hPray, hW, hang', hPW, hsides⟩ :=
    filler_alpha S hXY hN.swap.rot hZ hP' hXP hint hclamp hΩ K hKsum hKray
  have := dich_conv2 S x a (η + 1) hV hPray hW hPW hsides
  rcases this with ⟨R, h1, h2, h3⟩ | ⟨R, h1, h2, h3⟩
  · exact Or.inl ⟨τ, R, h1, h2, h3⟩
  · exact Or.inr ⟨τ, R, h1, h2, h3⟩


end rl9

end Erdos634.Draft.WGapStmt
