/-
Draft/WGapDich1.lean -- written 15 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.1, the filler `F` at `O = p(i+1,y0)`).
Not imported by any aggregate.  No sorry, no native_decide.
`dich_conv`: the conversion step of the ST dichotomy.  At `O = p(a+1, η0)` of the lattice with origin `x`, with `Y` = third vertex of `N`, `V_E` = the vertex of `E′` (mirror of
`U(a+1,η0)` in `l_{a+1}`): an `α`-tile `τ` with vertices `O, P, W` (`P` on the open ray `O → Y`, `W` strictly to the right of it, `|PW| = a`, `{|OP|,|OW|} = {c,b}`) is
 `F_c` (`c` on `[O,Y]`, `b` on `L_O`: the data of `St2`)  or  `F_b` (`b` on `[O,Y]`: the data of `Pi4`).
-/
import Erdos634.Draft.WGapSigA

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

/-- `O = p(a+1, η0)` -/
noncomputable def ptO (e f x a η0 : ℝ) : Plane := lpG e f 1 x (a + 1) η0
/-- `Y = p(a − ν, η0 + 2 + ν)`: third vertex of `N` -/
noncomputable def ptY (e f x a η0 : ℝ) : Plane := lpG e f 1 x (a - nuG e f) (η0 + 2 + nuG e f)
/-- `V_E = p(a, η0 + s)`, `s = (2f²−e²)/(f²−e²)`: the far vertex of `E′ = μ U(a+1,η0)` -/
noncomputable def ptV (e f x a η0 : ℝ) : Plane := lpG e f 1 x a (η0 + sMir e f)

theorem lp_add_smul (e f x ξ η ξ' η' t : ℝ) :
    lpG e f 1 x ξ η + t • (lpG e f 1 x ξ' η' - lpG e f 1 x ξ η) =
      lpG e f 1 x (ξ + t * (ξ' - ξ)) (η + t * (η' - η)) := by
  have h := lineMap_lpG e f 1 x ξ η ξ' η' t
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] at h
  exact h

section dich

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem dist_ptO_ptY {e f : ℝ} (he : 0 < e) (hef : e < f) (x a η0 : ℝ) : dist (ptO e f x a η0) (ptY e f x a η0) = f ^ 2 := by
  rw [dist_comm]; exact dist_N_VG he hef (by norm_num) a η0

theorem dich_ids {e f : ℝ} (he : 0 < e) (hef : e < f) :
    nuG e f * sMir e f = (2 * f ^ 2 - e ^ 2) / f ^ 2 ∧
    nuG e f * sMir e f - 2 - nuG e f = -1 ∧
    sMir e f * (1 + nuG e f) - (2 + nuG e f) = f ^ 2 / (f ^ 2 - e ^ 2) := by
  have hf : 0 < f := he.trans hef
  have hb : f ^ 2 - e ^ 2 ≠ 0 := by nlinarith
  have hf2 : f ^ 2 ≠ 0 := by positivity
  unfold sMir nuG
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- the conversion -/
theorem dich_conv (S : SetupG D e f α β γ L ax ay) (x a η0 : ℝ) {τ : Fin N} {P W : Plane}
    (hV : HasV D τ (ptO e f x a η0) P W)
    (hP : ∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap (ptO e f x a η0) (ptY e f x a η0) s)
    (hW : cross (ptY e f x a η0 - ptO e f x a η0) (W - ptO e f x a η0) < 0)
    (hPW : dist P W = (e : ℝ) * f)
    (hs : (dist (ptO e f x a η0) P = (f : ℝ) ^ 2 ∧ dist (ptO e f x a η0) W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
      (dist (ptO e f x a η0) P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (ptO e f x a η0) W = (f : ℝ) ^ 2)) :
    (∃ R, HasV D τ (ptO e f x a η0) (ptO e f x a η0 + nuG e f • (ptV e f x a η0 - ptO e f x a η0)) R ∧
        0 < cross (ptV e f x a η0 - ptO e f x a η0) (R - ptO e f x a η0)) ∨
    (∃ R, HasV D τ (ptO e f x a η0) (ptO e f x a η0 + nuG e f • (ptY e f x a η0 - ptO e f x a η0)) R ∧
        cross (ptY e f x a η0 - ptO e f x a η0) (R - ptO e f x a η0) < 0) := by
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
    refine ⟨P, ?_, ?_⟩
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
    exact ⟨W, by rw [← hPν]; exact hV, hW⟩

end dich

#print axioms dich_conv

end Erdos634.Draft.WGapStmt
