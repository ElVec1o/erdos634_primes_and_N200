/-
Draft/WGapRL22.lean -- written 16 November 2026 (session 13).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, the wedge fill of Lemma RL at a layer point).
Not imported by any aggregate.  No sorry, no native_decide.
`rl_fill_layer2` = `rl_fill_layer` (WGapRL8) WITH the identification of the third vertex (via `dich_conv2`): the filler is `gamma(t,m'+1)` (`R = pi(t-1,m'+2)`) or the flipped tile (`R = O + dcvec`).
-/
import Erdos634.Draft.WGapRL21

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

section rl22

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem rl_fill_layer2 (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i : ℕ) (t m' : ℝ)
    {tG1 tG2 tG3 tN2 tN : Fin N}
    (hG1 : HasV D tG1 (PIR (e : ℝ) f x j i (t + 1) m') (PIR (e : ℝ) f x j i t m') (PIR (e : ℝ) f x j i t (m' + 1)))
    (hG2 : HasV D tG2 (PIR (e : ℝ) f x j i t m') (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1)))
    (hG3 : HasV D tG3 (PIR (e : ℝ) f x j i (t + 1) m') (PIR (e : ℝ) f x j i (t + 1) (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1)))
    (hN2 : HasV D tN2 (PIR (e : ℝ) f x j i (t + 1) (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1 + 1)))
    (hN : HasV D tN (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1))) :
    (∃ τ : Fin N, ∃ R, HasV D τ (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1) + wvec (e : ℝ) f x) R ∧
        0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i t (m' + 1)) ∧ R = PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1)) ∨
    (∃ τ : Fin N, ∃ R, HasV D τ (PIR (e : ℝ) f x j i t (m' + 1))
        (PIR (e : ℝ) f x j i t (m' + 1) + nuG (e : ℝ) f • (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1) - PIR (e : ℝ) f x j i t (m' + 1))) R ∧
        cross (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1) - PIR (e : ℝ) f x j i t (m' + 1)) (R - PIR (e : ℝ) f x j i t (m' + 1)) < 0 ∧
        R = PIR (e : ℝ) f x j i t (m' + 1) + dcvec (e : ℝ) f x) := by
  have he0 := S.e0
  have hef := S.hef'
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hns := nu_s' he0 hef
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hκ := kapG_pos he0 hef
  -- distances
  have dab := dPIR_a he0 hef x j i
  have dbb := dPIR_b he0 hef x j i
  have dcc := dPIR_c he0 hef x j i
  have hc2 : dist (PIR (e : ℝ) f x j i t m') (PIR (e : ℝ) f x j i (t - 1) (m' + 1)) = (f : ℝ) ^ 2 := by
    have := dcc (t - 1) m'
    rw [sub_add_cancel] at this
    exact this
  have hc3 : dist (PIR (e : ℝ) f x j i t (m' + 1 + 1)) (PIR (e : ℝ) f x j i (t + 1) (m' + 1)) = (f : ℝ) ^ 2 := by
    rw [dist_comm]; exact dcc t (m' + 1)
  -- angles at O = pi(t, m'+1)
  have aG1 : (D.tile tG1).localAngle (PIR (e : ℝ) f x j i t (m' + 1)) = α :=
    (hG1.rot.rot.anglesG S.tile S.hM).1 (by rw [dab t m'])
  have aG2 : (D.tile tG2).localAngle (PIR (e : ℝ) f x j i t (m' + 1)) = γ :=
    (hG2.rot.anglesG S.tile S.hM).2.2 (by rw [dist_comm, hc2])
  have aG3 : (D.tile tG3).localAngle (PIR (e : ℝ) f x j i t (m' + 1)) = β :=
    (hG3.rot.rot.anglesG S.tile S.hM).2.1 (by rw [dbb (t + 1) m'])
  have aN2 : (D.tile tN2).localAngle (PIR (e : ℝ) f x j i t (m' + 1)) = γ :=
    (hN2.rot.anglesG S.tile S.hM).2.2 (by rw [hc3])
  have aN : (D.tile tN).localAngle (PIR (e : ℝ) f x j i t (m' + 1)) = β :=
    (hN.anglesG S.tile S.hM).2.1 (by rw [dbb (t - 1) (m' + 1)])
  -- off-ray facts
  have offPIR : ∀ (t' m'' : ℝ), t' + m'' ≠ t + (m' + 1) → ∀ s : ℝ, 0 < s →
      PIR (e : ℝ) f x j i t' m'' ≠ AffineMap.lineMap (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1)) s := by
    intro t' m'' hne
    unfold PIR
    refine off_lat he0 hef x _ _ _ _ _ _ ?_
    intro h0
    apply hne
    have : (-1 : ℝ) * (t' + m'' - (t + (m' + 1))) = 0 := by
      linear_combination h0 + (t' - t + m'' - (m' + 1)) * hns
    linarith
  have negray : ∀ s : ℝ, 0 < s →
      PIR (e : ℝ) f x j i (t + 1) m' ≠ AffineMap.lineMap (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1)) s := by
    intro s hs h
    unfold PIR at h
    rw [lineMap_lpG] at h
    have := lpG_xi_eq he0 hef hε h
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + nuG (e : ℝ) f) (by linarith : (0 : ℝ) < 1 + s)]
  -- the geometry of the fill
  have hN' : HasV D tN (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1)) :=
    hN.swap.rot
  have hZ : 0 < cross (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1) - PIR (e : ℝ) f x j i t (m' + 1))
      (PIR (e : ℝ) f x j i (t - 1) (m' + 1) - PIR (e : ℝ) f x j i t (m' + 1)) := by
    unfold PIR
    rw [cross_lpG]
    have : kapG (e : ℝ) f * (((t - 1 - (m' + 1 + 1) * nuG (e : ℝ) f) - (t - (m' + 1) * nuG (e : ℝ) f)) *
        (((j : ℝ) + i + 1 - (t - 1) + (m' + 1) * nuG (e : ℝ) f * sMir (e : ℝ) f) - ((j : ℝ) + i + 1 - t + (m' + 1) * nuG (e : ℝ) f * sMir (e : ℝ) f))
        - (((j : ℝ) + i + 1 - (t - 1) + (m' + 1 + 1) * nuG (e : ℝ) f * sMir (e : ℝ) f) - ((j : ℝ) + i + 1 - t + (m' + 1) * nuG (e : ℝ) f * sMir (e : ℝ) f)) *
        ((t - 1 - (m' + 1) * nuG (e : ℝ) f) - (t - (m' + 1) * nuG (e : ℝ) f))) = kapG (e : ℝ) f := by
      linear_combination (kapG (e : ℝ) f) * hns
    linarith [this, hκ]
  have hXY : PIR (e : ℝ) f x j i t (m' + 1) ≠ PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1) := by
    intro h
    rw [← h] at hZ
    simp [cross] at hZ
  have nG2N2 : tG2 ≠ tN2 := by
    obtain ⟨k, hk⟩ := hasV_third hG2
    refine (HasV.ne_of_vertex hN2 hk ?_ ?_ ?_)
    all_goals
      intro h
      unfold PIR at h
      have := lpG_xi_eq he0 hef hε h
      nlinarith
  have nG3N : tG3 ≠ tN := by
    obtain ⟨k, hk⟩ := hasV_third hN
    refine (HasV.ne_of_vertex hG3 hk ?_ ?_ ?_).symm
    all_goals
      intro h
      unfold PIR at h
      have := lpG_xi_eq he0 hef hε h
      nlinarith
  obtain ⟨τ, P, W, hV, hPray, hW, hang, hPW, hsides⟩ :=
    rl_fill_gen S aG1 aG2 aG3 aN2 aN nG2N2 nG3N hN' hZ hXY
      (known_off_ray hXY hG1.rot.rot (negray) (offPIR _ _ (by linarith))
        |> fun h j s hs => h j s hs)
      (known_off_ray hXY hG2.rot (offPIR _ _ (by linarith)) (offPIR _ _ (by linarith)))
      (known_off_ray hXY hG3.rot.rot (negray) (offPIR _ _ (by linarith)))
      (known_off_ray hXY hN2.rot (offPIR _ _ (by linarith)) (offPIR _ _ (by linarith)))
  -- conversion to the form of `dich_conv`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = t - (m' + 1) * nuG (e : ℝ) f - 1 := ⟨_, rfl⟩
  obtain ⟨η0, hη0⟩ : ∃ η0 : ℝ, η0 = (j : ℝ) + i + 1 - t + (m' + 1) * nuG (e : ℝ) f * sMir (e : ℝ) f := ⟨_, rfl⟩
  have hOp : ptO (e : ℝ) f x a η0 = PIR (e : ℝ) f x j i t (m' + 1) := by
    unfold ptO PIR
    exact lpG_congr (by rw [ha]; ring) (by rw [hη0])
  have hYp : ptY (e : ℝ) f x a η0 = PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1) := by
    unfold ptY PIR
    exact lpG_congr (by rw [ha]; ring) (by rw [hη0]; linear_combination (-1) * hns)
  have hVp : ptV (e : ℝ) f x a η0 - ptO (e : ℝ) f x a η0 = dcvec (e : ℝ) f x := by
    unfold ptV ptO dcvec
    have h1 : lpG (e : ℝ) f 1 x a (η0 + sMir (e : ℝ) f) = lpG (e : ℝ) f 1 x ((a + 1) + (-1)) (η0 + sMir (e : ℝ) f) :=
      lpG_congr (by ring) rfl
    rw [h1, lpG_add]
    abel
  have hconv := dich_conv S x a η0 (τ := τ) (P := P) (W := W) (by rw [hOp]; exact hV)
    (by rw [hOp, hYp]; exact hPray) (by rw [hOp, hYp]; exact hW) hPW (by rw [hOp]; exact hsides)
  have hconv := dich_conv2 S x a η0 (τ := τ) (P := P) (W := W) (by rw [hOp]; exact hV)
    (by rw [hOp, hYp]; exact hPray) (by rw [hOp, hYp]; exact hW) hPW (by rw [hOp]; exact hsides)
  have hVO : ptV (e : ℝ) f x a η0 = PIR (e : ℝ) f x j i t (m' + 1) + dcvec (e : ℝ) f x := by
    rw [← hOp, ← hVp]; abel
  rcases hconv with ⟨R, h1, h2, h3⟩ | ⟨R, h1, h2, h3⟩
  · left
    refine ⟨τ, R, ?_, ?_, ?_⟩
    · rw [hVp, ← wvec_eq, hOp] at h1; exact h1
    · rw [hVp, hOp] at h2; exact h2
    · rw [h3, hYp]
  · right
    refine ⟨τ, R, ?_, ?_, ?_⟩
    · rw [hYp, hOp] at h1; exact h1
    · rw [hYp, hOp] at h2; exact h2
    · rw [h3, hVO]

end rl22

#print axioms rl_fill_layer2

end Erdos634.Draft.WGapStmt
