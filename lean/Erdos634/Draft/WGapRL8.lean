/-
Draft/WGapRL8.lean -- written 16 November 2026 (session 10).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.1, P8.2: Gamma_{t'} at the points pi(t', m'+1), m' >= 0).
Not imported by any aggregate.  No sorry, no native_decide.
Distances of the reflected lattice `PIR` (`dPIR_a`, `dPIR_b`, `dPIR_c`) and `rl_fill_layer`: at `O = pi(t, m'+1)` the five known tiles
`nu(t,m')` (alpha), `gamma(t,m')` (gamma), `gamma(t+1,m')` (beta) below and `nu(t,m'+1)` (gamma), `nu(t-1,m'+1)` (beta) above leave the wedge `(2alpha, 3alpha)`; the filler is
`gamma(t,m'+1)`-shaped (b-edge `[O, O + w]` on the ray `L^(t)`, `cross dcvec > 0`) or flipped (b-edge `[O, O + nu d]` on the ray `Y - O`, `d = pi(t-1,m'+2) - O`, `cross d < 0`).
-/
import Erdos634.Draft.WGapRL7
import Erdos634.Draft.WGapRL4

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

theorem nu_s' {e f : ℝ} (he : 0 < e) (hef : e < f) : nuG e f * sMir e f = 1 + nuG e f := by
  have := nu_s he hef
  linarith

theorem dPIR_a {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t m : ℝ) :
    dist (PIR e f x j i (t + 1) m) (PIR e f x j i t m) = e * f := by
  unfold PIR
  refine dist_lpG (ε := 1) (x := x) he hef (by norm_num) (mul_pos he (he.trans hef)).le ?_
  unfold QfG
  ring

theorem dPIR_b {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t m : ℝ) :
    dist (PIR e f x j i t m) (PIR e f x j i t (m + 1)) = f ^ 2 - e ^ 2 := by
  have h := PIR_shift e f x j i t m 1
  rw [dist_eq_norm, h, one_smul, sub_add_cancel_left, norm_neg, norm_wvec he hef x]

theorem dPIR_c {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t m : ℝ) :
    dist (PIR e f x j i (t + 1) m) (PIR e f x j i t (m + 1)) = f ^ 2 := by
  have hns := nu_s' he hef
  have hν := nuG_spec he hef
  unfold PIR
  refine dist_lpG (ε := 1) (x := x) he hef (by norm_num) (by have := he.trans hef; positivity) ?_
  have e1 : ((t + 1 - m * nuG e f) - (t - (m + 1) * nuG e f)) = 1 + nuG e f := by ring
  have e2 : (((j : ℝ) + i + 1 - (t + 1) + m * nuG e f * sMir e f) - ((j : ℝ) + i + 1 - t + (m + 1) * nuG e f * sMir e f))
      = -(2 + nuG e f) := by linear_combination (-1) * hns
  rw [e1, e2]
  unfold QfG
  linear_combination (e ^ 2 * (nuG e f + 2)) * hν

section rl8

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem rl_fill_layer (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i : ℕ) (t m' : ℝ)
    {tG1 tG2 tG3 tN2 tN : Fin N}
    (hG1 : HasV D tG1 (PIR (e : ℝ) f x j i (t + 1) m') (PIR (e : ℝ) f x j i t m') (PIR (e : ℝ) f x j i t (m' + 1)))
    (hG2 : HasV D tG2 (PIR (e : ℝ) f x j i t m') (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1)))
    (hG3 : HasV D tG3 (PIR (e : ℝ) f x j i (t + 1) m') (PIR (e : ℝ) f x j i (t + 1) (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1)))
    (hN2 : HasV D tN2 (PIR (e : ℝ) f x j i (t + 1) (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1 + 1)))
    (hN : HasV D tN (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1)) (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1))) :
    (∃ τ : Fin N, ∃ R, HasV D τ (PIR (e : ℝ) f x j i t (m' + 1)) (PIR (e : ℝ) f x j i t (m' + 1) + wvec (e : ℝ) f x) R ∧
        0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i t (m' + 1))) ∨
    (∃ τ : Fin N, ∃ R, HasV D τ (PIR (e : ℝ) f x j i t (m' + 1))
        (PIR (e : ℝ) f x j i t (m' + 1) + nuG (e : ℝ) f • (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1) - PIR (e : ℝ) f x j i t (m' + 1))) R ∧
        cross (PIR (e : ℝ) f x j i (t - 1) (m' + 1 + 1) - PIR (e : ℝ) f x j i t (m' + 1)) (R - PIR (e : ℝ) f x j i t (m' + 1)) < 0) := by
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
  rcases hconv with ⟨R, h1, h2⟩ | ⟨R, h1, h2⟩
  · left
    refine ⟨τ, R, ?_, ?_⟩
    · rw [hVp, ← wvec_eq, hOp] at h1; exact h1
    · rw [hVp, hOp] at h2; exact h2
  · right
    refine ⟨τ, R, ?_, ?_⟩
    · rw [hYp, hOp] at h1; exact h1
    · rw [hYp, hOp] at h2; exact h2

end rl8

end Erdos634.Draft.WGapStmt
