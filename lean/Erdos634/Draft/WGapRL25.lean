/-
Draft/WGapRL25.lean -- written 16 November 2026 (session 13).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2 for `i = 2`, `t = 0`: Lemma RL, three layers).
Not imported by any aggregate.  No sorry, no native_decide.
`rl_two` = Lemma RL at `i = 2`, `t = 0` (the climb's end for `lambda = 2` and the steps (2), (6) of Proposition B at `i = 2`): the lattice tiles at `A_2`, `A_1` (D(1,j), U(2,j), U(1,j+1), N^1, N^2, D(0,j+1), U(0,j+2), N^0), `Pi4` and the left tile at `A_0` give False.
Route: `rl_two_B12` (layer 0: `gamma(2,0)`, `gamma(1,0)`; flipped cases by `rl_close`), `chord2_first`/`chord2_second` (the two-edge chord gives `nu(1,1)`, `nu(0,1)`), `rl_fill_layer2` at `pi(1,1)`
(flipped: `rl_close` tau = 1, m = 1, mu0 = 1; else `gamma(1,1)`, one-edge chord by `chord_a_step`, `nu(0,2)`, `rl_close` tau = 0, m = 2).
-/
import Erdos634.Draft.WGapRL24

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

section rl20

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem rl_two (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 2 + 1 ≤ f - 1)
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
    False := by
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
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hν1 := nuG_lt_one he0 hef
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  obtain ⟨τ2, τ1, hΓ2, hΓ1⟩ := rl_two_B12 S x j hi hDa hUa hUb hNb hNa hDc hUc hNc hP4 hleft
  -- wrappers
  have hnuA0 : ∀ m' : ℕ, m' ≤ 0 → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') m')
        (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
    intro m' hm'
    obtain rfl : m' = 0 := by omega
    exact ⟨tNa, hasV_congr hNa' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num))⟩
  have hnuB0' : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j 2 (((0 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) m')
        (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
    intro m' _ hm'
    obtain rfl : m' = 0 := by omega
    exact ⟨tNc, hasV_congr hNc' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num))⟩
  have hZc0 := rl_beta S x j 2 0 0 0 (by omega) (by omega) hi hnuB0' hleft
  have e01 : PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) (((0 : ℕ) : ℝ) + 1) = PIR (e : ℝ) f x j 2 0 1 :=
    PIR_congr (by norm_num) (by norm_num)
  rw [e01] at hZc0
  have Aα := rl_alpha S x j 2 0 hi (by omega) hnuA0 hP4
  have hcast : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
  have hB0e : PIR (e : ℝ) f x j 2 2 1 = lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j + (((0 + 1 : ℕ) : ℝ)) •
      (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) := by
    rw [hcast]; exact PIR_on_L3 he0 hef x j 2 1 2 (by norm_num)
  have hΞ : EdgeCoverS D (PIR (e : ℝ) f x j 2 2 1)
      (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) (-1) := by
    rw [hB0e]; exact Aα
  obtain ⟨τν, hν11⟩ := chord2_first S x j hi hΓ2 hΓ1 hNa' hΞ hZc0
  obtain ⟨τμ, hν01⟩ := chord2_second S x j hi hΓ2 hΓ1 hNb' hν11 hZc0
  -- layer 1: the filler at `pi(1,1)`
  have hfill := rl_fill_layer2 S x j 2 1 0 (tG1 := tNb) (tG2 := τ1) (tG3 := τ2) (tN2 := τν) (tN := τμ)
    (hasV_congr hNb' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num)))
    (hasV_congr hΓ1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num)))
    (hasV_congr hΓ2 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num)))
    (hasV_congr hν11 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num)))
    (hasV_congr hν01 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
      (PIR_congr (by norm_num) (by norm_num)))
  have hnuA1 : ∀ m' : ℕ, m' ≤ 1 → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') m')
        (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
    intro m' hm'
    interval_cases m'
    · exact ⟨tNa, hasV_congr hNa' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    · exact ⟨τν, hasV_congr hν11 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
  rcases hfill with ⟨τ, R, hτ, hcrR, hR⟩ | ⟨τ, R, hτ, hcrR, hR⟩
  · -- `gamma(1,1)`: one-edge chord `[pi(1,2), pi(0,2)]`
    have hΓ11 : HasV D τ (PIR (e : ℝ) f x j 2 1 1) (PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 0 2) := by
      refine hasV_congr hτ (PIR_congr (by norm_num) (by norm_num)) ?_ ?_
      · have h := PIR_shift (e : ℝ) f x j 2 1 1 1
        rw [one_smul] at h
        rw [show ((0 : ℝ) + 1) = 1 by norm_num, ← h]
        exact PIR_congr rfl (by norm_num)
      · rw [hR]; exact PIR_congr (by norm_num) (by norm_num)
    have hnuB01 : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 1 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 2 (((0 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm'
      interval_cases m'
      · exact ⟨tNc, hasV_congr hNc' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      · exact ⟨τμ, hasV_congr hν01 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
    have hZc1 := rl_beta S x j 2 0 0 1 (by omega) (by omega) hi hnuB01 hleft
    have e02 : PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) (((1 : ℕ) : ℝ) + 1) = PIR (e : ℝ) f x j 2 0 2 :=
      PIR_congr (by norm_num) (by norm_num)
    rw [e02] at hZc1
    have Aα1 := rl_alpha S x j 2 1 hi (by omega) hnuA1 hP4
    have hB1e : PIR (e : ℝ) f x j 2 1 2 = lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j + (((1 + 1 : ℕ) : ℝ)) •
        (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) := by
      rw [show (((1 + 1 : ℕ) : ℝ)) = 2 by norm_num]; exact PIR_on_L3 he0 hef x j 2 2 1 (by norm_num)
    have hΞ1 : EdgeCoverS D (PIR (e : ℝ) f x j 2 1 2)
        (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) (-1) := by
      rw [hB1e]; exact Aα1
    -- distances and crosses
    have dXY1 : dist (PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 0 2) = (e : ℝ) * f := by
      have := dPIR_a he0 hef x j 2 0 2
      rwa [show (0 : ℝ) + 1 = 1 by norm_num] at this
    have d1' : dist (PIR (e : ℝ) f x j 2 0 3) (PIR (e : ℝ) f x j 2 1 2) = (f : ℝ) ^ 2 := by
      have := dPIR_c he0 hef x j 2 0 2
      rw [show (0 : ℝ) + 1 = 1 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num] at this
      rw [dist_comm]; exact this
    have d2' : dist (PIR (e : ℝ) f x j 2 0 3) (PIR (e : ℝ) f x j 2 0 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      have := dPIR_b he0 hef x j 2 0 2
      rw [show (2 : ℝ) + 1 = 3 by norm_num] at this
      rw [dist_comm]; exact this
    have dcz : dist (PIR (e : ℝ) f x j 2 0 2) (PIR (e : ℝ) f x j 2 1 1) = (f : ℝ) ^ 2 := by
      have := dPIR_c he0 hef x j 2 0 1
      rw [show (0 : ℝ) + 1 = 1 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num] at this
      rw [dist_comm]; exact this
    have dNa1 : dist (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 1) = (e : ℝ) * f := by
      have := dPIR_a he0 hef x j 2 1 1
      rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this
    have hXY1 : PIR (e : ℝ) f x j 2 1 2 ≠ PIR (e : ℝ) f x j 2 0 2 := by
      intro h
      have h1 := dXY1
      rw [h, dist_self] at h1
      linarith
    have hz1 : 0 < cross (PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 1 2) := by
      have : cross (PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 1 2) = kapG (e : ℝ) f := by
        rw [cross_PIRg he0 hef]; push_cast; ring
      rw [this]; exact hκ
    have hW1 : cross (PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 0 3 - PIR (e : ℝ) f x j 2 1 2) < 0 := by
      have : cross (PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 0 3 - PIR (e : ℝ) f x j 2 1 2) = -kapG (e : ℝ) f := by
        rw [cross_PIRg he0 hef]; push_cast; ring
      rw [this]; linarith
    have aG1 : (D.tile τ).localAngle (PIR (e : ℝ) f x j 2 1 2) = γ := (hΓ11.rot.anglesG S.tile S.hM).2.2 dcz
    have aN1 : (D.tile τν).localAngle (PIR (e : ℝ) f x j 2 1 2) = α := (hν11.rot.rot.anglesG S.tile S.hM).1 dNa1
    have hcr1 : 0 < cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2) := by
      have : cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
          (PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2) = kapG (e : ℝ) f := by
        rw [PIR_lp he0 hef, PIR_lp he0 hef, cross_lpG]; push_cast; ring
      rw [this]; exact hκ
    have hNray1 := known_off_ray hXY1 hν11.rot.rot
      (off_PIRg he0 hef x j 2 1 2 0 2 2 1 (by intro h; nlinarith [h]))
      (off_PIRg he0 hef x j 2 1 2 0 2 1 1 (by intro h; nlinarith [h]))
    have hwcr1 : 0 < cross (wvec (e : ℝ) f x) (PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2) := by
      have h := cross_wvec_step he0 hef x j 2 0 2
      rw [show (0 : ℝ) + 1 = 1 by norm_num] at h
      have e1 : PIR (e : ℝ) f x j 2 0 2 - PIR (e : ℝ) f x j 2 1 2 = (-1 : ℝ) • (PIR (e : ℝ) f x j 2 1 2 - PIR (e : ℝ) f x j 2 0 2) := by
        rw [neg_one_smul]; abel
      rw [e1, cross_smul_right', h]; linarith
    obtain ⟨τρ, hν02⟩ := chord_a_step S (X := PIR (e : ℝ) f x j 2 1 2) (Y := PIR (e : ℝ) f x j 2 0 2)
      (Z := PIR (e : ℝ) f x j 2 1 1) (W0 := PIR (e : ℝ) f x j 2 0 3) (wv := wvec (e : ℝ) f x) (tG := τ) (tN := τν)
      hXY1 hΓ11.rot hz1 aG1 aN1 hΞ1 hcr1 hNray1 hZc1 hwcr1 dXY1 d1' d2' hW1
    have hnuA2 : ∀ m' : ℕ, m' ≤ 2 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') m')
          (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
      intro m' hm'
      interval_cases m'
      · exact ⟨tNa, hasV_congr hNa' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      · exact ⟨τν, hasV_congr hν11 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      · exact ⟨τρ, hasV_congr hν02 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
    have hnuB2 : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 2 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 2 (((0 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm'
      interval_cases m'
      · exact ⟨tNc, hasV_congr hNc' (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      · exact ⟨τμ, hasV_congr hν01 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
      · exact ⟨τρ, hasV_congr hν02 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
          (PIR_congr (by norm_num) (by norm_num))⟩
    exact rl_close S x j 2 0 0 2 (by omega) (by omega) hi (by omega) hnuA2 hP4 hnuB2 hleft
  · -- flipped `Gamma_1` at `pi(1,1)`: `rl_close` with `tau = 1`, `m = 1`, `mu0 = 1`
    have hs := nu_s' he0 hef
    have hs2 := sMir_gt_two he0 hef
    have hcd : 0 < cross (dcvec (e : ℝ) f x) (PIR (e : ℝ) f x j 2 (1 - 1) (0 + 1 + 1) - PIR (e : ℝ) f x j 2 1 (0 + 1)) := by
      have key : cross (dcvec (e : ℝ) f x) (PIR (e : ℝ) f x j 2 (1 - 1) (0 + 1 + 1) - PIR (e : ℝ) f x j 2 1 (0 + 1)) =
          kapG (e : ℝ) f * (sMir (e : ℝ) f - 1) := by
        unfold dcvec
        rw [PIR_lp he0 hef, PIR_lp he0 hef, cross_lpG]
        push_cast
        linear_combination (kapG (e : ℝ) f) * hs
      rw [key]; exact mul_pos hκ (by linarith)
    have e11' : PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((1 : ℕ) : ℝ) = PIR (e : ℝ) f x j 2 1 (0 + 1) :=
      PIR_congr (by norm_num) (by norm_num)
    have hleft' : ∃ (F : Fin N) (R' : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
        HasV D F (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((1 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((1 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R' ∧
        0 < cross (dcvec (e : ℝ) f x) (R' - PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((1 : ℕ) : ℝ)) := by
      refine ⟨τ, PIR (e : ℝ) f x j 2 1 (0 + 1) + nuG (e : ℝ) f •
        (PIR (e : ℝ) f x j 2 (1 - 1) (0 + 1 + 1) - PIR (e : ℝ) f x j 2 1 (0 + 1)), 1, Or.inr rfl, ?_, ?_⟩
      · rw [e11']
        refine hasV_congr hτ.rot.rot.swap rfl ?_ rfl
        rw [one_smul]; exact hR
      · rw [e11', add_sub_cancel_left, cross_smul_right']
        exact mul_pos hν0 hcd
    have hnuB11 : ∀ m' : ℕ, 1 ≤ m' → m' ≤ 1 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 2 (((1 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j 2 ((1 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' h1 hm'
      obtain rfl : m' = 1 := by omega
      exact ⟨τν, hasV_congr hν11 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    exact rl_close S x j 2 1 1 1 (by omega) (by omega) hi (by omega) hnuA1 hP4 hnuB11 hleft'

end rl20

#print axioms rl_two

end Erdos634.Draft.WGapStmt
