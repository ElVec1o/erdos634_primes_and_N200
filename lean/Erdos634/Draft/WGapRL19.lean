/-
Draft/WGapRL19.lean -- written 16 November 2026 (session 13).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, chord step of Lemma RL).
Not imported by any aggregate.  No sorry, no native_decide.
`chord_a_step`: the ABSTRACT one-edge chord step of Lemma RL (the branch of `rl_one` that produces `nu(0,1)`, in points `X, Y, Z, W0`):
a gamma tile `(X, Y, Z)` below the ray `X -> Y` (`|XY| = a`), an alpha tile at `X`, the half-disk cover `Xi` behind `X`, and a half-disk cover at `Y`
(from `rl_beta`) force the beta tile `(X, Y, W0)` above the ray (the `c`-edge on the ray would pass through `Y`, against the cover).
-/
import Erdos634.Draft.WGapRL18

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

section rl19

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem chord_a_step (S : SetupG D e f α β γ L ax ay) {X Y Z W0 d wv : Plane} {tG tN : Fin N}
    (hXY : X ≠ Y) (hG : HasV D tG X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (aG : (D.tile tG).localAngle X = γ) (aN : (D.tile tN).localAngle X = α)
    (hΞ : EdgeCoverS D X d (-1)) (hcr : 0 < cross d (Y - X))
    (hNray : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tN).pts j ≠ AffineMap.lineMap X Y s)
    (hZc : EdgeCoverS D Y wv 1) (hwcr : 0 < cross wv (Y - X))
    (hdXY : dist X Y = (e : ℝ) * f) (hd1 : dist W0 X = (f : ℝ) ^ 2)
    (hd2 : dist W0 Y = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (hW0 : cross (Y - X) (W0 - X) < 0) :
    ∃ τ : Fin N, HasV D τ X Y W0 := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  obtain ⟨τ', P, W, hV, ⟨s, hs0, hPs⟩, hW, hang, hPW, hsides⟩ :=
    rl_beta_fill_abs S hXY hG hZ aG aN hΞ hcr hNray
  have hdXP : dist X P = s * ((e : ℝ) * f) := by
    rw [hPs, dist_left_lineMap, Real.norm_of_nonneg hs0.le, hdXY]
  rcases hsides with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hs1 : s = 1 := by
      rw [h1] at hdXP
      have : (s - 1) * ((e : ℝ) * f) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hef0.ne'
    have hP : P = Y := by rw [hPs, hs1, AffineMap.lineMap_apply_one]
    have hWeq : W0 = W := by
      refine same_third hXY ?_ ?_ hW0 hW
      · rw [hd1, dist_comm W, h2]
      · rw [hd2, ← hP, dist_comm W, hPW]
    exact ⟨τ', hasV_congr hV rfl hP hWeq.symm⟩
  · exfalso
    have hsgt : 1 < s := by
      rw [h1] at hdXP
      have h3 : (e : ℝ) * f < (f : ℝ) ^ 2 := by nlinarith
      nlinarith
    obtain ⟨φ, hφm, hφang, hφpush⟩ := hZc
    obtain ⟨ε₀, hε₀, hεall⟩ := hφpush (Y - X) (by linarith)
    set ε' : ℝ := min ε₀ (s - 1) / 2 with hε'
    have hεpos : 0 < ε' := by rw [hε']; have := lt_min hε₀ (sub_pos.2 hsgt); linarith
    have hεa : ε' < ε₀ := by rw [hε']; have := min_le_left ε₀ (s - 1); linarith [lt_min hε₀ (sub_pos.2 hsgt)]
    have hyint := hεall ε' hεpos hεa
    obtain ⟨k, m, jj, hkm, hkj, hmj, hk, hm, hj⟩ := hV
    have hy : Y + ε' • (Y - X) ∈ segment ℝ ((D.tile τ').pts k) ((D.tile τ').pts m) := by
      rw [hk, hm, hPs]
      have hεb : ε' < s - 1 := by rw [hε']; have := min_le_right ε₀ (s - 1); linarith [lt_min hε₀ (sub_pos.2 hsgt)]
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

end rl19

#print axioms chord_a_step

end Erdos634.Draft.WGapStmt
