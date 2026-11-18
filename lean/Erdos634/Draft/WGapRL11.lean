/-
Draft/WGapRL11.lean -- written 16 November 2026 (session 11).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2 for `i = 1`, `t = 0`).
Not imported by any aggregate.  No sorry, no native_decide.
Helpers for `RL(i = 1, t = 0)` (module WGapRL12): `PIR_lp` (PIR in lattice form), `hasV_PIR`, `QfG_nu`, `dist_lp_nu`, `cross_V_Y_pos`.
-/
import Erdos634.Draft.WGapRL10

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

theorem PIR_lp {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t m : ℝ) :
    PIR e f x j i t m = lpG e f 1 x (t - m * nuG e f) ((j : ℝ) + i + 1 - t + m * (1 + nuG e f)) := by
  unfold PIR
  have := nu_s' he hef
  exact lpG_congr rfl (by linear_combination m * this)

theorem hasV_PIR {e f : ℝ} (he : 0 < e) (hef : e < f) {x : ℝ} {j i : ℕ} {T : Fin N}
    {ξ1 η1 ξ2 η2 ξ3 η3 t1 m1 t2 m2 t3 m3 : ℝ}
    (h : HasV D T (lpG e f 1 x ξ1 η1) (lpG e f 1 x ξ2 η2) (lpG e f 1 x ξ3 η3))
    (a1 : ξ1 = t1 - m1 * nuG e f) (b1 : η1 = (j : ℝ) + i + 1 - t1 + m1 * (1 + nuG e f))
    (a2 : ξ2 = t2 - m2 * nuG e f) (b2 : η2 = (j : ℝ) + i + 1 - t2 + m2 * (1 + nuG e f))
    (a3 : ξ3 = t3 - m3 * nuG e f) (b3 : η3 = (j : ℝ) + i + 1 - t3 + m3 * (1 + nuG e f)) :
    HasV D T (PIR e f x j i t1 m1) (PIR e f x j i t2 m2) (PIR e f x j i t3 m3) := by
  rw [PIR_lp he hef, PIR_lp he hef, PIR_lp he hef]
  exact hasV_congr h (lpG_congr a1 b1) (lpG_congr a2 b2) (lpG_congr a3 b3)

theorem QfG_nu {e f : ℝ} (he : 0 < e) (hef : e < f) (dξ dη : ℝ) :
    QfG e f dξ dη = f ^ 4 * (dξ ^ 2 + (1 + nuG e f) * nuG e f * (dξ * dη) + nuG e f ^ 2 * dη ^ 2) := by
  have hν := nuG_spec he hef
  have he2 : e ^ 2 = f ^ 2 - f ^ 2 * nuG e f := by linarith
  unfold QfG
  rw [he2]
  ring

theorem dist_lp_nu {e f : ℝ} (he : 0 < e) (hef : e < f) {x ξ η ξ' η' d : ℝ} (hd0 : 0 ≤ d)
    (h : f ^ 4 * ((ξ - ξ') ^ 2 + (1 + nuG e f) * nuG e f * ((ξ - ξ') * (η - η')) + nuG e f ^ 2 * (η - η') ^ 2) = d ^ 2) :
    dist (lpG e f 1 x ξ η) (lpG e f 1 x ξ' η') = d :=
  dist_lpG he hef (by norm_num) hd0 (by rw [QfG_nu he hef]; exact h)

theorem cross_V_Y_pos {e f : ℝ} (he : 0 < e) (hef : e < f) (x a η0 : ℝ) :
    0 < cross (ptV e f x a η0 - ptO e f x a η0) (ptY e f x a η0 - ptO e f x a η0) := by
  have hf0 : (0 : ℝ) < f := he.trans hef
  have hf2 : (0 : ℝ) < f ^ 2 := by positivity
  have hb : (0 : ℝ) < f ^ 2 - e ^ 2 := by nlinarith
  obtain ⟨hid1, hid2, hid3⟩ := dich_ids he hef
  have hκ := kapG_pos he hef
  unfold ptV ptO ptY
  rw [cross_lpG]
  have : (a - (a + 1)) * (η0 + 2 + nuG e f - η0) - (η0 + sMir e f - η0) * (a - nuG e f - (a + 1)) =
      f ^ 2 / (f ^ 2 - e ^ 2) := by
    rw [← hid3]; ring
  rw [this]
  exact mul_pos hκ (div_pos hf2 hb)

#print axioms hasV_PIR
#print axioms dist_lp_nu
#print axioms cross_V_Y_pos

end Erdos634.Draft.WGapStmt
