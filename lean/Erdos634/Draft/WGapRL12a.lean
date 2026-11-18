/-
Draft/WGapRL12a.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2 for `i = 1`).
Not imported by any aggregate.  No sorry, no native_decide.
Lattice helpers for `rl_one` (module WGapRL12): `PIR_congr`, `PIR_lp1` (PIR at `i = 1` in lattice form), `off_PIR`, `cross_PIR`, `cross_aux`, the specific distances/crosses of the points
`O1 = PIR 1 0`, `B0 = PIR 1 1`, `C0 = PIR 0 1`, `pi02 = PIR 0 2`.
-/
import Erdos634.Draft.WGapRL11

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

theorem PIR_congr {e f x : ℝ} {j i : ℕ} {t1 t2 m1 m2 : ℝ} (ht : t1 = t2) (hm : m1 = m2) :
    PIR e f x j i t1 m1 = PIR e f x j i t2 m2 := by rw [ht, hm]

theorem PIR_lp1 {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) (t m : ℝ) :
    PIR e f x j 1 t m = lpG e f 1 x (t - m * nuG e f) ((j : ℝ) + 2 - t + m * (1 + nuG e f)) := by
  rw [PIR_lp he hef]
  exact lpG_congr rfl (by push_cast; ring)

theorem off_PIR {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) (t0 m0 t1 m1 t m : ℝ)
    (h : ((t1 - m1 * nuG e f) - (t0 - m0 * nuG e f)) *
        (((j : ℝ) + 2 - t + m * (1 + nuG e f)) - ((j : ℝ) + 2 - t0 + m0 * (1 + nuG e f))) -
      (((j : ℝ) + 2 - t1 + m1 * (1 + nuG e f)) - ((j : ℝ) + 2 - t0 + m0 * (1 + nuG e f))) *
        ((t - m * nuG e f) - (t0 - m0 * nuG e f)) ≠ 0) :
    ∀ s : ℝ, 0 < s → PIR e f x j 1 t m ≠ AffineMap.lineMap (PIR e f x j 1 t0 m0) (PIR e f x j 1 t1 m1) s := by
  rw [PIR_lp1 he hef, PIR_lp1 he hef, PIR_lp1 he hef]
  exact off_lat he hef x _ _ _ _ _ _ h

theorem cross_PIR {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) (t1 m1 t2 m2 t3 m3 t4 m4 : ℝ) :
    cross (PIR e f x j 1 t1 m1 - PIR e f x j 1 t2 m2) (PIR e f x j 1 t3 m3 - PIR e f x j 1 t4 m4) =
      kapG e f * (((t1 - m1 * nuG e f) - (t2 - m2 * nuG e f)) *
        (((j : ℝ) + 2 - t3 + m3 * (1 + nuG e f)) - ((j : ℝ) + 2 - t4 + m4 * (1 + nuG e f))) -
        (((j : ℝ) + 2 - t1 + m1 * (1 + nuG e f)) - ((j : ℝ) + 2 - t2 + m2 * (1 + nuG e f))) *
          ((t3 - m3 * nuG e f) - (t4 - m4 * nuG e f))) := by
  rw [PIR_lp1 he hef, PIR_lp1 he hef, PIR_lp1 he hef, PIR_lp1 he hef, cross_lpG]

theorem cross_aux (O C dc : Plane) (ν : ℝ) :
    cross (C - (O + ν • dc)) (O - (O + ν • dc)) = ν * cross dc (C - O) := by
  simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem cross_smul_right' (c : ℝ) (v w : Plane) : cross v (c • w) = c * cross v w := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

/-- `|B0 C0| = a` -/
theorem rl12_dBC {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) :
    dist (PIR e f x j 1 1 1) (PIR e f x j 1 0 1) = e * f := by
  have := dPIR_a he hef x j 1 0 1
  rwa [zero_add] at this

/-- `|pi02 B0| = c` -/
theorem rl12_dZB {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) :
    dist (PIR e f x j 1 0 (1 + 1)) (PIR e f x j 1 1 1) = f ^ 2 := by
  have := dPIR_c he hef x j 1 0 1
  rw [zero_add] at this
  rw [dist_comm]; exact this

/-- `|C0 pi02| = b` -/
theorem rl12_dCZ {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) :
    dist (PIR e f x j 1 0 1) (PIR e f x j 1 0 (1 + 1)) = f ^ 2 - e ^ 2 :=
  dPIR_b he hef x j 1 0 1

/-- `|C0 O1| = c` -/
theorem rl12_dCO {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) :
    dist (PIR e f x j 1 0 1) (PIR e f x j 1 1 0) = f ^ 2 := by
  have := dPIR_c he hef x j 1 0 0
  rw [zero_add] at this
  rw [dist_comm]; exact this

/-- `|p(2,j) O1| = a` (alpha at B0 of `N^1`) -/
theorem rl12_dNa {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) :
    dist (PIR e f x j 1 (1 + 1) 0) (PIR e f x j 1 1 0) = e * f :=
  dPIR_a he hef x j 1 1 0

theorem rl12_cross_Z {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ) :
    cross (PIR e f x j 1 0 1 - PIR e f x j 1 1 1) (PIR e f x j 1 0 (1 + 1) - PIR e f x j 1 1 1) < 0 := by
  have hns := nu_s' he hef
  have hκ := kapG_pos he hef
  rw [cross_PIR he hef]
  have : ((0 - 1 * nuG e f) - (1 - 1 * nuG e f)) *
        (((j : ℝ) + 2 - 0 + (1 + 1) * (1 + nuG e f)) - ((j : ℝ) + 2 - 1 + 1 * (1 + nuG e f))) -
        (((j : ℝ) + 2 - 0 + 1 * (1 + nuG e f)) - ((j : ℝ) + 2 - 1 + 1 * (1 + nuG e f))) *
          ((0 - (1 + 1) * nuG e f) - (1 - 1 * nuG e f)) = -1 := by ring
  rw [this]; linarith

#print axioms rl12_cross_Z
#print axioms off_PIR
#print axioms rl12_dZB
#print axioms rl12_dCO

end Erdos634.Draft.WGapStmt
