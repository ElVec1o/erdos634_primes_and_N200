/-
Draft/WGapSig17.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.3: `Z*` shows `β`, `Y` is interior to its `c`-edge).
Not imported by any aggregate.  No sorry, no native_decide.
* `lp_bary3`: barycentric combinations of lattice points.
* `zstar_shape`: a tile `(X, P′, W)` with `P′ = p'(1,y)`, `X = p(0,y+1)`, `W` on the right of `X → P′` and angle `β` at `X` has `W = p(−1, y+1+s)` (`s = sMir`): `|XW| = c`, `|P′W| = b`.
* `zstar_Y_push`: with `Y = p(−ν, y+2+ν)` (on the open `c`-edge `[X,W]`), `Y + ε (Y − O)` is interior to the tile `(X, P′, W)` for small `ε > 0`, `O = p(1,y)`.
-/
import Erdos634.Draft.WGapSig16

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

theorem lp_bary3 (e f x ξ1 η1 ξ2 η2 ξ3 η3 c1 c2 c3 : ℝ) (h : c1 + c2 + c3 = 1) :
    c1 • lpG e f 1 x ξ1 η1 + c2 • lpG e f 1 x ξ2 η2 + c3 • lpG e f 1 x ξ3 η3 =
      lpG e f 1 x (c1 * ξ1 + c2 * ξ2 + c3 * ξ3) (c1 * η1 + c2 * η2 + c3 * η3) := by
  have hc1 : c1 = 1 - c2 - c3 := by linarith
  subst hc1
  unfold lpG
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring

section sig17

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem zstar_shape (S : SetupG D e f α β γ L ax ay) (x y : ℝ) {tZ : Fin N} {W : Plane}
    (hZ : HasV D tZ (lpG (e : ℝ) f 1 x 0 (y + 1)) (lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1)) W)
    (hZc : cross (lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1) - lpG (e : ℝ) f 1 x 0 (y + 1))
      (W - lpG (e : ℝ) f 1 x 0 (y + 1)) < 0)
    (hβ : (D.tile tZ).localAngle (lpG (e : ℝ) f 1 x 0 (y + 1)) = β) :
    W = lpG (e : ℝ) f 1 x (-1) (y + 1 + sMir (e : ℝ) f * 1) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hsm := sMir_mul he0 hef
  have hκ := kapG_pos he0 hef
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hZ
  have hXP : dist (lpG (e : ℝ) f 1 x 0 (y + 1)) (lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1)) = (e : ℝ) * f := by
    refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
    have e1 : (0 : ℝ) - (-1) = 1 := by ring
    have e2 : y + 1 - (y + sMir (e : ℝ) f * 1) = 1 - sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
  have hβ' : (D.tile tZ).localAngle ((D.tile tZ).pts k) = β := by rw [hk]; exact hβ
  obtain ⟨-, hsd⟩ := sides_of_beta S tZ hkm hkj hmj hβ'
  rw [hk, hm, hj] at hsd
  have hXW : dist (lpG (e : ℝ) f 1 x 0 (y + 1)) W = (f : ℝ) ^ 2 := by
    rcases hsd with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exfalso
      rw [hXP] at h1
      exact S.tile.ac h1
  have hPW : dist (lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1)) W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    obtain ⟨hopp, -⟩ := sides_of_beta S tZ hkm hkj hmj hβ'
    rw [hm, hj] at hopp
    exact hopp
  have hXne : lpG (e : ℝ) f 1 x 0 (y + 1) ≠ lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1) := by
    intro h
    rw [h, dist_self] at hXP
    exact (mul_pos he0 hf0).ne hXP
  refine (same_third hXne ?_ ?_ ?_ hZc).symm
  · rw [dist_comm W (lpG (e : ℝ) f 1 x 0 (y + 1)), hXW, dist_comm]
    refine dist_lpG he0 hef hε hf2.le ?_
    have e2 : y + 1 - (y + 1 + sMir (e : ℝ) f * 1) = -sMir (e : ℝ) f := by ring
    rw [show (0 : ℝ) - (-1) = 1 by ring, e2]
    unfold QfG
    linear_combination (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * sMir (e : ℝ) f) * hsm
  · rw [dist_comm W (lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1)), hPW, dist_comm]
    refine dist_lpG he0 hef hε hb.le ?_
    rw [show (-1 : ℝ) - (-1) = 0 by ring, show y + sMir (e : ℝ) f * 1 - (y + 1 + sMir (e : ℝ) f * 1) = -1 by ring]
    unfold QfG
    ring
  · rw [cross_lpG]
    have : ((-1 : ℝ) - 0) * (y + 1 + sMir (e : ℝ) f * 1 - (y + 1)) - (y + sMir (e : ℝ) f * 1 - (y + 1)) * ((-1) - 0) = -1 := by ring
    rw [this]; linarith

end sig17

#print axioms zstar_shape

end Erdos634.Draft.WGapStmt
