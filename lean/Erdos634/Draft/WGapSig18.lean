/-
Draft/WGapSig18.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.3: `Y` is interior to the `c`-edge of `Z*`).
Not imported by any aggregate.  No sorry, no native_decide.
`zstar_Y_push`: `Y + ε (Y − O)` is interior to the tile `Z* = (X, P′, W)`, `W = p(−1, y+1+s)`, for small `ε > 0` (barycentric weights `(1−ν−ε(1+ν), ε f²/b, ν+ε(1+ν)−ε f²/b)`).
-/
import Erdos634.Draft.WGapSig17

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

section sig18

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem zstar_Y_push (S : SetupG D e f α β γ L ax ay) (x y : ℝ) {tZ : Fin N}
    (hZ : HasV D tZ (lpG (e : ℝ) f 1 x 0 (y + 1)) (lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1))
      (lpG (e : ℝ) f 1 x (-1) (y + 1 + sMir (e : ℝ) f * 1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ptY e f x 0 y + ε • (ptY e f x 0 y - ptO e f x 0 y) ∈ interior (D.tile tZ).carrier := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  obtain ⟨hid1, hid2, hid3⟩ := dich_ids he0 hef
  have hνpos : 0 < nuG (e : ℝ) f := by unfold nuG; exact div_pos hb hf2
  have hν1 : nuG (e : ℝ) f < 1 := by
    unfold nuG
    rw [div_lt_one hf2]
    nlinarith [pow_pos he0 2]
  set ν := nuG (e : ℝ) f with hνdef
  set s := sMir (e : ℝ) f with hsdef
  set r : ℝ := (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) with hrdef
  have hr : 0 < r := div_pos hf2 hb
  have hνs : s * ν = 1 + ν := by linarith
  have hc : s * (1 + ν) - (2 + ν) = r := hid3
  refine ⟨min ((1 - ν) / (1 + ν)) (ν / r), lt_min (div_pos (by linarith) (by linarith)) (div_pos hνpos hr), ?_⟩
  intro ε hε hεδ
  have hε1 : ε < (1 - ν) / (1 + ν) := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hε2 : ε < ν / r := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hε1' : ε * (1 + ν) < 1 - ν := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + ν)).1 hε1
    linarith
  have hε2' : ε * r < ν := by
    have := (lt_div_iff₀ hr).1 hε2
    linarith
  have hc1 : 0 < 1 - ν - ε * (1 + ν) := by linarith
  have hc2 : 0 < ε * r := mul_pos hε hr
  have hc3 : 0 < ν + ε * (1 + ν) - ε * r := by nlinarith
  have hbary := hasV_bary hZ hc1 hc2 hc3 (by ring)
  have hext : ptY e f x 0 y + ε • (ptY e f x 0 y - ptO e f x 0 y) =
      (1 - ν - ε * (1 + ν)) • lpG (e : ℝ) f 1 x 0 (y + 1) + (ε * r) • lpG (e : ℝ) f 1 x (-1) (y + s * 1) +
        (ν + ε * (1 + ν) - ε * r) • lpG (e : ℝ) f 1 x (-1) (y + 1 + s * 1) := by
    rw [lp_bary3 _ _ _ _ _ _ _ _ _ _ _ _ (by ring)]
    unfold ptY ptO
    rw [lp_extG]
    exact lpG_congr (by ring) (by linear_combination (-1 : ℝ) * hνs - ε * hc)
  rw [hext]
  exact hbary

end sig18

#print axioms zstar_Y_push

end Erdos634.Draft.WGapStmt
