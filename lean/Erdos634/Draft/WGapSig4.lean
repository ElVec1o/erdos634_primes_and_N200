/-
Draft/WGapSig4.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b1), left end of `Λ`).
Not imported by any aggregate.  No sorry, no native_decide.
`row_left_clamp_E`: the LEFT clamp of the row `Λ = [p(0,y+1), p(q,y+1)]` from the mirror tile `E_y = μ U(0,y)`: the direction `e(π)` beyond `p(0,y+1)` is interior to `E_y`
(the direction `−q u` is `q (s−1) (p(0,y) − X) + q (p'(1,y) − X)`, `s = sMir > 2`).  This is `hclL` of `sigma_rowB`.
-/
import Erdos634.Draft.WGapSig3

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

section sig4

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem row_left_clamp_E (S : SetupG D e f α β γ L ax ay) {x y : ℝ} {q : ℕ} (hq : 0 < (q : ℝ)) {tE : Fin N}
    (hE : HasV D tE (mpG (e : ℝ) f 1 x 0 y) (mpG (e : ℝ) f 1 x 1 y) (mpG (e : ℝ) f 1 x 0 (y + 1))) :
    ∃ P' : Plane, GHG (f : ℝ) P' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)) ∧
      lpG (e : ℝ) (f : ℝ) 1 x 0 (y + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 x q (y + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 x 0 (y + 1)) (lpG (e : ℝ) (f : ℝ) 1 x q (y + 1)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hs2 := sMir_gt_two he0 hef
  have hX : mpG (e : ℝ) f 1 x 0 (y + 1) = lpG (e : ℝ) f 1 x 0 (y + 1) := mpG_eq_zero he0 hef x (y + 1)
  have hEx : HasV D tE (mpG (e : ℝ) f 1 x 0 (y + 1)) (mpG (e : ℝ) f 1 x 0 y) (mpG (e : ℝ) f 1 x 1 y) := hE.rot.rot
  have hθ1 : 0 < (q : ℝ) * (sMir (e : ℝ) f - 1) := mul_pos hq (by linarith)
  obtain ⟨ε₀, hε₀, hpush⟩ := hasV_push hEx hθ1 hq
  have hvec : (mpG (e : ℝ) f 1 x 0 (y + 1)) - lpG (e : ℝ) (f : ℝ) 1 x q (y + 1) =
      ((q : ℝ) * (sMir (e : ℝ) f - 1)) • (mpG (e : ℝ) f 1 x 0 y - mpG (e : ℝ) f 1 x 0 (y + 1)) +
        (q : ℝ) • (mpG (e : ℝ) f 1 x 1 y - mpG (e : ℝ) f 1 x 0 (y + 1)) := by
    rw [mpG_eq_zero he0 hef x y, mpG_eq_zero he0 hef x (y + 1), mpG_eq he0 hef x 1 y]
    unfold lpG
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  have hfA0 : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x 0 (y + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)) :=
    GHG_lp _ _ _ _ _ _
  have hfAq : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x q (y + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)) :=
    GHG_lp _ _ _ _ _ _
  rw [hX] at hpush hvec
  obtain ⟨P', hfP', hP', hsub⟩ := ext_point_of_push (T := D.tile tE) (GHG (f : ℝ)) hfA0 hfAq
    (by obtain ⟨k0, -, -, -, -, -, hk0, -, -⟩ := hEx; have := Erdos634.RouteOneCrossing.pts_mem_carrier (D.tile tE) k0; rw [hk0] at this; rwa [hX] at this)
    ⟨ε₀, hε₀, fun ε hε hε1 => by rw [hvec]; exact hpush ε hε hε1⟩
  exact ⟨P', hfP', hP', fun ed _ => not_straddles_of_interior D.toDissection hsub ed.1 ed.2⟩

end sig4

#print axioms row_left_clamp_E

end Erdos634.Draft.WGapStmt
