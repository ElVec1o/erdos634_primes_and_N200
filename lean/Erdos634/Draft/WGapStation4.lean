/-
Draft/WGapStation4.lean -- written 16 November 2026 (session 17).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P10.3, the joint induction).
Not imported by any aggregate.  No sorry, no native_decide.
**`WGapRung.no_tiling_W_gap`, UNCONDITIONAL**: for coprime `2 <= e < f`, `f <= M e`, `M (f - e) < f`, `W_M(e,f)` is not tiled.  No hypothesis beyond these.
The joint induction `Sigma[m] ∧ BUpToP (m+1)` of PROOF 10.3 runs with `B` restricted to the pairs `(j, i)` with `j + i >= 1` (`BUpToP`): the corner `i = j = 0` is never used
(`sigma_succ` calls `B` at `i >= 1` only; Proposition B at `i` calls `B` at the level `j + lam >= 1` only (3a)), so `PropBStmt` at `i = j = 0` (F32) is not needed.
-/
import Erdos634.Draft.WGapStation3
import Erdos634.Draft.WGapSig23
import Erdos634.Draft.WGapMainRed

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

section station4

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **The joint induction** (PROOF 10.3) with `BUpToP`: `Sigma[m] ∧ B[m+1]` (pairs `j + i >= 1`) for every `m` -/
theorem sigma_B_joint_P (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) :
    ∀ m : ℕ, SigmaAll D e f m ∧ BUpToP D e f (m + 1) := by
  intro m
  induction m with
  | zero =>
    have hS0 : SigmaAll D e f 0 := fun c₀ J hA s y₀ hJ hy hsf hsm => by omega
    refine ⟨hS0, ?_⟩
    intro c₀ J hA j i hJ hi hij hj1
    have hi0 : i = 0 := by omega
    subst hi0
    exact prop_B_le_two S h2 hH4 hA hJ (by omega) hij hj1 hS0
  | succ m ih =>
    obtain ⟨hSg, hBm⟩ := ih
    have hSg' : SigmaAll D e f (m + 1) := by
      refine sigma_succ S h2 hH4 m hSg ?_
      intro c₀ J hA s y₀ i hJ hy hsf hn hi1 hi2 hi3
      intro ⟨hΩ, hP⟩
      exact hBm c₀ J hA y₀ i hJ (by omega) (by omega) (by omega) (omega_pib hi2 hΩ hP)
    refine ⟨hSg', ?_⟩
    intro c₀ J hA j i hJ hi hij hj1
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact hBm c₀ J hA j i hJ hlt hij hj1
    · have hie : i = m + 1 := by omega
      subst hie
      exact prop_B_of_station_P S h2 hH4 hA hJ hij hj1 hSg' (hBm.mono' (by omega))

end station4

/-- `Sigma[m]` for every `m`, unconditionally: the statement `SigmaAllStmt` of `WGapMainRed` -/
theorem sigmaAll_unconditional : SigmaAllStmt := by
  intro N D e f α β γ L ax ay S h2 hH4 he2 m
  exact (sigma_B_joint_P S h2 hH4 m).1

end Erdos634.Draft.WGapStmt

namespace Erdos634.Draft.WGapRung

/-- **THE W-GAP THEOREM, UNCONDITIONAL**: no tiling of `W_M(e,f)` for coprime `2 <= e < f` with `f <= M e` and `M (f - e) < f`. -/
theorem no_tiling_W_gap (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hMf : M * (f - e) < f) : ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  Erdos634.Draft.WGapStmt.no_tiling_W_gap_of_all Erdos634.Draft.WGapStmt.sigmaAll_unconditional hco he hef hfM hMf

#print axioms Erdos634.Draft.WGapStmt.sigma_B_joint_P
#print axioms Erdos634.Draft.WGapStmt.sigmaAll_unconditional
#print axioms no_tiling_W_gap

end Erdos634.Draft.WGapRung
