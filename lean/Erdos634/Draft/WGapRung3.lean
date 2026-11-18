/-
Draft/WGapRung3.lean -- 16 November 2026 (work item LEAN_WGAP_2026-11-15, session 12).  UNAUDITED beyond internal checks.  Not imported by any aggregate.
**Rung 3, UNCONDITIONAL**: `no_tiling_W_rung3`: no tiling of `W_M(e,f)` when `M (f - e) ≤ e + 3` (and `M (f-e) < f`, `f ≤ M e`, `2 ≤ e`, `gcd (e,f) = 1`).
`Sigma[e+3]` = `sigma_succ` at `m = e+2` (from `st_d`); its exit hypothesis (`B` at `i = 1`) is `prop_B_one` (WGapRL18: Proposition B at `i = 1`, from `Sigma[1]`).
Credit: Beeson-Rosu (framework), the W-gap formalization work item (all of WGap*).
-/
import Erdos634.Draft.WGapRL18
import Erdos634.Draft.WGapRung1
import Erdos634.Draft.WGapSig23

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapRung

open Erdos634.Draft.WGapStmt
open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Erdos634.Draft.FDBBaseBetaE1 Set

/-- **`Sigma[e+3]` unconditionally** -/
theorem sigmaAllLe_rung3 : SigmaAllLeStmt (fun e => e + 3) := by
  intro N D e f α β γ L ax ay S h2 hH4 he2 m hm
  have hm' : m ≤ e + 3 := hm
  rcases Nat.lt_or_ge m (e + 3) with hlt | hge
  · exact st_d S h2 hH4 m (by omega)
  · have hme : m = e + 3 := by omega
    subst hme
    refine sigma_succ S h2 hH4 (e + 2) (st_d S h2 hH4 (e + 2) le_rfl) ?_
    intro c₀ J hA s y₀ i hJ hy hsf hn hi1 hi2 hi3 ⟨hΩ, hP⟩
    have hi : i = 1 := by omega
    subst hi
    have hPB := omega_pib hi2 hΩ hP
    exact prop_B_one S h2 hH4 hA hJ (by omega) (st_d S h2 hH4 1 (by omega)) hPB

/-- **Theorem R3 (rung `e+3`), UNCONDITIONAL**: no tiling of `W_M(e,f)` when `M (f - e) ≤ e + 3` (and `M (f-e) < f`). -/
theorem no_tiling_W_rung3 (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hMf : M * (f - e) < f) (hk : M * (f - e) ≤ e + 3) : ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  no_tiling_W_gap_of_sigma_le (B := fun e => e + 3) sigmaAllLe_rung3 hco he hef hfM hMf hk

#print axioms sigmaAllLe_rung3
#print axioms no_tiling_W_rung3

end Erdos634.Draft.WGapRung
