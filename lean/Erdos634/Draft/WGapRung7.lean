/-
Draft/WGapRung7.lean -- 16 November 2026 (work item LEAN_WGAP_2026-11-15, session 17).  UNAUDITED beyond internal checks.  Not imported by any aggregate.
**Rung 5, UNCONDITIONAL**: `no_tiling_W_rung5`: no tiling of `W_M(e,f)` when `M (f - e) <= e + 5` (and `M (f-e) < f`, `f <= M e`, `2 <= e`, `gcd (e,f) = 1`).
`prop_B_three` (Proposition B at `i = 3`) is `prop_B_of_station_P` (the general climb with the station lemma `station_stmt_P`, WGapStation1-3) with `B` at `i <= 2` from `prop_B_le_two`;
`Sigma[e+5]` is `sigma_succ` at `m = e+4` from `Sigma[e+4]` (WGapRung5), its exit hypotheses (`B` at `i = 1, 2, 3`) are `prop_B_one`, `prop_B_two`, `prop_B_three`, each from `Sigma[i]` (`st_d`).
Credit: Beeson-Rosu (framework), the W-gap formalization work item (all of WGap*), the Sigma-station template of session 8 (`WGapDich*`).
-/
import Erdos634.Draft.WGapStation3
import Erdos634.Draft.WGapRung5

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

section rung7

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **Proposition B at `i = 3`**, from `Sigma[3]` -/
theorem prop_B_three (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J : ℕ} (hA : IsApex D e f c₀ J) {j : ℕ} (hJ : J ≤ j) (hij : 3 + j + 1 ≤ f - 1)
    (hSig : SigmaAll D e f 3) : ¬ PiBCfg D e f c₀ J j 3 := by
  refine prop_B_of_station_P S h2 hH4 hA hJ hij (by omega) hSig ?_
  intro c₁ J₁ hA₁ j₁ i₁ hJ₁ hi₁ hij₁ hj1
  exact prop_B_le_two S h2 hH4 hA₁ hJ₁ (by omega) hij₁ hj1 (hSig.mono' (by omega))

/-- **`Sigma[e+5]` unconditionally** -/
theorem sigmaAllLe_rung5 : SigmaAllLeStmt (fun e => e + 5) := by
  intro N D e f α β γ L ax ay S h2 hH4 he2 m hm
  have hm' : m ≤ e + 5 := hm
  rcases Nat.lt_or_ge m (e + 5) with hlt | hge
  · exact sigmaAllLe_rung4 S h2 hH4 he2 m (by show m ≤ e + 4; omega)
  · have hme : m = e + 5 := by omega
    subst hme
    refine sigma_succ S h2 hH4 (e + 4) (sigmaAllLe_rung4 S h2 hH4 he2 (e + 4) le_rfl) ?_
    intro c₀ J hA s y₀ i hJ hy hsf hn hi1 hi2 hi3 ⟨hΩ, hP⟩
    have hPB := omega_pib hi2 hΩ hP
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · exact prop_B_one S h2 hH4 hA hJ (by omega) (st_d S h2 hH4 1 (by omega)) hPB
    · exact prop_B_two S h2 hH4 hA hJ (by omega) (st_d S h2 hH4 2 (by omega)) hPB
    · exact prop_B_three S h2 hH4 hA hJ (by omega) (st_d S h2 hH4 3 (by omega)) hPB

end rung7

/-- **Theorem R5 (rung `e+5`), UNCONDITIONAL**: no tiling of `W_M(e,f)` when `M (f-e) <= e + 5` (and `M (f-e) < f`). -/
theorem no_tiling_W_rung5 (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hMf : M * (f - e) < f) (hk : M * (f - e) ≤ e + 5) : ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  no_tiling_W_gap_of_sigma_le (B := fun e => e + 5) sigmaAllLe_rung5 hco he hef hfM hMf hk

#print axioms prop_B_three
#print axioms sigmaAllLe_rung5
#print axioms no_tiling_W_rung5

end Erdos634.Draft.WGapRung
