/-
Draft/WGapClimb8.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.2-P9.4 with `h_lambda = 0` throughout).
Not imported by any aggregate.  No sorry, no native_decide.
* `climb_nostation`: Proposition B for `i >= 1` (or `j >= 1`), CONDITIONAL on the explicit hypothesis `hNoSt` that no column `x <= i - lam - 2` of the row `y = j + lam` carries `N_x` (no station; PROOF 9.4 (3) is exactly the refutation of this hypothesis, or its replacement by an apex switch).  `hNoSt` is NOT a hypothesis of any top-level statement: it is the case boundary of the not yet built station lemma.
* `prop_B_le_two`: for `i <= 2` the hypothesis `hNoSt` is vacuous (columns `x <= i - lam - 2 < 0`): Proposition B at `i = 1, 2` (and `i = 0` with `j >= 1`) from the GENERAL climb (controls `prop_B_one`, `prop_B_two`).
-/
import Erdos634.Draft.WGapClimb7

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

section climb8

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 32000000 in
theorem climb_nostation (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J j i : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hij : i + j + 1 ≤ f - 1) (hj1 : 1 ≤ j + i)
    (hSig : SigmaAll D e f i)
    (hNoSt : ∀ lam : ℕ, 1 ≤ lam → lam < i → ∀ x : ℕ, x + 2 + lam ≤ i → ¬ NTile D e f c₀ x (j + lam)) :
    ¬ PiBCfg D e f c₀ J j i := by
  rintro ⟨hS1, hUall, hDall, hD0, hN, hP4⟩
  have key : ∀ n : ℕ, n ≤ i → ClimbSt D e f c₀ J j i n := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, hS1, hUall, hDall⟩
      intro t h1 h2'
      have : t = i := by omega
      subst this
      have e1 : j + t - t = j := by omega
      rw [e1]
      exact hN
    | succ n ih =>
      intro hn
      have hSt := ih (by omega)
      refine climb_step0 S h2 hH4 hA (by omega) hij (by omega) hSt ?_ hP4 hSig
      intro x hx
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · exact hD0 x (by omega)
      · rcases row_cases S hA (by omega) hij hn1 (by omega) hSt hSig hx with hD' | hN'
        · exact hD'
        · exfalso
          by_cases hx2 : x + 2 + n ≤ i
          · exact hNoSt n hn1 (by omega) x hx2 hN'
          · have hxe : x = i - n - 1 := by omega
            rw [hxe] at hN'
            exact rowN_false S hij hn1 (by omega) hSt hP4 hN'
  exact climb_end0 S (by omega) hij hj1 (key i le_rfl) hP4

/-- Proposition B at `i <= 2` from the general climb (control for `prop_B_one`, `prop_B_two`; here also `i = 0` with `j >= 1`) -/
theorem prop_B_le_two (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J j i : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hi2 : i ≤ 2) (hij : i + j + 1 ≤ f - 1) (hj1 : 1 ≤ j + i)
    (hSig : SigmaAll D e f i) : ¬ PiBCfg D e f c₀ J j i :=
  climb_nostation S h2 hH4 hA hJ hij hj1 hSig (fun lam h1 h2' x hx => by omega)

end climb8

#print axioms climb_nostation
#print axioms prop_B_le_two

end Erdos634.Draft.WGapStmt
