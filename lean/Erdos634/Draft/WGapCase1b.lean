/-
Draft/WGapCase1b.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 Case 1).
Not imported by any aggregate.  Module P-C2: the CASE 1 SUPPLIER of `inv_step` (hypothesis `case1` of `inv_step`/`u3_of_suppliers`, with the concrete `Bst`): the least flipped alpha-tile at `p'(i1, j-i1)`
gives the bottom clamp of level `j+1` (`flip_botclamp`) and the structure (b) at level `j+1`: `js = j - i1`, the flipped tile at `X0 = p'(i1, js)`, its far-side clamp (`clampB_outside` for `js = 0`
= [SIDE-2], `clampB_tile` with `U'(i1, js-1)` of the invariant (a) for `js >= 1`) and `D'(i1-1, js)` from the level step.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapB1

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

section case1b

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem flipAt_of_flip {j i : ℕ} (hij : i ≤ j) (h : Flip D e f j i) : FlipAt D e f i (j - i) := by
  obtain ⟨τ, hτ⟩ := h
  have c1 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by rw [Nat.cast_sub hij]
  exact ⟨τ, by rw [c1]; exact hτ⟩

/-- **Case 1 supplier** -/
theorem case1_supplier (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {J : ℕ} (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) :
    ∀ j c i₁ : ℕ, Inv D e f (Bst D e f) j c → j < J → 1 ≤ i₁ → i₁ ≤ c → (i₁ < c ∨ c = j) → Flip D e f j i₁ →
        (∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f j i) → BotClamp D e f (j + 1) i₁ ∧ Bst D e f (j + 1) i₁ := by
  intro j c i₁ I hjJ h1 h2' h3 hF _
  have hcj := I.cj
  have hc1 := I.c1
  refine ⟨flip_botclamp S h1 hF, ?_⟩
  intro _
  refine ⟨j - i₁, by omega, flipAt_of_flip (by omega) hF, ?_, ?_⟩
  · by_cases hj0 : j - i₁ = 0
    · rw [hj0]; exact clampB_outside S h2 i₁
    · have hic : i₁ < c := by omega
      obtain ⟨t, ht⟩ := I.ha i₁ (j - i₁ - 1) hic (by omega)
      exact clampB_tile S (by omega) ⟨t, ht⟩
  · intro i' hi1 hi2
    have hi' : i' = j - i₁ := by omega
    subst hi'
    have h := (level_data S hJf hU hT (by omega) hjJ I).1 (i₁ - 1) (by omega)
    have e1 : j - 1 - (i₁ - 1) = j - i₁ := by omega
    rw [e1] at h
    exact h

end case1b

end Erdos634.Draft.WGapStmt
