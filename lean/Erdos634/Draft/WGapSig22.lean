/-
Draft/WGapSig22.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.2 (c), (d)).
Not imported by any aggregate.  No sorry, no native_decide.
* `sigma_succ`: **Theorem ST (c) in the form `Σ[m] ∧ B-exits of size m+1 ⇒ Σ[m+1]`** (`sigma_step_n2` with `hSTa := st_a`; `lemma_M` for the size 1).
* `st_d`: **`Σ[e+2]` UNCONDITIONALLY** (ST (d)): the exits are vacuous for `n ≤ e+2`.
-/
import Erdos634.Draft.WGapSig21

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

section sig22

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem sigma_succ (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) (m : ℕ)
    (hIH : SigmaAll D e f m)
    (hB : ∀ c₀ J : ℕ, IsApex D e f c₀ J → ∀ s y₀ i : ℕ, J ≤ y₀ → y₀ < s → s ≤ f - 1 → s - y₀ = m + 1 → 1 ≤ i →
      i + 2 ≤ s - y₀ → e + 1 + i + 1 + y₀ ≤ s → ¬ (OmegaCfg D e f c₀ J s y₀ i ∧ Pi4 D e f c₀ i y₀)) :
    SigmaAll D e f (m + 1) := by
  intro c₀ J hA s y₀ hJ hy hsf hsm hσ
  by_cases hlt : s ≤ y₀ + m
  · exact hIH c₀ J hA s y₀ hJ hy hsf hlt hσ
  · have hn : s - y₀ = m + 1 := by omega
    rcases Nat.lt_or_ge m 1 with h0 | h1
    · have hm0 : m = 0 := by omega
      subst hm0
      exact sigma_le_e S h2 1 S.he c₀ J hA s y₀ hJ hy hsf hsm hσ
    · have hn2 : 2 ≤ s - y₀ := by omega
      refine sigma_step_n2 S h2 hH4 hA hJ hy hsf hn2 (by rw [show s - y₀ - 1 = m by omega]; exact hIH)
        (fun hn' hΩ => st_a S h2 hH4 hA hJ hy hsf hn' hΩ)
        (fun i hi1 hi2 hi3 => hB c₀ J hA s y₀ i hJ hy hsf hn hi1 hi2 hi3) hσ

/-- **ST (d)**: `Σ[e+2]` unconditionally -/
theorem st_d (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) :
    ∀ m : ℕ, m ≤ e + 2 → SigmaAll D e f m := by
  intro m
  induction m with
  | zero =>
    intro _ c₀ J hA s y₀ hJ hy hsf hsm
    omega
  | succ m ih =>
    intro hm
    refine sigma_succ S h2 hH4 m (ih (by omega)) ?_
    intro c₀ J hA s y₀ i hJ hy hsf hn hi1 hi2 hi3
    exfalso
    omega

end sig22

#print axioms sigma_succ
#print axioms st_d

end Erdos634.Draft.WGapStmt
