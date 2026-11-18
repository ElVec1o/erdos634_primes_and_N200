/-
Draft/WGapSig23.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P10).
Not imported by any aggregate.  No sorry, no native_decide.
**The joint induction, conditional on exactly Proposition B** (`PropBStmt` = `prop_B` of `WGapStmt_Scratch3_20261115.lean`, universally quantified; it contains Lemma RL):
* `omega_pib`: the bridge `Ω ∧ Π4 ⇒ Π_b` (PROOF 10.1, second claim).
* `sigma_B_joint_of`: `P(m) = Σ[m] ∧ B[m+1]` for every `m` from `PropBStmt` (rank induction of PROOF 10.3).
* `sigma_all_of_propB`, **`no_tiling_W_gap_of_propB`**: `no_tiling_W_gap` follows from `PropBStmt`.
So the ONLY missing proof of the whole target `no_tiling_W_gap` is Proposition B (P9, with Lemma RL, P8).  `PropBStmt` is a hypothesis here: a conditional reduction, not a result.
-/
import Erdos634.Draft.WGapSig22

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

/-- **Proposition B as a hypothesis** (`prop_B` of the Scratch3 file): `Π_b^𝔞(j,i)` does not occur, given `Σ[i]` and `B[i−2]` -/
def PropBStmt : Prop :=
  ∀ {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay)
    (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) (he2 : 2 ≤ e) (c₀ J : ℕ) (hA : IsApex D e f c₀ J) (j i : ℕ)
    (hJ : J ≤ j) (hij : i + j + 1 ≤ f - 1) (hSig : SigmaAll D e f i) (hB : BUpTo D e f (i - 1)),
    ¬ PiBCfg D e f c₀ J j i

section sig23

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **`Ω ∧ Π4 ⇒ Π_b`** (PROOF 10.1, "It contains Π_b^𝔞(y₀,i)") -/
theorem omega_pib {c₀ J s y₀ i : ℕ} (hi : i + 2 ≤ s - y₀) (hΩ : OmegaCfg D e f c₀ J s y₀ i) (hP : Pi4 D e f c₀ i y₀) :
    PiBCfg D e f c₀ J y₀ i := by
  obtain ⟨⟨hS1, hK2, hK3⟩, hDk, hNt, hEt⟩ := hΩ
  refine ⟨hS1, fun a b hb hab => hK2.1 a b hb (by omega), fun a b hb hab => hK2.2 a b hb (by omega), hDk, hNt, hP⟩

/-- **The joint induction** (PROOF 10.3), from Proposition B: `Σ[m] ∧ B[m+1]` for every `m` -/
theorem sigma_B_joint_of (hB : PropBStmt) (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    (he2 : 2 ≤ e) : ∀ m : ℕ, SigmaAll D e f m ∧ BUpTo D e f (m + 1) := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun c₀ J hA s y₀ hJ hy hsf hsm => by omega, ?_⟩
    intro c₀ J hA j i hJ hi hij
    have hi0 : i = 0 := by omega
    subst hi0
    exact hB S h2 hH4 he2 c₀ J hA j 0 hJ (by omega) (fun c₀ J hA s y₀ hJ hy hsf hsm => by omega)
      (fun c₀ J hA j i hJ hi => by omega)
  | succ m ih =>
    obtain ⟨hSg, hBm⟩ := ih
    have hSg' : SigmaAll D e f (m + 1) := by
      refine sigma_succ S h2 hH4 m hSg ?_
      intro c₀ J hA s y₀ i hJ hy hsf hn hi1 hi2 hi3
      intro ⟨hΩ, hP⟩
      exact hBm c₀ J hA y₀ i hJ (by omega) (by omega) (omega_pib hi2 hΩ hP)
    refine ⟨hSg', ?_⟩
    intro c₀ J hA j i hJ hi hij
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact hBm c₀ J hA j i hJ hlt hij
    · have hie : i = m + 1 := by omega
      subst hie
      exact hB S h2 hH4 he2 c₀ J hA j (m + 1) hJ hij hSg' (fun c₀ J hA j i hJ hi' hij' => hBm c₀ J hA j i hJ (by omega) hij')

/-- `Σ[m]` for every `m`, from Proposition B: the statement `SigmaAllStmt` of `WGapMainRed` -/
theorem sigma_all_of_propB (hB : PropBStmt) : SigmaAllStmt := by
  intro N D e f α β γ L ax ay S h2 hH4 he2 m
  exact (sigma_B_joint_of hB S h2 hH4 he2 m).1

/-- **`no_tiling_W_gap` from Proposition B alone** -/
theorem no_tiling_W_gap_of_propB (hB : PropBStmt) {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hfM : f ≤ M * e) (hMfe : M * (f - e) < f) : ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  no_tiling_W_gap_of_all (sigma_all_of_propB hB) hco he hef hfM hMfe

end sig23

#print axioms omega_pib
#print axioms sigma_B_joint_of
#print axioms no_tiling_W_gap_of_propB

end Erdos634.Draft.WGapStmt
