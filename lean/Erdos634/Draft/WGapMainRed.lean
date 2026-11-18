/-
Draft/WGapMainRed.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P10.4, P11.1).
Not imported by any aggregate.  **Theorem MAIN from Theorem Sigma at the corner**: `wgap_main_of_sigma : SigmaCornerStmt → WGapMainStmt`, and S0 `mirrorAt_iff_UTM00`
(the corner mirror tile `T_0` of the project's `MirrorAt` is `UTM D e f 1 0 0 0`).  `SigmaCornerStmt` is `theorem_sigma_corner` of `WGapStmt_Scratch3_20261115.lean` (universally
quantified hypothesis).  The proof uses `SideRunGMo.corner_run_data` (the run hypotheses give `MirrorAt`, `K2G D e f 1 0 k 0`, `K3G D e f 1 0 k 0`).  Together with
`WGapFinal.no_tiling_W_gap_of_main` the target `no_tiling_W_gap` is reduced to `SigmaCornerStmt`.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapFinal
import Erdos634.Draft.WGapMirrorLat
import Erdos634.Draft.WGapInterior
import Erdos634.Draft.WGapDall
import Erdos634.Draft.WGapDefs3

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Erdos634.Draft.FDBBaseBetaE1 Set

variable {N : ℕ} {D : CongruentDissection N}

/-- **S0**: `(H2)` of the hand proof (the project's `MirrorAt`) is the tile `T_0 = μ U(0,0)` -/
theorem mirrorAt_iff_UTM00 {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay) :
    MirrorAt D (e : ℝ) (f : ℝ) 1 0 0 ↔ UTM D (e : ℝ) (f : ℝ) 1 0 0 0 := by
  have he0 := S.e0
  have hef := S.hef'
  have hA : mpG (e : ℝ) f 1 0 0 0 = lpG (e : ℝ) f 1 0 0 0 := mpG_zero_zero _ _ _ _
  have hB : mpG (e : ℝ) f 1 0 0 (0 + 1) = lpG (e : ℝ) f 1 0 0 (0 + 1) := mp_zero_eta _ _ _ _ _
  have hC : mpG (e : ℝ) f 1 0 (0 + 1) 0 = lpG (e : ℝ) f 1 0 (-1) (0 + (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [mpG_eq he0 hef]
    unfold sMir
    exact lpG_congr (by ring) (by ring)
  unfold MirrorAt UTM
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, hasV_congr ht.swap.rot hA.symm hC.symm hB.symm⟩
  · rintro ⟨t, ht⟩
    have h2 := hasV_congr ht hA hC hB
    exact ⟨t, h2.swap.rot⟩

/-- **Theorem Sigma at the corner as a hypothesis** (the statement `theorem_sigma_corner` of `WGapStmt_Scratch3_20261115.lean`, universally quantified) -/
def SigmaCornerStmt : Prop :=
  ∀ {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay)
    (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) (he2 : 2 ≤ e) (k : ℕ) (hk1 : 1 ≤ k) (hkf : k ≤ f - 1),
    ¬ (UTM D (e : ℝ) (f : ℝ) 1 0 0 ((0 : ℕ) : ℝ) ∧ K2G D (e : ℝ) (f : ℝ) 1 0 k 0 ∧
      K3G D (e : ℝ) (f : ℝ) 1 0 (k : ℝ) ((0 : ℕ) : ℝ))

/-- **MAIN from Sigma at the corner**: the run `C1^k` of alternative (ii) gives `H(k)` (`corner_run_data`) -/
theorem wgap_main_of_sigma (hσ : SigmaCornerStmt) : WGapMainStmt := by
  intro N D e f α β γ L ax ay m X tile τ S Co h2 hH4 he2 Ch k hk1 hkf hrun hsucc hM
  have hsucc' : k = m ∨ (k < m ∧ τ k ≠ Ty.B1 ∧ τ k ≠ Ty.C1) := by
    rcases hsucc with h | ⟨h, h'⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
  obtain ⟨-, hMir, hK2, hK3⟩ := corner_run_data S Co Ch (by omega : 1 ≤ k) (by omega : k < f) hrun hsucc'
  have hUT : UTM D (e : ℝ) (f : ℝ) 1 0 0 ((0 : ℕ) : ℝ) := by
    rw [Nat.cast_zero]
    exact (mirrorAt_iff_UTM00 S).1 (by rw [Nat.cast_zero] at hMir; exact hMir)
  exact hσ S h2 hH4 he2 k (by omega) hkf ⟨hUT, hK2, hK3⟩

/-- **The target reduced to Sigma at the corner**: `no_tiling_W_gap` follows from `SigmaCornerStmt` -/
theorem no_tiling_W_gap_of_sigma (hσ : SigmaCornerStmt) {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hfM : f ≤ M * e) (hMfe : M * (f - e) < f) : ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  no_tiling_W_gap_of_main (wgap_main_of_sigma hσ) hco he hef hfM hMfe

/-- **The induction's output as a hypothesis**: `Σ[m]` for every `m` (first conjunct of `sigma_B_joint` of `WGapStmt_Scratch3_20261115.lean`) -/
def SigmaAllStmt : Prop :=
  ∀ {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay)
    (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) (he2 : 2 ≤ e) (m : ℕ), SigmaAll D e f m

/-- **Sigma at the corner from the induction**: the corner is the apex `(0,0)`, `H(k)` is `SigmaCfg D e f 0 0 k 0` -/
theorem sigma_corner_of_all (hall : SigmaAllStmt) : SigmaCornerStmt := by
  intro N D e f α β γ L ax ay S h2 hH4 he2 k hk1 hkf ⟨hUT, hK2, hK3⟩
  have hx : xo f 0 = 0 := by simp [xo]
  have hcfg : SigmaCfg D e f 0 0 k 0 := by
    refine ⟨fun y h1 h2' => ?_, ?_, ?_⟩
    · have hy : y = 0 := by omega
      subst hy
      rw [hx]; simpa using hUT
    · rw [hx]; exact hK2
    · rw [hx]; simpa using hK3
  exact hall S h2 hH4 he2 k 0 0 (Or.inl ⟨rfl, rfl⟩) k 0 le_rfl (by omega) hkf (by omega) hcfg

/-- **The target reduced to the induction**: `no_tiling_W_gap` from `Σ[m]` for all `m` -/
theorem no_tiling_W_gap_of_all (hall : SigmaAllStmt) {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hfM : f ≤ M * e) (hMfe : M * (f - e) < f) : ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  no_tiling_W_gap_of_sigma (sigma_corner_of_all hall) hco he hef hfM hMfe

#print axioms mirrorAt_iff_UTM00
#print axioms wgap_main_of_sigma
#print axioms no_tiling_W_gap_of_sigma
#print axioms no_tiling_W_gap_of_all

end Erdos634.Draft.WGapStmt
