/-
Draft/WGapFinal.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P11.3).
Not imported by any aggregate.  **The W-gap corollary from Theorem MAIN** (the assembly S5 from S4, findings F1, F2 of FINDINGS.md closed):
`no_tiling_W_gap_of_main : WGapMainStmt → ¬ WTilable e f M` for coprime `2 ≤ e < f`, `f ≤ M e`, `M (f − e) < f`.
`WGapMainStmt` is EXACTLY the statement `wgap_main_stmt` of `WGapStmt_Scratch20261115.lean` (a hypothesis of the form "for every dissection ... False"), i.e. this module reduces the target
`no_tiling_W_gap` to the one remaining theorem MAIN.  The proof is that of `SplusThick.thickw_count_tiling_thick`/`cornerrun_counts_thick` with the last step replaced:
the word-count `z ≤ M (f − e) < f` (`SplusThickArith.C_AQ'`) kills alternative (i) (`f` consecutive `C1`/`C2`), alternative (ii) gives the run `C1^k`, `e + 1 ≤ k ≤ f − 1`, with
(H2) = `corner_run_mirror`, `Corner2` (F1) from `cornersA_two_of_angle`, (H4) (F2) from `setup_of_corners_F2` (|s'| = M f^3).
Credit: Beeson-Rosu (framework, cor:thickw), E2R6 work item, the S+ audit (G2 `M (f − e) < f`).  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStmt
import Erdos634.Draft.WGapSetupF2
import Erdos634.Draft.SplusThickFinal
import Erdos634.Draft.W23

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

/-- **Theorem MAIN as a hypothesis** (the statement `wgap_main_stmt` of the scratch, universally quantified) -/
def WGapMainStmt : Prop :=
  ∀ {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}
    (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    (he2 : 2 ≤ e) (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk1 : e + 1 ≤ k) (hkf : k ≤ f - 1)
    (hrun : ∀ j, j < k → τ j = Ty.C1) (hsucc : k = m ∨ (k < m ∧ (τ k = Ty.A2 ∨ τ k = Ty.B2 ∨ τ k = Ty.C2)))
    (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 0 0), False

/-- **S5 from S4**: the W-gap corollary follows from Theorem MAIN -/
theorem no_tiling_W_gap_of_main (hmain : WGapMainStmt) {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hfM : f ≤ M * e) (hMfe : M * (f - e) < f) : ¬ Erdos634.Draft.CollarG.WTilable e f M := by
  rintro ⟨D₀, hT, hMod⟩
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; omega
    · exact h
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨hA, hQ, hB⟩ := W_corners_of_sides e f (by omega) hef hMr D₀ τ h1 h2 h3
  obtain ⟨D, g, L, ax, ay, hL, hLd, hD, hP, hB', S, Co, h2c, hdist⟩ :=
    setup_of_corners_F2 e f (by omega) hef hco D₀ hMod (rotA.trans τ) (Or.inl hA) (Or.inr hQ)
  obtain ⟨m, X, tile, τc, Ch⟩ := S.exists_chainG
  obtain ⟨x, y, z, hsum, hz⟩ := sideG_counts_gen S Ch
  have hLeq : L = (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [← hLd]; exact h2
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
  have hnat : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2) := by
    have h' : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℝ) =
        ((M * f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
      linear_combination hsum.trans hLeq
    exact_mod_cast h'
  have hzlt : z < f := by
    have := (SplusThick.C_AQ' (by omega) hef hco hnat).2 hMfe
    omega
  -- (H4) from the side `|s'| = M f^3`
  have hH4 : H4 f ax ay := by
    have e1 := dist_sq_pts (mkPt ax ay) (mkPt 0 0)
    have e2 : dist (mkPt ax ay) (mkPt 0 0) = (M : ℝ) * (f : ℝ) ^ 3 := by
      rw [hdist]; exact h1
    simp only [mkPt_zero, mkPt_one] at e1
    rw [e2] at e1
    unfold H4
    have hf2 : (2 : ℝ) ≤ f := by exact_mod_cast (by omega : 2 ≤ f)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hf3 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
    have hlt : ((f : ℝ) - 1) * (f : ℝ) ^ 2 < (M : ℝ) * (f : ℝ) ^ 3 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < f) 3]
    have hpos : (0 : ℝ) ≤ ((f : ℝ) - 1) * (f : ℝ) ^ 2 := by nlinarith
    nlinarith [e1]
  have hCorner2 : Corner2 e f ax ay := cornersA_two_of_angle S Co (h2c hA)
  rcases corner_side_theorem S Co Ch with ⟨i, him, hrun⟩ | ⟨k, hk1, hkf, hkm, hrun, hsucc⟩
  · have hfz := hz i f him hrun
    omega
  · have hsucc' : k = m ∨ (k < m ∧ τc k ≠ Ty.B1 ∧ τc k ≠ Ty.C1) := by
      rcases hsucc with h | ⟨h, h'⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
    have hek : e + 1 ≤ k := by
      by_contra hlt
      exact corner_run_short S Co Ch hk1 (by omega) hrun hsucc'
    have hMirror := corner_run_mirror S Co Ch hk1 hkf hrun hsucc'
    exact hmain S Co hCorner2 hH4 he Ch hek (by omega) hrun hsucc hMirror

#print axioms no_tiling_W_gap_of_main

end Erdos634.Draft.WGapStmt
