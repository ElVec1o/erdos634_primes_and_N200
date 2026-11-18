/-
Draft/WGapSig14.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5, n ≥ 2: steps (a), (b), (c)).
Not imported by any aggregate.  No sorry, no native_decide.
`sigma_step_n2`: **the induction step of Theorem ST (c) for `n = s − y₀ ≥ 2`**: from `Σ[n−1]` (all apexes) and the two exit hypotheses (`hSTa`: ST (a); `hB`: `¬ (Ω ∧ Π4)` for `i ≥ 1`,
`n−i−1 ≥ e+1`), `Σ_𝔞(s,y₀)`.  Steps: (a) `sigma_stepA`; (b) `sigma_row0`, `sigma_Tplus`, `sigma_rowB2`; (c) `T⁺` again (Theorem K at `js = y₀+1` or `Σ` at level `y₀+1`).
-/
import Erdos634.Draft.WGapSig13

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

section sig14

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 2000000 in
theorem sigma_step_n2 (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J s y₀ : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hy : y₀ < s) (hsf : s ≤ f - 1) (hn2 : 2 ≤ s - y₀)
    (IHS : SigmaAll D e f (s - y₀ - 1))
    (hSTa : 2 ≤ s - y₀ → OmegaCfg D e f c₀ J s y₀ 0 → ¬ Pi4 D e f c₀ 0 y₀)
    (hB : ∀ i : ℕ, 1 ≤ i → i + 2 ≤ s - y₀ → e + 1 + i + 1 + y₀ ≤ s →
      ¬ (OmegaCfg D e f c₀ J s y₀ i ∧ Pi4 D e f c₀ i y₀)) :
    ¬ SigmaCfg D e f c₀ J s y₀ := by
  intro hσ
  have hσ' := hσ
  obtain ⟨hS1, hK2, hK3⟩ := hσ
  have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
  have hDrow := sigma_stepA S hA hJ hy hsf hσ' IHS hSTa hB
  have hU01 := sigma_row0 S h2 hH4 hA hJ hy hsf hn2 hσ' hDrow
  have hTP := sigma_Tplus S hJ hy hn2 hσ' hU01
  have hq : 1 ≤ s - y₀ - 1 := by omega
  have hqj : (s - y₀ - 1) + y₀ + 1 ≤ f := by omega
  have hU0' : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0 := by
    have := hK2.1 0 0 (Nat.zero_le _) (by omega)
    rwa [Nat.cast_zero] at this
  -- the claim `K` / `Σ` of smaller size at the row `y₀ + 1`
  have hStarAll : ∀ s' : ℕ, y₀ + 1 < s' → s' < f → s' - (y₀ + 1) ≤ s - y₀ - 1 →
      K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) s' (y₀ + 1) →
      K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (s' : ℝ) ((y₀ + 1 : ℕ) : ℝ) → False := by
    intro s' h1 h2' h3 hk2 hk3
    rcases hTP with hK1 | hE1
    · exact K_at_origin S c₀ (y₀ + 1) (fun _ => h2) hU0' hK1 (s' - (y₀ + 1)) (by omega) s' (y₀ + 1) le_rfl h1 h2'
        rfl hk2 hk3
    · refine IHS c₀ J hA s' (y₀ + 1) (by omega) h1 (by omega) (by omega) ⟨?_, hk2, hk3⟩
      intro y hy1 hy2
      rcases Nat.lt_or_ge y (y₀ + 1) with hlt | hge
      · exact hS1 y hy1 (by omega)
      · have : y = y₀ + 1 := by omega
        subst this
        rw [Nat.cast_add, Nat.cast_one]
        exact hE1
  have hrow := sigma_rowB2 C hq hqj
    (fun i' j' hj' hij' => hK2.1 i' j' hj' (by omega)) (fun i' j' hj' hij' => hK2.2 i' j' hj' (by omega))
    (fun i' hi' => hDrow i' (by omega))
    (sigma_clamp_right S hy hsf hK2 hK3 hq)
    (by
      obtain ⟨tE, hE0⟩ := hS1 y₀ hJ le_rfl
      rw [zero_add] at hE0
      exact row_left_clamp_E S (by exact_mod_cast hq : (0 : ℝ) < ((s - y₀ - 1 : ℕ) : ℝ)) hE0)
    hU01
    (fun m' h1 h2' s' hs1 hs2 hs3 hk2 hk3 => hStarAll s' hs1 hs2 (by omega) hk2 hk3)
  -- step (c): `K2` and `K3` hold for `(s, y₀+1)`
  have hK2' : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) s (y₀ + 1) := by
    refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
    · rcases Nat.lt_or_ge j (y₀ + 1) with hlt | hge
      · exact hK2.1 i j (by omega) hij
      · have hje : j = y₀ + 1 := by omega
        subst hje
        have h := hrow i (by omega)
        rw [Nat.cast_add, Nat.cast_one]
        exact h
    · rcases Nat.lt_or_ge j y₀ with hlt | hge
      · exact hK2.2 i j hlt hij
      · have hje : j = y₀ := by omega
        subst hje
        exact hDrow i (by omega)
  have hK3' : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (s : ℝ) ((y₀ + 1 : ℕ) : ℝ) := hK3.mono (by push_cast; linarith)
  exact hStarAll s (by omega) (by omega) (by omega) hK2' hK3'

end sig14

#print axioms sigma_step_n2

end Erdos634.Draft.WGapStmt
