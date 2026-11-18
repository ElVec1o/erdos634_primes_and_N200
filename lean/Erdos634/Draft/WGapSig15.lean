/-
Draft/WGapSig15.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.2 (c), (d)).
Not imported by any aggregate.  No sorry, no native_decide.
Copies of `sigma_noN`, `sigma_stepA`, `sigma_step_n2` (WGapSig2, WGapSig14) in which the exit hypothesis `hSTa` (ST (a)) carries the extra premise `e + 2 + y₀ ≤ s` (it is only
used when `n − 1 ≥ e + 1`), so that for `n ≤ e + 1` no exit hypothesis is needed: `sigma_le_e1` : `Σ[e+1]` UNCONDITIONALLY (no ST (a), no B).
-/
import Erdos634.Draft.WGapSig14

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

section sig15

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **N_i(y₀) is not a tile** (PROOF 7.5 (a2)) -/
theorem sigma_noN2 (S : SetupG D e f α β γ L ax ay) {c₀ J s y₀ i : ℕ} (hJ : J ≤ y₀) (hy : y₀ < s) (hsf : s ≤ f - 1)
    (hi : i + 2 ≤ s - y₀) (hσ : SigmaCfg D e f c₀ J s y₀)
    (hDk : ∀ k : ℕ, k < i → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (k : ℝ) (y₀ : ℝ))
    (IHS : SigmaAll D e f (s - y₀ - 1))
    (hSTa : i = 0 → e + 2 + y₀ ≤ s → OmegaCfg D e f c₀ J s y₀ 0 → ¬ Pi4 D e f c₀ 0 y₀)
    (hB : 1 ≤ i → e + 1 + i + 1 + y₀ ≤ s → ¬ (OmegaCfg D e f c₀ J s y₀ i ∧ Pi4 D e f c₀ i y₀)) :
    ¬ NTile D e f c₀ i y₀ := by
  intro hNt
  have hε1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hsf' : s < f := by omega
  obtain ⟨hS1, hK2, hK3⟩ := hσ
  obtain ⟨tN, hN⟩ := hNt
  have hmir := noN_mirror S hε1 hK2 hK3 hsf' hi tN hN
  have hEt : UTM D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + i + 1)) 0 (y₀ : ℝ) := by
    rw [xo_eq_shiftX]; exact (mirrorAt_iff_UTM_gen S _ _).1 hmir
  have hΩ : OmegaCfg D e f c₀ J s y₀ i := ⟨⟨hS1, hK2, hK3⟩, hDk, ⟨tN, hN⟩, hEt⟩
  by_cases hle : s - i - 1 ≤ y₀ + e
  · exact lemma_M S (c₀ + i + 1) (s - i - 1) y₀ (fun h => absurd h (by omega)) (by omega) (by omega) hle hEt
      (K2_xo (by omega) hK2) (K3_xo (by omega) hK3)
  · rcases st_dichotomy_core S hy hsf hi hK2 ⟨tN, hN⟩ hEt with hSt2 | hPi4
    · obtain ⟨hAp, hσ2⟩ := st_b c₀ J s y₀ i hi hΩ hSt2
      exact IHS (c₀ + i + 1) y₀ hAp (s - i - 1) y₀ le_rfl (by omega) (by omega) (by omega) hσ2
    · rcases Nat.eq_zero_or_pos i with h0 | hi0
      · subst h0; exact hSTa rfl (by omega) hΩ hPi4
      · exact hB hi0 (by omega) ⟨hΩ, hPi4⟩

/-- **STEP (a)**: `D(i,y₀)` is a tile for `0 ≤ i ≤ n−2` -/
theorem sigma_stepA2 (S : SetupG D e f α β γ L ax ay) {c₀ J s y₀ : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hy : y₀ < s)
    (hsf : s ≤ f - 1) (hσ : SigmaCfg D e f c₀ J s y₀) (IHS : SigmaAll D e f (s - y₀ - 1))
    (hSTa : 2 ≤ s - y₀ → e + 2 + y₀ ≤ s → OmegaCfg D e f c₀ J s y₀ 0 → ¬ Pi4 D e f c₀ 0 y₀)
    (hB : ∀ i : ℕ, 1 ≤ i → i + 2 ≤ s - y₀ → e + 1 + i + 1 + y₀ ≤ s →
      ¬ (OmegaCfg D e f c₀ J s y₀ i ∧ Pi4 D e f c₀ i y₀)) :
    ∀ i : ℕ, i + 2 ≤ s - y₀ → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (i : ℝ) (y₀ : ℝ) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨hS1, hK2, hK3⟩ := hσ
    have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
    have hU1 := hK2.1 i y₀ le_rfl (by omega)
    have hU2 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) y₀ := by
      have h := hK2.1 (i + 1) y₀ le_rfl (by omega)
      rwa [Nat.cast_add, Nat.cast_one] at h
    refine C.D_ofG hU1 hU2 ?_ ?_ ?_
    · rcases Nat.eq_zero_or_pos y₀ with hj | hj
      · exact Or.inl hj
      · exact Or.inr ⟨hj, hK2.2 (i + 1) (y₀ - 1) (by omega) (by omega)⟩
    · intro w hw
      refine IHS c₀ J hA (i + y₀ + 1) y₀ hJ (by omega) (by omega) (by omega)
        ⟨hS1, ⟨fun a b hb hab => hK2.1 a b hb (by omega), fun a b hb hab => hK2.2 a b hb (by omega)⟩, ?_⟩
      have e1 : ((i + y₀ + 1 : ℕ) : ℝ) = (i : ℝ) + y₀ + 1 := by push_cast; ring
      rw [e1]
      exact Or.inr ⟨w, hw⟩
    · intro t ht
      exact sigma_noN2 S hJ hy hsf hi ⟨hS1, hK2, hK3⟩ (fun k hk => ih k hk (by omega)) IHS
        (fun h0 h1 hΩ => by subst h0; exact hSTa hi h1 hΩ)
        (fun h1 h2 => hB i h1 hi h2) ⟨t, ht⟩

set_option maxHeartbeats 2000000 in
theorem sigma_step_n2b (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J s y₀ : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hy : y₀ < s) (hsf : s ≤ f - 1) (hn2 : 2 ≤ s - y₀)
    (IHS : SigmaAll D e f (s - y₀ - 1))
    (hSTa : 2 ≤ s - y₀ → e + 2 + y₀ ≤ s → OmegaCfg D e f c₀ J s y₀ 0 → ¬ Pi4 D e f c₀ 0 y₀)
    (hB : ∀ i : ℕ, 1 ≤ i → i + 2 ≤ s - y₀ → e + 1 + i + 1 + y₀ ≤ s →
      ¬ (OmegaCfg D e f c₀ J s y₀ i ∧ Pi4 D e f c₀ i y₀)) :
    ¬ SigmaCfg D e f c₀ J s y₀ := by
  intro hσ
  have hσ' := hσ
  obtain ⟨hS1, hK2, hK3⟩ := hσ
  have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
  have hDrow := sigma_stepA2 S hA hJ hy hsf hσ' IHS hSTa hB
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


/-- **`Σ[e+1]` UNCONDITIONALLY** (hypotheses: `Corner2`, `H4`, `2 ≤ e`; the exit hypotheses are vacuous for `n ≤ e + 1`): by induction on `n`, with `lemma_M` for `n ≤ e` and `sigma_step_n2b` for `n = e+1`.
Statement of `Σ[m]`: `SigmaAll D e f m`. -/
theorem sigma_le_e1 (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) :
    ∀ m : ℕ, m ≤ e + 1 → SigmaAll D e f m := by
  intro m
  induction m with
  | zero =>
    intro _ c₀ J hA s y₀ hJ hy hsf hsm
    omega
  | succ m ih =>
    intro hm c₀ J hA s y₀ hJ hy hsf hsm hσ
    by_cases hlt : s ≤ y₀ + m
    · exact ih (by omega) c₀ J hA s y₀ hJ hy hsf hlt hσ
    · have hn : s - y₀ = m + 1 := by omega
      rcases Nat.lt_or_ge m 1 with h0 | h1
      · -- n = 1
        have hm0 : m = 0 := by omega
        subst hm0
        exact sigma_le_e S h2 1 S.he c₀ J hA s y₀ hJ hy hsf hsm hσ
      · have hn2 : 2 ≤ s - y₀ := by omega
        refine sigma_step_n2b S h2 hH4 hA hJ hy hsf hn2 (by rw [hn]; simpa using ih (by omega)) ?_ ?_ hσ
        · intro _ h; omega
        · intro i hi1 hi2 hi3; omega

end sig15

#print axioms sigma_le_e1

end Erdos634.Draft.WGapStmt
