/-
Draft/WGapSig2.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.2 (b), P7.5 step (a)).
Not imported by any aggregate.  No sorry, no native_decide.
* `st_b`: `Ω_c` contains the station `O″ = p(c₀+i+1,y₀)` with the configuration `Σ_{O″}(s−i−1,y₀)` (K2, K3 shifted by `K2G_shift`, `K3G_shift_nat`).
* `sigma_noN`: PROOF 7.5 (a2): `N_i(y₀)` is not a tile, from `Σ[n−1]` (all apexes), Lemma M (`lemma_M`, sizes `≤ e`), `st_dichotomy_core`, `st_b` and the two exits
  of `F_b` (`hSTa`: ST (a), `i = 0`; `hB`: the exit hypothesis `B`).  `hSTa` and `hB` are HYPOTHESES here (ST (a) is proved separately; `hB` is Proposition B).
* `sigma_stepA`: STEP (a): `D(i,y₀)` is a tile for `0 ≤ i ≤ n−2` (`D_ofG`, `hR` from `Σ[n−1]`, `hNo` from `sigma_noN`; strong induction on `i`).
-/
import Erdos634.Draft.WGapDich4

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

theorem xo_eq_shiftX (f c₀ i : ℕ) : xo f (c₀ + i + 1) = shiftX (f : ℝ) 1 (xo f c₀) (i + 1) := by
  unfold xo shiftX; push_cast; ring

section sig2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem K2_xo {c₀ i s y₀ : ℕ} (hi : i + 1 ≤ s) (h : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) s y₀) :
    K2G D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + i + 1)) (s - i - 1) y₀ := by
  have hs : s - i - 1 + (i + 1) = s := by omega
  have h' : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (s - i - 1 + (i + 1)) y₀ := by rw [hs]; exact h
  have := K2G_shift (D := D) h'
  rwa [← xo_eq_shiftX] at this

theorem K3_xo {c₀ i s y₀ : ℕ} (hi : i + 1 ≤ s) (h : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (s : ℝ) (y₀ : ℝ)) :
    K3G D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + i + 1)) ((s - i - 1 : ℕ) : ℝ) (y₀ : ℝ) := by
  have hs : s - i - 1 + (i + 1) = s := by omega
  have h' : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (((s - i - 1 + (i + 1) : ℕ)) : ℝ) (y₀ : ℝ) := by rw [hs]; exact h
  have := K3G_shift_nat (D := D) (by norm_num : (1 : ℝ) ^ 2 = 1) h'
  rwa [← xo_eq_shiftX] at this

/-- **ST (b)** (PROOF 7.4) -/
theorem st_b (c₀ J s y₀ i : ℕ) (hi : i + 2 ≤ s - y₀)
    (hΩ : OmegaCfg D e f c₀ J s y₀ i) (hSt2 : St2 D (e : ℝ) (f : ℝ) (xo f (c₀ + i + 1)) (y₀ : ℝ)) :
    IsApex D e f (c₀ + i + 1) y₀ ∧ SigmaCfg D e f (c₀ + i + 1) y₀ (s - i - 1) y₀ := by
  obtain ⟨⟨hS1, hK2, hK3⟩, hDk, hNt, hEt⟩ := hΩ
  refine ⟨Or.inr ⟨by omega, hSt2⟩, ?_, K2_xo (by omega) hK2, K3_xo (by omega) hK3⟩
  intro y h1 h2
  have : y = y₀ := le_antisymm h2 h1
  subst this
  exact hEt

/-- **N_i(y₀) is not a tile** (PROOF 7.5 (a2)) -/
theorem sigma_noN (S : SetupG D e f α β γ L ax ay) {c₀ J s y₀ i : ℕ} (hJ : J ≤ y₀) (hy : y₀ < s) (hsf : s ≤ f - 1)
    (hi : i + 2 ≤ s - y₀) (hσ : SigmaCfg D e f c₀ J s y₀)
    (hDk : ∀ k : ℕ, k < i → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (k : ℝ) (y₀ : ℝ))
    (IHS : SigmaAll D e f (s - y₀ - 1))
    (hSTa : i = 0 → OmegaCfg D e f c₀ J s y₀ 0 → ¬ Pi4 D e f c₀ 0 y₀)
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
      · subst h0; exact hSTa rfl hΩ hPi4
      · exact hB hi0 (by omega) ⟨hΩ, hPi4⟩

/-- **STEP (a)**: `D(i,y₀)` is a tile for `0 ≤ i ≤ n−2` -/
theorem sigma_stepA (S : SetupG D e f α β γ L ax ay) {c₀ J s y₀ : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hy : y₀ < s)
    (hsf : s ≤ f - 1) (hσ : SigmaCfg D e f c₀ J s y₀) (IHS : SigmaAll D e f (s - y₀ - 1))
    (hSTa : 2 ≤ s - y₀ → OmegaCfg D e f c₀ J s y₀ 0 → ¬ Pi4 D e f c₀ 0 y₀)
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
      exact sigma_noN S hJ hy hsf hi ⟨hS1, hK2, hK3⟩ (fun k hk => ih k hk (by omega)) IHS
        (fun h0 hΩ => by subst h0; exact hSTa hi hΩ)
        (fun h1 h2 => hB i h1 hi h2) ⟨t, ht⟩

end sig2

#print axioms st_b
#print axioms sigma_noN
#print axioms sigma_stepA

end Erdos634.Draft.WGapStmt
