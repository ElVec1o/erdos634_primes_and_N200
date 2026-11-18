/-
Draft/WGapStCase1.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapCase1a` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStB1
import Erdos634.Draft.WGapStInv2

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}

open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv ub ClampB FlipAt Bst bst_self ub_norm ub_ne clampB_outside clampB_tile

/-- the Wall Lemma's conclusion at every point `q'(q,J0)` of the wall row, as a hypothesis (instantiated by `wl_mirror`) -/
def WallOK (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (J0 : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ f - 1 → (∀ t : ℕ, t < q → UTM D (e : ℝ) (f : ℝ) 1 x (t : ℝ) (J0 : ℝ)) →
    EdgeCover D (mpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) (J0 : ℝ))
      (mpG (e : ℝ) (f : ℝ) 1 x 1 (J0 : ℝ) - mpG (e : ℝ) (f : ℝ) 1 x 0 (J0 : ℝ))

section case1

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

theorem flip_botclamp (S : SetupG D e f α β γ L ax ay) {j i : ℕ} (hi : 1 ≤ i) (hF : Flip D e f x j i) :
    BotClamp D e f x (j + 1) i := by
  obtain ⟨τ, hτ⟩ := hF
  intro ed _
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine_x he0 hef x
  set ν := nuG (e : ℝ) f with hν
  have hδ : 0 < ν / (1 + ν) := by positivity
  refine not_straddles_short D.toDissection (j := τ) (δ := ν / (1 + ν)) (ρ := (i : ℝ)) hδ (by exact_mod_cast hi) ?_ ?_ ed.1 ed.2
  · unfold sj
    simp only [hm]
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  · intro ε h0 h1
    have hεν : ε * (1 + ν) < ν := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 1 + ν)).mp h1
      linarith
    have hε1 : ε < 1 := by nlinarith
    have hb : 0 < ε / ν := div_pos h0 hν0
    have hc : 0 < ν * (1 - ε) := mul_pos hν0 (by linarith)
    have ha : 0 < 1 - ε / ν - ν * (1 - ε) := by
      have : ε / ν + ν * (1 - ε) < 1 := by
        rw [div_add' _ _ _ hν0.ne', div_lt_one hν0]
        nlinarith
      linarith
    have key := hasV_bary hτ ha hb hc (by ring)
    convert key using 1
    unfold sj
    simp only [hm]
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    push_cast
    field_simp
    ring


theorem flipAt_of_flip {j i : ℕ} (hij : i ≤ j) (h : Flip D e f x j i) : FlipAt D e f x i (j - i) := by
  obtain ⟨τ, hτ⟩ := h
  have c1 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by rw [Nat.cast_sub hij]
  exact ⟨τ, by rw [c1]; exact hτ⟩

/-- **Case 1 supplier** (station) -/
theorem case1_supplier (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1))
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) (hW : WallOK D e f x J0) :
    ∀ j c i₁ : ℕ, Inv D e f x J0 (Bst D e f x J0) j c → j < J → 1 ≤ i₁ → i₁ ≤ c → (i₁ < c ∨ c + J0 = j) → Flip D e f x j i₁ →
        (∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f x j i) → BotClamp D e f x (j + 1) i₁ ∧ Bst D e f x J0 (j + 1) i₁ := by
  intro j c i₁ I hjJ h1 h2' h3 hF _
  have hcj := I.cj
  have hc1 := I.c1
  refine ⟨flip_botclamp S h1 hF, ?_⟩
  intro _
  refine ⟨j - i₁, by omega, by omega, flipAt_of_flip (by omega) hF, ?_, ?_⟩
  · by_cases hj0 : j - i₁ = J0
    · rw [hj0]
      refine clampB_wall S i₁ (hW i₁ h1 (by omega) ?_)
      intro t ht
      obtain ⟨τ, hτ⟩ := I.ha t J0 (by omega) le_rfl (by omega)
      exact ⟨τ, hτ⟩
    · have hic : i₁ < c := by omega
      obtain ⟨t, ht⟩ := I.ha i₁ (j - i₁ - 1) hic (by omega) (by omega)
      exact clampB_tile S (by omega) ⟨t, ht⟩
  · intro i' hi1 hi2
    have hi' : i' = j - i₁ := by omega
    subst hi'
    have h := (level_data S hJf hU hT (by omega) hjJ I).1 (i₁ - 1) (by omega)
    have e1 : j - 1 - (i₁ - 1) = j - i₁ := by omega
    rw [e1] at h
    exact h

end case1

end Erdos634.Draft.WGapSt
