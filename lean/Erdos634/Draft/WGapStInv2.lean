/-
Draft/WGapStInv2.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapInv2`: the induction step `Inv j c -> Inv (j+1) c'` at absolute levels with floor `J0`,
the four suppliers (side1, side3, case1, case3) as NAMED HYPOTHESES.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStInv1

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

/-- the unflipped alpha-tile `U'(i, j-i)` at the chord point `p'(i, j-i)` -/
def Unfl (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (j i : ℕ) : Prop :=
  ∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ))) (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) ((j : ℝ) - (i : ℝ)))
    (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ) + 1))

/-- the flipped alpha-tile at `p'(i, j-i)` (its `c`-edge on `l'_i`) -/
def Flip (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (j i : ℕ) : Prop :=
  ∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ)))
    (mpG (e : ℝ) f 1 x ((i : ℝ) + nuG (e : ℝ) f) ((j : ℝ) - (i : ℝ)))
    (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ) + 1 / nuG (e : ℝ) f))

section skel

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

theorem unfl_utm {j i : ℕ} (hij : i ≤ j) (h : Unfl D e f x j i) :
    UTM D (e : ℝ) f 1 x (i : ℝ) (((j - i : ℕ)) : ℝ) := by
  obtain ⟨t, ht⟩ := h
  have c1 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by rw [Nat.cast_sub hij]
  rw [c1]; exact ⟨t, ht⟩

/-- `ha` of the next level -/
theorem ha_succ {Bst : ℕ → ℕ → Prop} {j c c' J : ℕ} (I : Inv D e f x J0 Bst j c) (hc' : c' ≤ c ∨ (c + J0 = j ∧ c' = c + 1))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) (hjJ : j < J)
    (hun : ∀ i : ℕ, 1 ≤ i → i < c' → UTM D (e : ℝ) f 1 x (i : ℝ) (((j - i : ℕ)) : ℝ)) :
    ∀ i i' : ℕ, i < c' → J0 ≤ i' → i + i' + 1 ≤ j + 1 → UTM D (e : ℝ) f 1 x (i : ℝ) (i' : ℝ) := by
  intro i i' hi hJ hii
  have hcj := I.cj
  have hc1 := I.c1
  by_cases h1 : i + i' + 1 ≤ j
  · exact I.ha i i' (by rcases hc' with h | ⟨h, h'⟩ <;> omega) hJ h1
  · have h2 : i' = j - i := by omega
    subst h2
    by_cases h0 : i = 0
    · subst h0
      simpa using hT j (by omega) hjJ
    · exact hun i (by omega) hi

theorem hDp_succ {Bst : ℕ → ℕ → Prop} {j c c' : ℕ} (I : Inv D e f x J0 Bst j c) (hc' : c' ≤ c + 1)
    (hD : ∀ i : ℕ, i < c → DTM D (e : ℝ) f 1 x (i : ℝ) (((j - 1 - i : ℕ)) : ℝ)) :
    ∀ i : ℕ, i + 2 ≤ c' → DTM D (e : ℝ) f 1 x (i : ℝ) (((j + 1 - 2 - i : ℕ)) : ℝ) := by
  intro i hi
  have h : j + 1 - 2 - i = j - 1 - i := by omega
  rw [h]; exact hD i (by omega)

/-- **The induction step `Inv j c -> Inv (j+1) c'`** (skeleton: the four suppliers are hypotheses). -/
theorem inv_step (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1))
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop}
    (hBj : ∀ j c, c + J0 = j → Bst j c)
    (side1 : ∀ j c : ℕ, Inv D e f x J0 Bst j c → j < J → c + J0 = j → (∀ t : ℕ, t ≤ c → UTM D (e : ℝ) f 1 x (t : ℝ) (J0 : ℝ)) →
        BotClamp D e f x (j + 1) (c + 1))
    (side3 : ∀ j c : ℕ, Inv D e f x J0 Bst j c → j < J → c + J0 = j → Unfl D e f x j c ∨ Flip D e f x j c)
    (case1 : ∀ j c i₁ : ℕ, Inv D e f x J0 Bst j c → j < J → 1 ≤ i₁ → i₁ ≤ c → (i₁ < c ∨ c + J0 = j) → Flip D e f x j i₁ →
        (∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f x j i) → BotClamp D e f x (j + 1) i₁ ∧ Bst (j + 1) i₁)
    (case3 : ∀ j c : ℕ, Inv D e f x J0 Bst j c → j < J → c + J0 < j → (∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f x j i) →
        BotClamp D e f x (j + 1) c ∧ Bst (j + 1) c)
    {j c : ℕ} (hj1 : J0 + 1 ≤ j) (hjJ : j < J) (I : Inv D e f x J0 Bst j c) : ∃ c' : ℕ, Inv D e f x J0 Bst (j + 1) c' := by
  obtain ⟨hD, hW⟩ := level_data S hJf hU hT hj1 hjJ I
  have hcj := I.cj
  have hc1 := I.c1
  by_cases hfl : ∃ i : ℕ, 1 ≤ i ∧ i ≤ c ∧ (i < c ∨ c + J0 = j) ∧ Flip D e f x j i
  · set i₁ := Nat.find hfl with hi₁
    obtain ⟨h1, h2', h3, h4⟩ := Nat.find_spec hfl
    have hmin : ∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f x j i := by
      intro i hi1 hi2
      have hnp := Nat.find_min hfl hi2
      have hic : i < c := by omega
      rcases hW i hi1 hic with h | h
      · exact h
      · exact absurd ⟨hi1, hic.le, Or.inl hic, h⟩ hnp
    obtain ⟨hcl, hb⟩ := case1 j c i₁ I hjJ h1 h2' h3 h4 hmin
    exact ⟨i₁, ⟨h1, by omega,
      ha_succ I (Or.inl h2') hT hjJ (fun i hi1 hi2 => unfl_utm (by omega) (hmin i hi1 hi2)),
      hDp_succ I (by omega) hD, hcl, hb⟩⟩
  · push_neg at hfl
    have hU' : ∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f x j i := by
      intro i hi1 hic
      rcases hW i hi1 hic with h | h
      · exact h
      · exact absurd h (hfl i hi1 hic.le (Or.inl hic))
    by_cases hc : c + J0 = j
    · have hUj : Unfl D e f x j c := by
        rcases side3 j c I hjJ hc with h | h
        · exact h
        · exact absurd h (by have := hfl c hc1 le_rfl (Or.inr hc); exact this)
      have hUall : ∀ t : ℕ, t ≤ c → UTM D (e : ℝ) f 1 x (t : ℝ) (J0 : ℝ) := by
        intro t ht
        by_cases htc : t = c
        · subst htc
          have := unfl_utm (by omega) hUj
          have e1 : j - t = J0 := by omega
          rw [e1] at this
          exact this
        · obtain ⟨τ, hτ⟩ := I.ha t J0 (by omega) le_rfl (by omega)
          exact ⟨τ, hτ⟩
      refine ⟨c + 1, ⟨by omega, by omega,
        ha_succ I (Or.inr ⟨hc, rfl⟩) hT hjJ ?_, hDp_succ I (by omega) hD, side1 j c I hjJ hc hUall, hBj (j + 1) (c + 1) (by omega)⟩⟩
      intro i hi1 hi2
      by_cases hij : i = c
      · subst hij; exact unfl_utm (by omega) hUj
      · exact unfl_utm (by omega) (hU' i hi1 (by omega))
    · obtain ⟨hcl, hb⟩ := case3 j c I hjJ (by omega) hU'
      exact ⟨c, ⟨hc1, by omega,
        ha_succ I (Or.inl le_rfl) hT hjJ (fun i hi1 hi2 => unfl_utm (by omega) (hU' i hi1 hi2)),
        hDp_succ I (by omega) hD, hcl, hb⟩⟩

end skel

end Erdos634.Draft.WGapSt
