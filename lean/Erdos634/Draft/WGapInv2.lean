/-
Draft/WGapInv2.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5, step j -> j+1, Cases 1-3).
Not imported by any aggregate.  Module P-E2: the SKELETON of the induction of Lemma U3 with the three Case suppliers (`side3`, `case1`, `case3`) as NAMED HYPOTHESES:
`inv_step` (Inv j c, j < J => exists c', Inv (j+1) c'), the base case `inv_one`, the induction `inv_all`.  Case 2 (c = j, no flipped tile) is PROVED here (its clamp is `side1_botclamp`).
Hypotheses `side3` (the alpha-wedge at the boundary point p'(j,0)), `case1` (clamp at the flipped tile) and `case3` (clamp from the far-side c-edge, structure (b)) are discharged in later modules.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapInv1

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

/-- the unflipped alpha-tile `U'(i, j-i)` at the chord point `p'(i, j-i)` (real form of `level_fill`) -/
def Unfl (D : CongruentDissection N) (e f j i : ℕ) : Prop :=
  ∃ τ, HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ))) (mpG (e : ℝ) f 1 0 ((i : ℝ) + 1) ((j : ℝ) - (i : ℝ)))
    (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ) + 1))

/-- the flipped alpha-tile at `p'(i, j-i)` (its `c`-edge on `l'_i`) -/
def Flip (D : CongruentDissection N) (e f j i : ℕ) : Prop :=
  ∃ τ, HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ)))
    (mpG (e : ℝ) f 1 0 ((i : ℝ) + nuG (e : ℝ) f) ((j : ℝ) - (i : ℝ)))
    (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ) + 1 / nuG (e : ℝ) f))

section skel

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem unfl_utm {j i : ℕ} (hij : i ≤ j) (h : Unfl D e f j i) :
    UTM D (e : ℝ) f 1 0 (i : ℝ) (((j - i : ℕ)) : ℝ) := by
  obtain ⟨t, ht⟩ := h
  have c1 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by rw [Nat.cast_sub hij]
  rw [c1]; exact ⟨t, ht⟩

/-- `ha` of the next level -/
theorem ha_succ {Bst : ℕ → ℕ → Prop} {j c c' J : ℕ} (I : Inv D e f Bst j c) (hc' : c' ≤ c ∨ (c = j ∧ c' = j + 1))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) (hjJ : j < J)
    (hun : ∀ i : ℕ, 1 ≤ i → i < c' → UTM D (e : ℝ) f 1 0 (i : ℝ) (((j - i : ℕ)) : ℝ)) :
    ∀ i i' : ℕ, i < c' → i + i' + 1 ≤ j + 1 → UTM D (e : ℝ) f 1 0 (i : ℝ) (i' : ℝ) := by
  intro i i' hi hii
  have hcj := I.cj
  by_cases h1 : i + i' + 1 ≤ j
  · exact I.ha i i' (by rcases hc' with h | ⟨h, h'⟩ <;> omega) h1
  · have h2 : i' = j - i := by omega
    subst h2
    by_cases h0 : i = 0
    · subst h0
      simpa using hT j hjJ
    · exact hun i (by omega) hi

theorem hDp_succ {Bst : ℕ → ℕ → Prop} {j c c' : ℕ} (I : Inv D e f Bst j c) (hc' : c' ≤ c + 1)
    (hD : ∀ i : ℕ, i < c → DTM D (e : ℝ) f 1 0 (i : ℝ) (((j - 1 - i : ℕ)) : ℝ)) :
    ∀ i : ℕ, i + 2 ≤ c' → DTM D (e : ℝ) f 1 0 (i : ℝ) (((j + 1 - 2 - i : ℕ)) : ℝ) := by
  intro i hi
  have h : j + 1 - 2 - i = j - 1 - i := by omega
  rw [h]; exact hD i (by omega)

/-- **The induction step `Inv j c -> Inv (j+1) c'`** (skeleton: the three suppliers are hypotheses). -/
theorem inv_step (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {J : ℕ} (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} (hBj : ∀ j, Bst j j)
    (side3 : ∀ j c : ℕ, Inv D e f Bst j c → j < J → c = j → Unfl D e f j j ∨ Flip D e f j j)
    (case1 : ∀ j c i₁ : ℕ, Inv D e f Bst j c → j < J → 1 ≤ i₁ → i₁ ≤ c → (i₁ < c ∨ c = j) → Flip D e f j i₁ →
        (∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f j i) → BotClamp D e f (j + 1) i₁ ∧ Bst (j + 1) i₁)
    (case3 : ∀ j c : ℕ, Inv D e f Bst j c → j < J → c < j → (∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f j i) →
        BotClamp D e f (j + 1) c ∧ Bst (j + 1) c)
    {j c : ℕ} (hj1 : 1 ≤ j) (hjJ : j < J) (I : Inv D e f Bst j c) : ∃ c' : ℕ, Inv D e f Bst (j + 1) c' := by
  obtain ⟨hD, hW⟩ := level_data S hJf hU hT hj1 hjJ I
  have hcj := I.cj
  have hc1 := I.c1
  by_cases hfl : ∃ i : ℕ, 1 ≤ i ∧ i ≤ c ∧ (i < c ∨ c = j) ∧ Flip D e f j i
  · set i₁ := Nat.find hfl with hi₁
    obtain ⟨h1, h2', h3, h4⟩ := Nat.find_spec hfl
    have hmin : ∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f j i := by
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
    have hU' : ∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f j i := by
      intro i hi1 hic
      rcases hW i hi1 hic with h | h
      · exact h
      · exact absurd h (hfl i hi1 hic.le (Or.inl hic))
    by_cases hc : c = j
    · have hUj : Unfl D e f j j := by
        rcases side3 j c I hjJ hc with h | h
        · exact h
        · exact absurd h (by have := hfl j hj1 (by omega) (Or.inr hc); exact this)
      refine ⟨j + 1, ⟨by omega, le_rfl,
        ha_succ I (Or.inr ⟨hc, rfl⟩) hT hjJ ?_, hDp_succ I (by omega) hD, side1_botclamp S h2 (j + 1), hBj (j + 1)⟩⟩
      intro i hi1 hi2
      by_cases hij : i = j
      · subst hij; exact unfl_utm le_rfl hUj
      · exact unfl_utm (by omega) (hU' i hi1 (by omega))
    · obtain ⟨hcl, hb⟩ := case3 j c I hjJ (by omega) hU'
      exact ⟨c, ⟨hc1, by omega,
        ha_succ I (Or.inl le_rfl) hT hjJ (fun i hi1 hi2 => unfl_utm (by omega) (hU' i hi1 hi2)),
        hDp_succ I (by omega) hD, hcl, hb⟩⟩

end skel

end Erdos634.Draft.WGapStmt
