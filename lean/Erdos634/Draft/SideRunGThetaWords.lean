/-
Draft/SideRunGThetaWords.lean  Part of `AllThreshold`.  Word part.

**The word theorem for a side whose two corners have the angle `α + β`.**  Let `1 ≤ e < f` be coprime and `Δ` a triangle cut into copies of `(ef, f² − e², f²)`; if a side `s` of `Δ` has the angle `α + β` at both corners,
then `s` carries `f` consecutive tiles of type `C1` or `f` of type `C2`; in particular `|s| ≥ f³`.  The proof is the word argument of `thm:siderunall` (`SideRunWords.side_word`) with the right corner `α + β` instead of `β`:

* the last tile does not show `γ` at its right end (`rB`: not of type `R`; the corner `α + β` is smaller than `γ`), instead of "the last tile is `A2` or `C1`";
* the rule (a) is as in `SideRules`; the rule (b) says in addition that a maximal run of `C2` that is first or follows a tile of type `R` does not end the side (rule (d): at the right corner `α + β`, (i') holds); the rule (c) is as in `SideRules`.

CONTENTS.  `SideRulesT n m τ` (the rules), `side_word_T` (a word that satisfies them contains `n` consecutive `C1` or `n` consecutive `C2`), `exRulesT` (the hypotheses are satisfiable).  `run_max`, `ty_cases`, `b1_gR` of `SideRunWords.lean` are reused.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunWords

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGT

open Erdos634.Draft.W2E1 Erdos634.Draft.W2E1.Ty Erdos634.Draft.SideRun

/-- **THE RULES OF A SIDE WITH THE CORNERS `α + β`, `α + β`**, for a typed word `τ 0, …, τ (m − 1)`, `0 < m`, with the run bound `n`. -/
structure SideRulesT (n m : ℕ) (τ : ℕ → Ty) : Prop where
  rQ : τ 0 ≠ A2 ∧ τ 0 ≠ B2
  rB : ¬ (τ (m - 1)).gR
  rGG : ∀ k, k + 1 < m → (τ k).gR → ¬ (τ (k + 1)).gL
  ra : ∀ i k, 1 ≤ k → k < n → i + k ≤ m → (∀ j, j < k → τ (i + j) = C1) →
    (i = 0 ∨ (τ (i - 1)).gR) → i + k < m ∧ (τ (i + k) = B1 ∨ τ (i + k) = C1)
  rb : ∀ i k, 1 ≤ k → k < n → i + k ≤ m → (∀ j, j < k → τ (i + j) = C2) →
    (i = 0 ∨ (τ (i - 1)).gR) → i + k < m ∧ ¬ (τ (i + k)).gL
  rc : ∀ i s r, 1 ≤ s → s < n → 1 ≤ r → r < n → i + s + r ≤ m → (∀ j, j < s → τ (i + j) = C2) →
    (∀ j, j < r → τ (i + s + j) = C1) → (i = 0 ∨ (τ (i - 1)).gR) →
    i + s + r < m ∧ (τ (i + s + r) = B1 ∨ τ (i + s + r) = C1)

/-- **THE WORD THEOREM OF S7 (SIDE-θ)**: a typed word that satisfies `SideRulesT` contains `n` consecutive `C1` or `n` consecutive `C2`.  (Paper, proof of `thm:siderunall` with the right corner `α + β`: after the start `Q` and after every tile of type `R` there is a
later tile of type `R`; the word is finite.) -/
theorem side_word_T (n m : ℕ) (τ : ℕ → Ty) (hm : 0 < m) (hr : SideRulesT n m τ) :
    ∃ i, i + n ≤ m ∧ ((∀ j, j < n → τ (i + j) = C1) ∨ (∀ j, j < n → τ (i + j) = C2)) := by
  by_contra hno
  push Not at hno
  have hshort1 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C1) → k < n := by
    intro p k hpk hrun
    by_contra hc
    push Not at hc
    obtain ⟨j, hj, hne⟩ := (hno p (by omega)).1
    exact hne (hrun j (by omega))
  have hshort2 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C2) → k < n := by
    intro p k hpk hrun
    by_contra hc
    push Not at hc
    obtain ⟨j, hj, hne⟩ := (hno p (by omega)).2
    exact hne (hrun j (by omega))
  -- after START and after every tile showing `γ` on the right there is a later such tile
  have step : ∀ p, p ≤ m → (p = 0 ∨ (τ (p - 1)).gR) →
      ∃ p', p < p' ∧ p' ≤ m ∧ (τ (p' - 1)).gR := by
    intro p hpm hp
    have hplt : p < m := by
      rcases Nat.lt_or_ge p m with h | h
      · exact h
      · exfalso
        have hpe : p = m := by omega
        rcases hp with h0 | hg
        · omega
        · rw [hpe] at hg
          exact hr.rB hg
    have hnotL : ¬ (τ p).gL := by
      rcases Nat.eq_zero_or_pos p with h0 | h0
      · rw [h0]
        intro hL
        rcases hL with h | h
        · exact hr.rQ.1 h
        · exact hr.rQ.2 h
      · rcases hp with h | hg
        · omega
        · have := hr.rGG (p - 1) (by omega) hg
          rwa [Nat.sub_add_cancel h0] at this
    rcases ty_cases (τ p) with hR | hL | hC1 | hC2
    · exact ⟨p + 1, by omega, by omega, by rwa [Nat.add_sub_cancel]⟩
    · exact absurd hL hnotL
    · obtain ⟨k, hk1, hkm, hrun, hend⟩ := run_max τ C1 p m hplt hC1
      have hkn := hshort1 p k hkm hrun
      obtain ⟨hlt, hnext⟩ := hr.ra p k hk1 hkn hkm hrun hp
      have hB : τ (p + k) = B1 := by
        rcases hnext with h | h
        · exact h
        · rcases hend with h' | h'
          · omega
          · exact absurd h h'
      refine ⟨p + k + 1, by omega, by omega, ?_⟩
      rw [Nat.add_sub_cancel, hB]; exact b1_gR
    · obtain ⟨s, hs1, hsm, hrun, hend⟩ := run_max τ C2 p m hplt hC2
      have hsn := hshort2 p s hsm hrun
      obtain ⟨hslt, hZnotL⟩ := hr.rb p s hs1 hsn hsm hrun hp
      have hZne : τ (p + s) ≠ C2 := by
        rcases hend with h | h
        · omega
        · exact h
      rcases ty_cases (τ (p + s)) with hR | hL | hC1 | hC2'
      · exact ⟨p + s + 1, by omega, by omega, by rwa [Nat.add_sub_cancel]⟩
      · exact absurd hL hZnotL
      · obtain ⟨r, hr1, hrm, hrun', hend'⟩ := run_max τ C1 (p + s) m hslt hC1
        have hrn := hshort1 (p + s) r hrm hrun'
        obtain ⟨hlt, hnext⟩ := hr.rc p s r hs1 hsn hr1 hrn hrm hrun hrun' hp
        have hB : τ (p + s + r) = B1 := by
          rcases hnext with h | h
          · exact h
          · rcases hend' with h' | h'
            · omega
            · exact absurd h h'
        refine ⟨p + s + r + 1, by omega, by omega, ?_⟩
        rw [Nat.add_sub_cancel, hB]; exact b1_gR
      · exact absurd hC2' hZne
  have hall : ∀ K : ℕ, ∃ p, K ≤ p ∧ p ≤ m ∧ (p = 0 ∨ (τ (p - 1)).gR) := by
    intro K
    induction K with
    | zero => exact ⟨0, le_refl _, Nat.zero_le _, Or.inl rfl⟩
    | succ K ih =>
      obtain ⟨p, hKp, hpm, hp⟩ := ih
      obtain ⟨p', hpp', hp'm, hg⟩ := step p hpm hp
      exact ⟨p', by omega, hp'm, Or.inr hg⟩
  obtain ⟨p, hp1, hp2, -⟩ := hall (m + 1)
  omega

/-- **The hypotheses of `side_word_T` are satisfiable**: the word `C1^n` satisfies the rules (`m = n ≥ 1`): the run rules ask nothing of a run of length `n`, and `C1` shows `β` at its right end. -/
theorem exRulesT (n : ℕ) (hn : 1 ≤ n) : SideRulesT n n (fun _ => C1) := by
  have hC2 : (C1 : Ty) ≠ C2 := by decide
  have hgR : ¬ (C1 : Ty).gR := by decide
  refine ⟨by decide, hgR, ?_, ?_, ?_, ?_⟩
  · intro k _ hg
    exact absurd hg hgR
  · intro i k hk1 hkn hik _ hp
    rcases hp with h | h
    · exact ⟨by omega, Or.inr rfl⟩
    · exact absurd h hgR
  · intro i k hk1 _ _ hrun _
    exact absurd (hrun 0 (by omega)) hC2
  · intro i s r hs1 _ _ _ _ hrun _ _
    exact absurd (hrun 0 (by omega)) hC2

end Erdos634.Draft.SideRunGT

#print axioms Erdos634.Draft.SideRunGT.side_word_T
#print axioms Erdos634.Draft.SideRunGT.exRulesT
