import Erdos634.MarchMonotone
namespace Erdos634.Draft.MarchMonotoneWrap
open Erdos634.MarchMonotone

variable {L : ℕ} (w : ℕ → Bool)

theorem wrap_mono_of_no_step (h : ∀ i, i + 1 < L → w i = true → w (i + 1) = true) :
    ∀ i j, i ≤ j → j < L → w i = true → w j = true :=
  mono_of_no_step w h

theorem wrap_block_form (h : ∀ i, i + 1 < L → w i = true → w (i + 1) = true) :
    ∃ j : ℕ, (∀ i, i < j → i < L → w i = false) ∧ (∀ i, j ≤ i → i < L → w i = true) :=
  block_form w h

theorem wrap_at_most_one_transition
    (h : ∀ i, i + 1 < L → w i = true → w (i + 1) = true) :
    ∃ j : ℕ, ∀ i, i + 1 < L → w i ≠ w (i + 1) → i + 1 = j :=
  at_most_one_transition w h

theorem wrap_transitions_card_le_one
    (h : ∀ i, i + 1 < L → w i = true → w (i + 1) = true) :
    ((Finset.range L).filter (fun i => i + 1 < L ∧ w i ≠ w (i + 1))).card ≤ 1 :=
  transitions_card_le_one w h

theorem wrap_exceptional_is_transition (i : ℕ)
    (hi : w i = false) (hi1 : w (i + 1) = true) : w i ≠ w (i + 1) :=
  exceptional_is_transition w i hi hi1

example : True := trivial
#print axioms wrap_transitions_card_le_one
end Erdos634.Draft.MarchMonotoneWrap
