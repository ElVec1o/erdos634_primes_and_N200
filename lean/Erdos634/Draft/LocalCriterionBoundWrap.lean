import Erdos634.LocalCriterionBound
namespace Erdos634.Draft.LocalCriterionBoundWrap
open Erdos634.LocalCriterionBound

variable {α : Type*} [DecidableEq α]

theorem wrap_no_forbidden_inside_witness
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    (W : Finset α) (hW : Realizable W) :
    ∀ F, Bad F → ¬ F ⊆ W :=
  no_forbidden_inside_witness Realizable Bad hsound W hW

theorem wrap_forbidden_meets_residue
    {T W F : Finset α} (hFT : F ⊆ T) (hnot : ¬ F ⊆ W) :
    (F ∩ (T \ W)).Nonempty :=
  forbidden_meets_residue hFT hnot

theorem wrap_F2
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    {T W : Finset α} (hWT : W ⊆ T) (hW : Realizable W) :
    (∀ F, Bad F → F ⊆ T → (F ∩ (T \ W)).Nonempty) ∧ (T \ W).card = T.card - W.card :=
  F2 Realizable Bad hsound hWT hW

theorem wrap_local_criterion_powerless
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    {W : Finset α} (hW : Realizable W)
    (hsupp : ∀ F, Bad F → F ⊆ W) :
    ∀ F, ¬ Bad F :=
  local_criterion_powerless Realizable Bad hsound hW hsupp

theorem wrap_forbidden_meets_both_residues
    (Realizable : Finset α → Prop) (Bad : Finset α → Prop)
    (hsound : ∀ A, Realizable A → ∀ F, Bad F → ¬ F ⊆ A)
    {T W₁ W₂ F : Finset α} (hFT : F ⊆ T)
    (h₁ : Realizable W₁) (h₂ : Realizable W₂) (hF : Bad F) :
    (F ∩ (T \ W₁)).Nonempty ∧ (F ∩ (T \ W₂)).Nonempty :=
  forbidden_meets_both_residues Realizable Bad hsound hFT h₁ h₂ hF

theorem wrap_witness_23 : 23 - 17 = 6 ∧ 39 - 33 = 6 :=
  witness_23

example : True := trivial
#print axioms wrap_F2
end Erdos634.Draft.LocalCriterionBoundWrap
