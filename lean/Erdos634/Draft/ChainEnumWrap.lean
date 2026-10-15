import Erdos634.ChainEnum

namespace Erdos634.Draft.ChainEnumWrap

open Erdos634.ChainEnum

theorem ce_exists_sorted_enum {ι : Type*} [Inhabited ι] (l : List ι) (pos : ι → ℝ)
    (hnodup : l.Nodup) :
    ∃ E : ℕ → ι,
      (∀ i j, i ≤ j → j < l.length → pos (E i) ≤ pos (E j)) ∧
      (∀ i < l.length, E i ∈ l) ∧
      (∀ x ∈ l, ∃ i < l.length, E i = x) ∧
      (∀ i j, i < l.length → j < l.length → E i = E j → i = j) :=
  exists_sorted_enum l pos hnodup

example : True := trivial

#print axioms ce_exists_sorted_enum

end Erdos634.Draft.ChainEnumWrap
