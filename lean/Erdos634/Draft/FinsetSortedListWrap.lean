import Erdos634.FinsetSortedList

namespace Erdos634.Draft.FinsetSortedListWrap
open Erdos634.ChordTraceReal

theorem wrap_exists_sorted_list_of_finset {N : ℕ} (key : Fin N → ℝ) :
    ∀ T : Finset (Fin N), ∃ L : List (Fin N),
      L.toFinset = T ∧ L.Nodup ∧ L.length = T.card ∧
      (∀ i j, (hi : i < L.length) → (hj : j < L.length) → i ≤ j →
        key (L.get ⟨i, hi⟩) ≤ key (L.get ⟨j, hj⟩)) :=
  exists_sorted_list_of_finset key

example : True := trivial
#check @wrap_exists_sorted_list_of_finset

end Erdos634.Draft.FinsetSortedListWrap
