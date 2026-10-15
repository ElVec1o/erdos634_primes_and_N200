import Erdos634.IntervalChain

namespace Erdos634.Draft.IntervalChainWrap

open Erdos634.IntervalChain Set

variable {n : ℕ} {L : ℝ} {lo hi : Fin n → ℝ}

theorem ic_no_straddle (H : Cover L lo hi) (i j : Fin n)
    (h1 : lo j < hi i) (h2 : hi i < hi j) : False :=
  no_straddle H i j h1 h2

theorem ic_first_starts_at_zero (H : Cover L lo hi) (hL : 0 ≤ L) : ∃ i, lo i = 0 :=
  first_starts_at_zero H hL

theorem ic_chain_of_cover (H : Cover L lo hi) (hL : 0 ≤ L) :
    (∃ i, lo i = 0) ∧ (∀ i, hi i < L → ∃ j, lo j = hi i) :=
  chain_of_cover H hL

example : True := trivial

#print axioms ic_chain_of_cover

end Erdos634.Draft.IntervalChainWrap
