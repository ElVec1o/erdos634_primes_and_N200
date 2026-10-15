import Erdos634.ChainOrder

namespace Erdos634.Draft.ChainOrderWrap

open Erdos634.ChainOrder Set

theorem co_no_gap_in_sorted_cover (n : ℕ) (L R : ℕ → ℝ) (a b c : ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hnd : ∀ j < n, L j ≤ R j)
    (hcov : Icc a b ⊆ ⋃ j ∈ Finset.range n, Icc (L j) (R j))
    (hsub : ∀ j, j < n → Icc (L j) (R j) ⊆ Icc a b)
    (hsorted : ∀ i j, i ≤ j → j < n → L i ≤ L j)
    (hreach : ∀ j ≤ k, R j ≤ c) (hlt : c < L (k + 1)) : False :=
  no_gap_in_sorted_cover n L R a b c k hk1 hnd hcov hsub hsorted hreach hlt

theorem co_reach_next (n : ℕ) (L R : ℕ → ℝ) (a b : ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hnd : ∀ j < n, L j ≤ R j)
    (hcov : Icc a b ⊆ ⋃ j ∈ Finset.range n, Icc (L j) (R j))
    (hsub : ∀ j, j < n → Icc (L j) (R j) ⊆ Icc a b)
    (hsorted : ∀ i j, i ≤ j → j < n → L i ≤ L j) :
    ∃ j ≤ k, L (k + 1) ≤ R j :=
  reach_next n L R a b k hk1 hnd hcov hsub hsorted

example : co_reach_next = reach_next := rfl

#print axioms co_no_gap_in_sorted_cover

end Erdos634.Draft.ChainOrderWrap
