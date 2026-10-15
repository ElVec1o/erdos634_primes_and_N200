import Erdos634.ChainWalk

namespace Erdos634.Draft.ChainWalkWrap

open Erdos634.ChainWalk

theorem cw_telescope (n : ℕ) (hn : 1 ≤ n) (L R : ℕ → ℝ) (hcontig : ∀ j, j + 1 < n → R j = L (j + 1)) :
    ∑ j ∈ Finset.range n, (R j - L j) = R (n - 1) - L 0 :=
  telescope n hn L R hcontig

theorem cw_chain_walk (n : ℕ) (hn : 1 ≤ n) (L R : ℕ → ℝ) (a b c : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcontig : ∀ j, j + 1 < n → R j = L (j + 1))
    (hlen : ∀ j ∈ Finset.range n, R j - L j ∈ ({a, b, c} : Finset ℝ)) :
    R (n - 1) - L 0
      = ((Finset.range n).filter (fun j => R j - L j = a)).card * a
        + ((Finset.range n).filter (fun j => R j - L j = b)).card * b
        + ((Finset.range n).filter (fun j => R j - L j = c)).card * c :=
  chain_walk n hn L R a b c hab hac hbc hcontig hlen

theorem cw_count_pos (n : ℕ) (len : ℕ → ℝ) (a : ℝ) (j : ℕ) (hj : j ∈ Finset.range n)
    (hja : len j = a) :
    0 < ((Finset.range n).filter (fun i => len i = a)).card :=
  count_pos n len a j hj hja

example : cw_count_pos = count_pos := rfl

#print axioms cw_chain_walk

end Erdos634.Draft.ChainWalkWrap
