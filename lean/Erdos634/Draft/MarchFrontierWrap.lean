import Erdos634.MarchFrontier
namespace Erdos634.Draft.MarchFrontierWrap
open Erdos634.MarchFrontier

theorem wrap_noTwoZeros_succ_succ (n : ℕ) :
    noTwoZeros (n + 2) = noTwoZeros (n + 1) + noTwoZeros n :=
  noTwoZeros_succ_succ n

theorem wrap_frontier_values :
    noTwoZeros 2 = 3 ∧ noTwoZeros 3 = 5 ∧ noTwoZeros 4 = 8 ∧ noTwoZeros 5 = 13 :=
  frontier_values

theorem wrap_split_by_last (n : ℕ) :
    noTwoZeros (n + 2) = noTwoZeros (n + 1) + noTwoZeros n :=
  split_by_last n

theorem wrap_frontier_induction (S : ℕ → Prop) (h0 : S 0) (h1 : S 1)
    (hstep : ∀ n, S n → S (n + 1) → S (n + 2)) : ∀ n, S n :=
  frontier_induction S h0 h1 hstep

theorem wrap_frontier_grows (n : ℕ) : noTwoZeros (n + 1) ≤ noTwoZeros (n + 2) :=
  frontier_grows n

example : True := trivial
#print axioms wrap_frontier_induction
#print axioms wrap_frontier_grows
end Erdos634.Draft.MarchFrontierWrap
