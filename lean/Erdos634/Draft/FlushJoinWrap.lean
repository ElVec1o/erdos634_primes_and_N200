import Erdos634.FlushJoin

namespace Erdos634.Draft.FlushJoinWrap

open Erdos634.FlushJoin Erdos634.Geometry Erdos634.LineParam Set

variable {N : ℕ}

/-- Thin wrapper: the side lengths on a wall chain sum to the wall length. -/
theorem wrap_sum_sideLen_eq_dist
    (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    (hsub : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ u v) :
    ∑ e ∈ D.lineChain f c, sideLen D e = dist u v :=
  sum_sideLen_eq_dist D f hf c u v huv hS hint hwall hsub

/-- Thin wrapper: the line chain is nonempty whenever a wall segment exists. -/
theorem wrap_lineChain_nonempty_of_join
    (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    (hsub : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ u v) :
    (D.lineChain f c).Nonempty :=
  lineChain_nonempty_of_join D f hf c u v huv hS hint hwall hsub

example : True := trivial

#print axioms wrap_lineChain_nonempty_of_join

end Erdos634.Draft.FlushJoinWrap
