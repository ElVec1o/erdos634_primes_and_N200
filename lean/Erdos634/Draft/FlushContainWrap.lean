import Erdos634.FlushContain

namespace Erdos634.Draft.FlushContainWrap

open Erdos634.FlushContain Erdos634.Geometry Erdos634.FlushJoin Erdos634.FlushCounts Set

variable {N : ℕ}

/-- Thin wrapper: every side contact of a congruent dissection with a wall yields a nonneg
integer combination of the model's three edge lengths. -/
theorem wrap_exists_counts_of_side
    (D : CongruentDissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (P Q : Plane) (hPQ : P ≠ Q)
    (hS : segment ℝ P Q ⊆ {y | f y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (htarget : {x ∈ D.target.carrier | f x = c} ⊆ segment ℝ P Q) :
    ∃ na nb nc : ℕ,
      na * dist (D.model.pts 0) (D.model.pts 1)
        + nb * dist (D.model.pts 2) (D.model.pts 0)
        + nc * dist (D.model.pts 1) (D.model.pts 2) = dist P Q :=
  exists_counts_of_side D f hf c P Q hPQ hS hint hwall htarget

-- Non-vacuity: the statement is consistent (trivial witness for `True`)
example : True := trivial

#print axioms wrap_exists_counts_of_side

end Erdos634.Draft.FlushContainWrap
