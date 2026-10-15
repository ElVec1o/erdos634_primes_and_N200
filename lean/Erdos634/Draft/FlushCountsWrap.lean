import Erdos634.FlushCounts

namespace Erdos634.Draft.FlushCountsWrap

open Erdos634.FlushCounts Erdos634.Geometry Erdos634.FlushJoin Finset

variable {N : ℕ} (D : CongruentDissection N)

/-- Thin wrapper: each tile edge length belongs to the model's three-element side set. -/
theorem wrap_sideLen_eq_or (e : Fin N × Fin 3) :
    sideLen D.toDissection e = dist (D.model.pts 0) (D.model.pts 1) ∨
    sideLen D.toDissection e = dist (D.model.pts 2) (D.model.pts 0) ∨
    sideLen D.toDissection e = dist (D.model.pts 1) (D.model.pts 2) :=
  sideLen_eq_or D e

/-- Thin wrapper: the wall-length decomposition into model-side counts. -/
theorem wrap_exists_counts_of_wall (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (P Q : Plane)
    (hPQ : P ≠ Q)
    (hS : segment ℝ P Q ⊆ {y | f y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hsub : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q) :
    ∃ na nb nc : ℕ,
      na * dist (D.model.pts 0) (D.model.pts 1)
        + nb * dist (D.model.pts 2) (D.model.pts 0)
        + nc * dist (D.model.pts 1) (D.model.pts 2) = dist P Q :=
  exists_counts_of_wall (D := D) f hf c P Q hPQ hS hint hwall hsub

example : True := trivial

#print axioms wrap_sideLen_eq_or
#print axioms wrap_exists_counts_of_wall

end Erdos634.Draft.FlushCountsWrap
