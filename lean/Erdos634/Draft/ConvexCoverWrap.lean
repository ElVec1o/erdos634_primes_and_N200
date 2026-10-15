import Erdos634.ConvexCover

/-!
# ConvexCover: covering from a.e. disjointness, positivity and a volume count, wrapper
Key results: `aedisjoint_of_interiors`, `volume_pos_of_isOpen`,
`volume_iUnion_eq_sum`, `covers_of_volume`.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.ConvexCoverWrap
open Erdos634.ConvexCover Erdos634.Geometry MeasureTheory

variable {N : ℕ}

/-- Disjoint interiors imply a.e. disjointness. -/
theorem wrap_aedisjoint_of_interiors {t₁ t₂ : Tri}
    (h : Disjoint (interior t₁.carrier) (interior t₂.carrier)) :
    AEDisjoint volume t₁.carrier t₂.carrier :=
  aedisjoint_of_interiors h

/-- A nonempty open set has positive volume. -/
theorem wrap_volume_pos_of_isOpen {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < volume U :=
  volume_pos_of_isOpen hU hne

/-- The union of pieces has the sum of their volumes, given pairwise disjoint interiors. -/
theorem wrap_volume_iUnion_eq_sum (tile : Fin N → Tri)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier)) :
    volume (⋃ i, (tile i).carrier) = ∑ i, volume (tile i).carrier :=
  volume_iUnion_eq_sum tile hdisj

/-- The certified-search bridge: (C2) + (C3) + (C4) imply pointwise covering. -/
theorem wrap_covers_of_volume (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume target.carrier) :
    (⋃ i, (tile i).carrier) = target.carrier :=
  covers_of_volume target tile hsub hdisj hvol

example : True := trivial

#print axioms wrap_aedisjoint_of_interiors
#print axioms wrap_volume_pos_of_isOpen
#print axioms wrap_volume_iUnion_eq_sum
#print axioms wrap_covers_of_volume

end Erdos634.Draft.ConvexCoverWrap
