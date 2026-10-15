import Erdos634.CoversGeneral

/-!
# CoversGeneral: covering from volume for general convex compact targets, wrapper
Key results: `covers_of_volume_general`, `covers_of_volume_tri`.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.CoversGeneralWrap
open Erdos634.Geometry MeasureTheory

variable {N : ℕ}

/-- General covering-from-volume: containment + disjoint interiors + area identity
    force a finite family of triangles to cover any convex compact target with
    nonempty interior and finite volume. -/
theorem wrap_covers_of_volume_general {S : Set Plane}
    (hSconv : Convex ℝ S) (hScompact : IsCompact S)
    (hSint : (interior S).Nonempty) (hSvol : volume S ≠ ⊤)
    (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ S)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume S) :
    (⋃ i, (tile i).carrier) = S :=
  covers_of_volume_general hSconv hScompact hSint hSvol tile hsub hdisj hvol

/-- ConvexCover.covers_of_volume as a corollary of the general statement. -/
theorem wrap_covers_of_volume_tri (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume target.carrier) :
    (⋃ i, (tile i).carrier) = target.carrier :=
  covers_of_volume_tri target tile hsub hdisj hvol

example : True := trivial

#print axioms wrap_covers_of_volume_general
#print axioms wrap_covers_of_volume_tri

end Erdos634.Draft.CoversGeneralWrap
