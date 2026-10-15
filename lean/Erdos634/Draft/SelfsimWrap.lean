import Erdos634.SecondEdge

/-!
# The descent is self-similar: wrapper

Suppose a tile Z lays a c-edge of an equal side between
consecutive junctions J' (nearer the apex) and J, and presents α at J'. Let W be its third vertex.
Then W lies exactly on the chord C through J; the segment JW is Z's a-edge, of length a, lying
along C; and Z presents β at J and γ at W.

The proof uses: the drop from J' to W is b·cos(α/2) = drop from J' to J = c·cos(3α/2) (the apex identity),
and the horizontal offsets differ by c·sin(3α/2) − b·sin(α/2) = a. The angles at J and W
are those opposite b and c, namely β and γ.

Lean content:
1. **`selfsim_drop_uniform`**: the drop δ = (k+1)δ − kδ is constant across levels
   (`SecondEdge.selfsim_drop`).
2. **`selfsim_configuration_uniform`**: the drop at level j equals the drop at level k
   (`SecondEdge.selfsim_uniform`).

The statements are drop-uniformity arithmetic; tile Z, the junctions J'/J and the geometric instantiation
in a real dissection are not part of this module.
0 sorry, standard axioms.
-/

namespace Erdos634.Draft.SelfsimWrap

open Erdos634.SecondEdge

/-- prop:selfsim (drop): the drop from the k-th junction to the (k+1)-st is δ (selfsim_drop). -/
theorem selfsim_drop_uniform (δ : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * δ - k * δ = δ :=
  selfsim_drop δ k

/-- prop:selfsim (uniformity): the drop at level j equals the drop at level k (selfsim_uniform). -/
theorem selfsim_configuration_uniform (δ : ℝ) (j k : ℕ) :
    ((j + 1 : ℝ) * δ - j * δ) = ((k + 1 : ℝ) * δ - k * δ) :=
  selfsim_uniform δ j k

#print axioms selfsim_drop_uniform
#print axioms selfsim_configuration_uniform

end Erdos634.Draft.SelfsimWrap
