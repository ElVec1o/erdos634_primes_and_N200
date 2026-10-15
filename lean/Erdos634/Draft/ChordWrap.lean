import Erdos634.Frontier
import Erdos634.Dissection

/-!
# The chord at the last junction: wrapper

Let f=2e+1 and let a side have p=2. The apex c-tile presents β at
J_{2f} with its a-ray pointing along the horizontal, and J_{2f} lies at height fraction 2e/f,
so the horizontal chord from J_{2f} to the opposite side has length exactly e(3f²-e²)(f-2e)/f = eN/f.
At (3,7) this is 414/7.

Moreover the tiles meeting that chord from either side meet it in whole edges: a tile whose interior
misses the chord line lies in a closed half-plane of it, so its contact is a face (tile_contact_face),
and at a non-vertex point that face is an edge (contact_is_edge). Disjointness of tile interiors then
makes the covering a chain starting at the end of the c-tile's a-edge, and convexity of the target
keeps every endpoint within the chord.

Lean content:
1. **`chord_chord_length`**: chord length identity (1 - 2e/f) · eN = eN(f-2e)/f (`Frontier.chord_length`).
2. **`chord_height_identity`**: height identity 2A(f-2e)/f = 2A/f ↔ f=2e+1 (`Frontier.height_identity`).
3. **`chord_tile_contact_face`**: tile contact with a hyperplane is a face (`Dissection.tile_contact_face`).
4. **`chord_contact_is_edge`**: at a non-vertex point the face is an edge (`Dissection.contact_is_edge`).

Only the chord length arithmetic and the contact lemmas are formalized.  J_{2f} as a geometric
junction object (placed by the p=2 cascade) is not defined in Lean; the chord direction, endpoint
convexity, and the chain-covering conclusion need placement.
-/

namespace Erdos634.Draft.ChordWrap

open Erdos634.Frontier Erdos634.Geometry Erdos634.Geometry.Dissection

/-- lem:chord (length): chord length at height fraction 2e/f is (1-2e/f)·eN = eN(f-2e)/f. -/
theorem chord_chord_length (e f N : ℚ) (he : 0 < e) (hf : 0 < f) :
    (1 - 2 * e / f) * (e * N) = e * N * (f - 2 * e) / f :=
  chord_length e f N he hf

/-- lem:chord (tight family): the height identity 2A(f-2e) = 2A ↔ f=2e+1. -/
theorem chord_height_identity (A e f : ℚ) (hA : A ≠ 0) :
    2 * A * (f - 2 * e) = 2 * A ↔ f = 2 * e + 1 :=
  height_identity A e f hA

/-- lem:chord (tile contact): intersection of a tile with a supporting hyperplane is a face
(Dissection.tile_contact_face). -/
theorem chord_tile_contact_face (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) :
    {x ∈ T.carrier | f x = c} =
    convexHull ℝ (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane) :=
  tile_contact_face T f c hle

/-- lem:chord (edge contact): at a non-vertex point a face contact is an edge
(Dissection.contact_is_edge). -/
theorem chord_contact_is_edge (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) {x : Plane} (hx : x ∈ T.carrier) (hfx : f x = c)
    (hxv : ∀ k, x ≠ T.pts k) :
    ∃ k, {y ∈ T.carrier | f y = c} = T.edge k :=
  contact_is_edge T f c hf hle hx hfx hxv

#print axioms chord_chord_length
#print axioms chord_height_identity
#print axioms chord_tile_contact_face
#print axioms chord_contact_is_edge

end Erdos634.Draft.ChordWrap
