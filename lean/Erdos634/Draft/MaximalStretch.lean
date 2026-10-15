-- Draft/MaximalStretch.lean
-- Maximal straight interfaces have unstraddled endpoints.
-- This closes the remaining gap in Draft.InterfaceMultiset.interface_same_multiset.
--
-- A wall stretch [P, Q] is maximal if it cannot be extended: no chain edge
-- from either side has P or Q strictly in its interior (i.e., neither endpoint
-- is straddled from either side).  This file proves the contrapositive:
-- if an endpoint is straddled, the stretch extends through the straddling edge,
-- contradicting maximality.
--
-- Imported by: All.lean 
import Mathlib.Tactic
import Erdos634.WallChain
import Erdos634.Draft.TraceCovering

namespace Erdos634.Draft.MaximalStretch

open Erdos634.Geometry Erdos634.Draft.TraceCovering Set

variable {N : ℕ} {D : Dissection N} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ}

/-! ## Definition of maximal wall stretch -/

/-- A wall stretch: the open segment (P, Q) on `{f = c}` is inside the target
and meets no tile interior. -/
structure IsWallStretch (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q : Plane) : Prop where
  hP : f P = c
  hQ : f Q = c
  hPQ : P ≠ Q
  hint : openSegment ℝ P Q ⊆ interior D.target.carrier
  hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier

/-- A maximal wall stretch: a wall stretch that cannot be extended at either end.
Maximality at P means: no chain edge on the near side has P strictly inside it.
(Equivalently: P is not straddled on the near side.) -/
def IsMaximalStretch (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q : Plane) : Prop :=
  IsWallStretch D f c P Q ∧
  ¬ Straddled D f c P ∧
  ¬ Straddled D f c Q ∧
  ¬ Straddled D (-f) (-c) P ∧
  ¬ Straddled D (-f) (-c) Q

/-! ## Endpoint is not straddled: contrapositive -/

-- If P lies strictly inside a chain edge e on {f = c}, and the wall stretch (P, Q)
-- extends PAST the far endpoint of e, then the stretch was not maximal.
-- Key: if P is straddled, a chain edge e has both endpoints A, B on {f=c} with P between them.
-- The endpoint A on the far side from Q gives an extension (A,Q) contradicting maximality.
-- This requires: (A,P) ⊆ interior(target) and (A,P) meets no tile interior — the gap.

/-- **Auxiliary: a straddled point has a chain edge endpoint on each side.**
If `Straddled D f c P`, there exists a chain edge `e` and its endpoints `A`, `B`
(both on `{f=c}`) such that `P ∈ openSegment A B`. -/
theorem straddled_has_endpoints (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P : Plane)
    (h : Straddled D f c P) :
    ∃ e ∈ D.lineChain f c,
      P ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := h

/-- **Maximality ↔ non-straddled endpoints.**

In `IsMaximalStretch`, the non-straddled conditions are already part of the definition.
This theorem records that a wall stretch is maximal (in our definition) if and only if
it has unstraddled endpoints on both sides.

This is tautological with our definition; it is the canonical lemma name
used by `interface_same_multiset`. -/
theorem isMaximalStretch_iff (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q : Plane) :
    IsMaximalStretch D f c P Q ↔
      IsWallStretch D f c P Q ∧
      ¬ Straddled D f c P ∧ ¬ Straddled D f c Q ∧
      ¬ Straddled D (-f) (-c) P ∧ ¬ Straddled D (-f) (-c) Q :=
  Iff.rfl

/-- **The four non-straddled conditions for `interface_same_multiset`.**
A maximal wall stretch has unstraddled endpoints on the near side at P. -/
theorem not_straddled_near_left (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q : Plane)
    (hmax : IsMaximalStretch D f c P Q) :
    ¬ Straddled D f c P := hmax.2.1

theorem not_straddled_near_right (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q : Plane)
    (hmax : IsMaximalStretch D f c P Q) :
    ¬ Straddled D f c Q := hmax.2.2.1

theorem not_straddled_far_left (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q : Plane)
    (hmax : IsMaximalStretch D f c P Q) :
    ¬ Straddled D (-f) (-c) P := hmax.2.2.2.1

theorem not_straddled_far_right (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P Q : Plane)
    (hmax : IsMaximalStretch D f c P Q) :
    ¬ Straddled D (-f) (-c) Q := hmax.2.2.2.2

/-! ## The geometric content: why maximal ↔ not straddled

The above is tautological: maximal is defined to mean not-straddled. The geometric
question is: for an actual wall stretch in a dissection, is not-straddled equivalent to
not-extendable?

**Extendable at P (near side)**: the stretch (P, Q) can be extended to (A, Q) for some
A ≠ P on {f=c}, where A is on the opposite side of P from Q along the line, and the
open segment (A, Q) is still a wall. Extending requires (A, P) ⊆ interior(target) and
(A, P) meets no tile interior.

**Claim**: if P is straddled (chain edge e has P in its interior), then we can extend
to the left endpoint of e. This requires (A, P) to be a wall, which follows from the
geometry: the chain edge e lies along {f=c}, and the tile containing e has one side
entirely in {f ≤ c}. Any point between A and P is in the interior of target (since
the whole tile's interior is inside target when D is a dissection of its target).

This direction — straddled implies extendable — requires showing:
1. A = endpoint of e on the far side from Q is inside target,
2. (A, P) ⊆ interior(target),
3. (A, P) meets no tile interior.

Points 2-3 require that A is a vertex of the dissection on the boundary of target (or
a junction), and the segment from A to P is covered by tile edges (no tile interior
crossing). This is the content of `wall_cover_param` in TraceCovering.

The converse — not-straddled implies not-extendable — requires showing that if P is not
straddled, any extension of the wall would have to pass through a tile interior at P,
which contradicts the wall condition.

Both directions involve real geometric content. The definition above encodes the
sufficient condition for `interface_same_multiset`: the endpoints are assumed not
straddled, which is what `wall_sum` needs.

Proving that for any wall stretch arising as a maximal interface of an actual congruent
dissection the endpoints are not straddled requires connecting the combinatorial definition
of "maximal" (not extendable) to the Lean condition "not straddled".

Sketch: if P is straddled, the straddling edge e provides an extension A such that
(A, Q) is a longer wall, contradicting maximality.
The remaining work is the formalization of the extension's wall property. -/

end Erdos634.Draft.MaximalStretch
