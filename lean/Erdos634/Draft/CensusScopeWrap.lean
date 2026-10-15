import Erdos634.OrderForcing

/-!
# Scope of the vertex census: wrapper

The vertex census identity
  v₁ − v₃ − 2·v₄ − n₂ = 1
is the entire content of corner counting at a base-β target: it is exact on the
three tilings held (N=44 twice and N=99) and does not involve the side structure,
so corner counting alone cannot see the side parameter p.

The identity is `OrderForcing.vertex_census`.
The corollary that v₁ ≥ 1 in every tiling is `OrderForcing.climber_mandatory`.

The claim that the identity does not involve the side structure is not a Lean statement; it
describes what `vertex_census` does not use, which is evident from its type (no side-structure
input).  That the identity is exact on the three tilings is checked by the kernel-checked
instances in Primitives.lean (N44B, N44C, Tiling99) but not wired here.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.CensusScopeWrap

open Erdos634.OrderForcing

/-- The vertex census identity v₁ = 1 + n₂ + v₃ + 2v₄ in any base-β tiling. -/
theorem censusscope_identity {N n1 n2 v1 v2 v3 v4 : ℕ}
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) :
    v1 = 1 + n2 + v3 + 2 * v4 :=
  vertex_census ha hb hg

/-- rem:censusscope corollary: at least one climber vertex in every tiling. -/
theorem censusscope_climber_mandatory {N n1 n2 v1 v2 v3 v4 : ℕ}
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) : 1 ≤ v1 :=
  climber_mandatory ha hb hg

#print axioms censusscope_identity
#print axioms censusscope_climber_mandatory

end Erdos634.Draft.CensusScopeWrap
