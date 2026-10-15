import Erdos634.OrderForcing

/-!
# The chain never needs the apex line: arithmetic kernel

When traversing the collision figure, the chain indices
k stay strictly below f, so the apex line (at position f) is never needed.

Key arithmetic fact in `OrderForcing.lean`:

**`chain_needs_small_lines`**: for 3 ≤ bp ≤ f and k ≤ bp−1, k < f.
This is an `omega` step.

Also wrapped: `climber_mandatory` (v₁ ≥ 1 in every tiling) and
`vertex_census` (v₁ = 1 + n₂ + v₃ + 2v₄) as they share the OrderForcing module.

This file contains only the arithmetic core; the statement about which lines the collision figure
consumes (brick/mate structure) is not formalized here.  Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.NoapexWrap

open Erdos634.OrderForcing

/-- lem:noapexline (arithmetic core): chain index k ≤ bp−1 ≤ f−1 implies k < f.
    This is `chain_needs_small_lines`; the apex line is at position f, never reached. -/
theorem noapex_chain_small {f bp k : ℕ} (hf : 3 ≤ f) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hk : k ≤ bp - 1) : k < f :=
  chain_needs_small_lines hf hb3 hbf hk

/-- Vertex census identity: v₁ = 1 + n₂ + v₃ + 2·v₄ (from the three corner-balance equations). -/
theorem noapex_vertex_census {N n1 n2 v1 v2 v3 v4 : ℕ}
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) :
    v1 = 1 + n2 + v3 + 2 * v4 :=
  vertex_census ha hb hg

/-- Climber mandatory: v₁ ≥ 1 in every tiling of the base-β target. -/
theorem noapex_climber_mandatory {N n1 n2 v1 v2 v3 v4 : ℕ}
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) : 1 ≤ v1 :=
  climber_mandatory ha hb hg

/-- Non-vacuity: at f=3, bp=3, k=1: k ≤ bp−1=2 and bp ≤ f=3, so k=1 < 3. -/
theorem noapex_chain_witness : (1 : ℕ) ≤ 3 - 1 ∧ (3 : ℕ) ≤ 3 ∧ (1 : ℕ) < 3 := by norm_num

/-- Non-vacuity for vertex_census: (N=9, n1=0, n2=2, v1=3, v2=0, v3=0, v4=0). -/
theorem noapex_census_witness : (3 : ℕ) + 0 + 3*2 + 2*0 + 4*0 + 6*0 = 9 ∧
    (2 : ℕ) + 0 + 2*2 + 3 + 2*0 + 3*0 + 4*0 = 9 ∧
    (0 : ℕ) + 3*3 + 2*0 + 0 = 9 ∧ (3 : ℕ) = 1 + 2 + 0 + 2*0 := by norm_num

#print axioms noapex_chain_small
#print axioms noapex_vertex_census
#print axioms noapex_climber_mandatory

end Erdos634.Draft.NoapexWrap
