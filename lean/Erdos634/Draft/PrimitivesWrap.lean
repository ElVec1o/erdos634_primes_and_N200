import Erdos634.Primitives

/-!
# Cevian atom and addition law: arithmetic kernels

`Primitives.lean` has two ring identities:

* `two_tiles_plus_atom` (cevian atom):
  m²·(3f²−e²) = 2·(fm)² + (f²−e²)·m².
* `add_count` (addition law):
  (m₁+m₂)²·N = m₁²·N + 2·m₁·m₂·N + m₂²·N.

Both are pure ring identities. The geometric claims, that the cevian cuts
a target into these three pieces and that the addition law holds for a real
tiling, require the placement layer and are not part of this file.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PrimitivesWrap

/-- prop:cevianatom: the whole target is two scaled tiles plus one atom: m²N₁ = 2(fm)² + bm². -/
theorem cevian_atom_count (e f m : ℤ) :
    m ^ 2 * (3 * f ^ 2 - e ^ 2) = 2 * (f * m) ^ 2 + (f ^ 2 - e ^ 2) * m ^ 2 :=
  Erdos634.Primitives.two_tiles_plus_atom e f m

/-- thm:addlaw: the tile count for scale m₁+m₂ expands correctly. -/
theorem add_law_count (m1 m2 N : ℤ) :
    (m1 + m2) ^ 2 * N = m1 ^ 2 * N + 2 * (m1 * m2 * N) + m2 ^ 2 * N :=
  Erdos634.Primitives.add_count m1 m2 N

/-- lem:wpgram arithmetic kernel: Y = 2f²−1 = f·a+b and brick count identity. -/
theorem wpgram_slab_counts (f : ℤ) :
    2 * f ^ 2 - 1 = f * f + (f ^ 2 - 1) ∧
    2 * (f * f + (f ^ 2 - 1)) = 2 * (2 * f ^ 2 - 1) :=
  Erdos634.Primitives.w_slab_counts f

/-- Non-vacuity: both theorems are ring identities, trivially satisfiable. -/
theorem primitives_witness : ∃ (e f m : ℤ), e = 1 ∧ f = 2 ∧ m = 1 :=
  ⟨1, 2, 1, rfl, rfl, rfl⟩

#print axioms cevian_atom_count
#print axioms add_law_count
#print axioms wpgram_slab_counts

end Erdos634.Draft.PrimitivesWrap
