import Erdos634.ApexRigidity

/-!
# Bound on p: arithmetic kernel

pe + 2 ≤ f and p ≤ 1 on f = 2e+1.

* `ApexRigidity.side_p_bound`: pe + 2 ≤ f assuming n + pe = f, n ≥ 2 (arithmetic).
* `ApexRigidity.p_le_one_of_tight`: p ≤ 1 when pe + 2 ≤ 2e + 1 (arithmetic).

The geometric premise n ≥ 2 (that n_c ≥ 2 in the side walk) requires
the placement layer and is not part of this file.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PBoundWrap

/-- Arithmetic core of pe + 2 ≤ f: if n + pe = f with n ≥ 2, then pe + 2 ≤ f. -/
theorem p_bound_arithmetic {p e f n : ℕ}
    (hn : n + p * e = f) (h2 : 2 ≤ n) : p * e + 2 ≤ f :=
  Erdos634.ApexRigidity.side_p_bound hn h2

/-- On the tight subfamily (f = 2e+1): pe + 2 ≤ f forces p ≤ 1. -/
theorem p_le_one_of_tight_arithmetic {p e : ℕ}
    (h : p * e + 2 ≤ 2 * e + 1) : p ≤ 1 :=
  Erdos634.ApexRigidity.p_le_one_of_tight h

/-- Non-vacuity: both hypotheses are satisfiable. -/
theorem p_bound_witness : ∃ (p e f n : ℕ), n + p * e = f ∧ 2 ≤ n :=
  ⟨1, 2, 5, 3, by norm_num, by norm_num⟩

#print axioms p_bound_arithmetic
#print axioms p_le_one_of_tight_arithmetic

end Erdos634.Draft.PBoundWrap
