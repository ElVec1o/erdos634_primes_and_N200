import Erdos634.DirectionGroup

/-!
# Direction group: algebraic kernels

Every edge direction in a tiling by angle-`(α,β,γ)` tiles is an
integer multiple of `γ` modulo `π`, for the base-β branch (`3α + 2β = π`).

The direction group `ℤ²/⟨p,q⟩` classifies branches:
  - base-β `(p,q) = (3,2)`, `gcd = 1` → group `ℤ` (torsion-free, generator is `γ`)
  - `γ = 2α` `(p,q) = (3,1)`, `gcd = 1` → group `ℤ` (torsion-free)
  - special-angle branches: `gcd = 2` or `3` → group `ℤ ⊕ ℤ/d` with torsion

The algebraic content (the structure of `ℤ²/⟨(p,q)⟩`, surjectivity and
kernel of the label map, and the torsion characterization) is in `DirectionGroup.lean`.  This module wraps it;
it does not connect `Dissection.dirSet` (the set of edge directions of a real tiling) to the abstract structure.

Standard axioms, no sorry.
-/

namespace Erdos634.Draft.DirGroupWrap

open Erdos634.DirectionGroup

/-- The base-β label: for the branch `3α + 2β = π`, the direction label is `L(x,y) = 2x − 3y`. -/
theorem basebeta_label (x y : ℤ) : L 3 2 x y = 2 * x - 3 * y :=
  L_basebeta x y

/-- The base-β relation vector `(3,2)` is primitive (`gcd(3,2) = 1`). -/
theorem basebeta_primitive : IsCoprime (3 : ℤ) 2 :=
  basebeta_coprime

/-- The `γ = 2α` relation vector `(3,1)` is also primitive. -/
theorem gamma_two_alpha_primitive : IsCoprime (3 : ℤ) 1 :=
  gamma_two_alpha_coprime

/-- Every integer is a label in the base-β direction group: the free part is all of `ℤ`. -/
theorem basebeta_label_surjective (n : ℤ) : ∃ x y : ℤ, L 3 2 x y = n :=
  L_surjective basebeta_coprime n

/-- The label `L 3 2` vanishes exactly on multiples of `(3,2)`, i.e., the kernel is `⟨(3,2)⟩`. -/
theorem basebeta_label_kernel (x y : ℤ) :
    L 3 2 x y = 0 ↔ ∃ k : ℤ, x = 3 * k ∧ y = 2 * k :=
  L_ker basebeta_coprime (by norm_num) x y

/-- The base-β direction group `ℤ²/⟨(3,2)⟩` is torsion-free: the only torsion is trivial. -/
theorem basebeta_torsion_free (x y : ℤ)
    (htors : ∃ n : ℤ, n ≠ 0 ∧ ∃ k : ℤ, n * x = 1 * 3 * k ∧ n * y = 1 * 2 * k) :
    ∃ m : ℤ, x = 3 * m ∧ y = 2 * m :=
  (torsion_iff basebeta_coprime (by norm_num) 1 one_ne_zero x y).mp htors

/-- For the `d = 1` case, torsion order 1 means every torsion class is 0. -/
theorem basebeta_torsion_order_one (k : ℤ) :
    (∃ j : ℤ, k * 3 = 1 * 3 * j ∧ k * 2 = 1 * 2 * j) ↔ (1 : ℤ) ∣ k :=
  torsion_order (by norm_num) 1 k

#print axioms basebeta_label
#print axioms basebeta_label_surjective
#print axioms basebeta_label_kernel
#print axioms basebeta_torsion_free

end Erdos634.Draft.DirGroupWrap
