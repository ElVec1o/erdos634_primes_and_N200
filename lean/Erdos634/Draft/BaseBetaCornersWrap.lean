import Erdos634.BaseBetaCorners

/-!
# Vertex figure and b-unsplittability arithmetic kernels: wrapper

Re-exports results of `BaseBetaCorners`:

1. **`corner_beta_unique`**: 2p−3q+r=−3, q+r=1 forces p=0,q=1,r=0 (base corner).
2. **`corner_apex_unique`**: 2p−3q+r=6, q+r=0 forces p=3,q=0,r=0 (apex).
3. **`pi_vertex_figures`**: 2p−3q+r=0, q+r=2 ⟹ (p,q,r) ∈ {(1,0,1),(3,2,0)}.
4. **`pi_vertex_gamma_le_one`**: same hypotheses ⟹ r≤1 (no double γ at interior boundary).
5. **`b_unsplittable`**: x·a+y·b+z·c=b forces (0,1,0); the b-edge is unsplittable.

Pure arithmetic.  No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseBetaCornersWrap

open Erdos634.BaseBetaCorners

/-- Base corner is a single β-tile: 2p−3q+r=−3, q+r=1 ⟹ (0,1,0). -/
theorem corners_beta_unique (p q r : ℕ)
    (h1 : 2 * (p : ℤ) - 3 * q + r = -3) (h2 : q + r = 1) :
    p = 0 ∧ q = 1 ∧ r = 0 :=
  corner_beta_unique p q r h1 h2

/-- Apex carries exactly three α-tiles: 2p−3q+r=6, q+r=0 ⟹ (3,0,0). -/
theorem corners_apex_unique (p q r : ℕ)
    (h1 : 2 * (p : ℤ) - 3 * q + r = 6) (h2 : q + r = 0) :
    p = 3 ∧ q = 0 ∧ r = 0 :=
  corner_apex_unique p q r h1 h2

/-- π-vertex figures: 2p−3q+r=0, q+r=2 ⟹ (p,q,r)∈{(3,2,0),(1,1,1)}. -/
theorem corners_pi_vertex (p q r : ℕ)
    (h1 : 2 * (p : ℤ) - 3 * q + r = 0) (h2 : q + r = 2) :
    (p = 3 ∧ q = 2 ∧ r = 0) ∨ (p = 1 ∧ q = 1 ∧ r = 1) :=
  pi_vertex_figures p q r h1 h2

/-- No double γ at interior boundary: 2p−3q+r=0, q+r=2 ⟹ r≤1. -/
theorem corners_pi_vertex_gamma_le_one (p q r : ℕ)
    (h1 : 2 * (p : ℤ) - 3 * q + r = 0) (h2 : q + r = 2) : r ≤ 1 :=
  pi_vertex_gamma_le_one p q r h1 h2

/-- b-edge unsplittable: x·a+y·b+z·c=b forces (0,1,0). -/
theorem corners_b_unsplittable (e f b na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = b) :
    na = 0 ∧ nb = 1 ∧ nc = 0 :=
  b_unsplittable e f b na nb nc he hef hcop hb heq

/-- Non-vacuity: corner_beta_unique: (0,1,0) satisfies 2·0−3·1+0=−3, 1+0=1. -/
theorem corners_witness : 2 * (0:ℤ) - 3 * 1 + 0 = -3 ∧ (1:ℕ) + 0 = 1 := by norm_num

#print axioms corners_beta_unique
#print axioms corners_apex_unique
#print axioms corners_b_unsplittable

end Erdos634.Draft.BaseBetaCornersWrap
