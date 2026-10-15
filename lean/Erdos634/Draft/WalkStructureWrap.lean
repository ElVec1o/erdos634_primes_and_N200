import Erdos634.WalkStructure

/-!
# Base and side walk structure: wrapper

Key results:
- `base_P_residue`: f ∣ P − j·e (base walk)
- `side_Q_residue`: f ∣ Q (side walk)
- `side_no_b`: the side walk has q = 0 (no b-edges)
- `base_level`: p·e + j·f + R = 2e (level equation)

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.WalkStructureWrap

open Erdos634.WalkStructure

theorem ws_base_P_residue (e f P R j : ℤ) (hcop : IsCoprime e f)
    (h : P * e + j * (f ^ 2 - e ^ 2) + R * f = 2 * e * f) : f ∣ P - j * e :=
  base_P_residue e f P R j hcop h

theorem ws_side_Q_residue (e f P Q R : ℤ) (hcop : IsCoprime e f)
    (h : P * (e * f) + Q * (f ^ 2 - e ^ 2) + R * f ^ 2 = f ^ 3) : f ∣ Q :=
  side_Q_residue e f P Q R hcop h

theorem ws_side_no_b (e f P R q p : ℤ) (he : 1 ≤ e) (hef : e < f) (hP0 : 0 ≤ P)
    (hP : P = q * e + f * p) (hR : 1 ≤ R) (hq : 0 ≤ q)
    (hlev : p * e + q * f + R = f) : q = 0 :=
  side_no_b e f P R q p he hef hP0 hP hR hq hlev

theorem ws_base_level (e f P R j p : ℤ) (hf : f ≠ 0) (hP : P = j * e + f * p)
    (h : P * e + j * (f ^ 2 - e ^ 2) + R * f = 2 * e * f) : p * e + j * f + R = 2 * e :=
  base_level e f P R j p hf hP h

/-- Non-vacuity: IsCoprime 1 2 is trivially satisfied. -/
theorem ws_witness : IsCoprime (1 : ℤ) 2 := ⟨-1, 1, by ring⟩

#print axioms ws_base_P_residue
#print axioms ws_side_no_b
#print axioms ws_base_level

end Erdos634.Draft.WalkStructureWrap
