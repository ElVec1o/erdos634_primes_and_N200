import Erdos634.EpredColumnKill

/-!
# The e=f−1 family: arithmetic kernel (wrapper)

On the family e=f−1, the side parameter p vanishes.
Arithmetic core: p·e + R = f with R≥2 ⟹ p=0 (`side_p_zero_of_two_c`);
full side-walk specialization: P=0, Q=0 (`epred_side_no_a`).

On the family e=f−1 the column (0,e,2e) is killed.
Arithmetic core: if side walks with P>0 (from the corner), then P=f, Q=0, R=1
(`column_zero_side_word`), which contradicts R≥2 (`column_zero_dies_of_two_c`).

The geometric premise n_c≥2 (the exclusion of the a-edge on the second side) appears as hypothesis `hR : 2 ≤ R`.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.EpredWrap

open Erdos634.EpredColumnKill

/-- thm:efminus1 (arithmetic tail): p·e + R = f, R≥2, e+1=f ⟹ p = 0. -/
theorem efminus1_p_zero {e f p R : ℕ} (he : e + 1 = f)
    (hlevel : p * e + R = f) (hR : 2 ≤ R) : p = 0 :=
  side_p_zero_of_two_c he hlevel hR

/-- thm:efminus1 (side walk): at e=f−1, n_c≥2 forces P=0, Q=0 in the side walk. -/
theorem efminus1_side_no_a {e f P Q R b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hR : 2 ≤ R) : P = 0 ∧ Q = 0 :=
  epred_side_no_a he he1 hb hwalk hR

/-- prop:n1fromwalls (family e=f−1): if corner lays an a-edge (P>0) and n_c≥2, False. -/
theorem n1fromwalls_column_zero_dies {e f P Q R b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hPpos : 0 < P) (hR : 2 ≤ R) : False :=
  column_zero_dies_of_two_c he he1 hb hwalk hgamma hPpos hR

/-- prop:n1fromwalls (side word): a-edge on the side forces P=f, Q=0, R=1 at e=f−1. -/
theorem n1fromwalls_side_word {e f P Q R b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hPpos : 0 < P) : P = f ∧ Q = 0 ∧ R = 1 :=
  column_zero_side_word he he1 hb hwalk hgamma hPpos

/-- Non-vacuity: (e,f)=(1,2), e+1=f. At (1,2), b=3: 1·2+3·4=4+12=16≠8. -/
-- Witness at (e,f)=(2,3): b+4=9, b=5; walk 0·6+0·5+1·9=9=27? No.
-- Actual witness: at (e=1,f=2), b+1=4 so b=3; P=0,Q=0,R=2: 0·2+0·3+2·4=8=8=f³. R=2≥2.
theorem efminus1_witness : (1 : ℕ) + 1 = 2 ∧ (2 : ℕ) ≤ 2 ∧
    (0 : ℕ) * (1 * 2) + 0 * 3 + 2 * (2 * 2) = 2 * 2 * 2 := by norm_num

#print axioms efminus1_p_zero
#print axioms efminus1_side_no_a
#print axioms n1fromwalls_column_zero_dies

end Erdos634.Draft.EpredWrap
