import Erdos634.Inflation

/-!
# Inflation rigidity: arithmetic kernel

The inflated tile (see `InflBdy`) admits no
tiling by f² copies whose c-side carries the p=1 word, at each of the ten members
(1,3), (1,4), (1,5), (2,5), (3,5), (1,6), (1,7), (3,7), (5,7), (4,9).

The statement has two parts:
1. **Arithmetic**: the two-word dichotomy — the inflated c-side has exactly two compositions
   (p=0 and p=1), and the a/b sides are rigid. Formalized here.
2. **Search**: the p=1 profile has no tiling at each of the ten members (exhaustive
   computer search). Not formalized in this module.

Lean content:
1. **`inflrigid_middle_nine_at_13`**: at (1,3), any middle-of-c-side word sums to 9 → is [9] or [3,3,3].
2. **`inflrigid_residual_245_at_37`**: at (3,7), c-side residual 245 = 5·49 or 7·21+2·49.
3. **`inflrigid_residual_75_at_25`**: at (2,5), c-side residual 75 has exactly two solutions.
4. **`inflrigid_a_side_rigid_13`**: at (1,3), a/b sides are rigid (forced 9=3+3+3, 24=8+8+8).
5. **`inflrigid_c_side_words_13`**: at (1,3), both c-side profiles have the right total.

Arithmetic kernel only: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.InflRigidWrap

open Erdos634.Inflation

/-- thm:inflrigid arithmetic (1,3): any word of sides summing to 9 is [9] or [3,3,3].
    This is the middle-of-c-side forcing at the (1,3) member, establishing the two
    possible c-side profiles. -/
theorem inflrigid_middle_nine_at_13 (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 9) :
    w = [9] ∨ w = [3, 3, 3] :=
  middle_nine w h hs

/-- thm:inflrigid arithmetic (3,7): the inflated c-side residual 245 has exactly two
    compositions: 5·49 (p=0) or 7·21+2·49 (p=1). -/
theorem inflrigid_residual_245_at_37 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 245) :
    (x = 0 ∧ y = 0 ∧ z = 5) ∨ (x = 7 ∧ y = 0 ∧ z = 2) :=
  residual_245 x y z h

/-- thm:inflrigid arithmetic (2,5): the inflated c-side residual 75 has exactly two solutions:
    (x=0,y=0,z=3) the p=0 profile and (x=5,y=0,z=1) the p=1 profile. -/
theorem inflrigid_residual_75_at_25 (x y z : ℕ) (h : 10 * x + 21 * y + 25 * z = 75) :
    (x = 0 ∧ y = 0 ∧ z = 3) ∨ (x = 5 ∧ y = 0 ∧ z = 1) :=
  residual_75 x y z h

/-- thm:inflrigid arithmetic (1,3): the a/b sides are rigid (9 = 3+3+3, 24 = 8+8+8). -/
theorem inflrigid_a_b_sides_rigid_13 :
    ([3, 3, 3] : List ℕ).sum = 9 ∧ ([8, 8, 8] : List ℕ).sum = 24 :=
  a_b_sides_rigid

/-- thm:inflrigid arithmetic (1,3): both c-side profiles have length 27. -/
theorem inflrigid_c_side_words_13 :
    ([9, 9, 9] : List ℕ).sum = 27 ∧ ([9, 3, 3, 3, 9] : List ℕ).sum = 27 :=
  c_side_words

/-- thm:inflrigid arithmetic (3,7): a-side residual 105 = 5·21 (unique). -/
theorem inflrigid_residual_105_at_37 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 105) :
    x = 5 ∧ y = 0 ∧ z = 0 :=
  residual_105 x y z h

/-- thm:inflrigid arithmetic (3,7): b-side residual 200 = 5·40 (unique). -/
theorem inflrigid_residual_200_at_37 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 200) :
    x = 0 ∧ y = 5 ∧ z = 0 :=
  residual_200 x y z h

#print axioms inflrigid_middle_nine_at_13
#print axioms inflrigid_residual_245_at_37
#print axioms inflrigid_residual_75_at_25
#print axioms inflrigid_a_b_sides_rigid_13
#print axioms inflrigid_c_side_words_13

end Erdos634.Draft.InflRigidWrap
