import Erdos634.CChord

/-!
# c-chord and base walk dichotomies: arithmetic wrapper

Arithmetic kernels of `CChord.*` (pure ℕ/ℤ arithmetic, no geometry):

1. **`c_chord_dichotomy`**: x·a + y·b + z·c = c forces (0,0,1) or e=1,(f,0,0).
2. **`base_dichotomy_thick`**: at e≥1, f>e: x·a + y·b + z·c = f(f²−e²) forces
   (0,e,2e) or (f,e,e) at a separated member (f²>2ef+e²).
3. **`base_trichotomy`**: general walk x·a+y·b+z·c = e(3f²−e²) forces one of 3 cases.
4. **`base_dichotomy_2e`**: at 2e<f the dichotomy (0,e,2e) or (f,e,e).

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.CChordWrap

open Erdos634.CChord

/-- c-chord dichotomy: x·a+y·b+z·c = c forces (0,0,1) or e=1∧(f,0,0). -/
theorem cchord_dichotomy {e f a b c : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f)
    {x y z : ℕ} (h : x * a + y * b + z * c = c) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (e = 1 ∧ x = f ∧ y = 0 ∧ z = 0) :=
  c_chord_dichotomy hco he hef ha hb hc h

/-- c-chord unique at thick member: e≥2 forces (0,0,1) only. -/
theorem cchord_unique_thick {e f x y z : ℕ} (he : 2 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = f * f) :
    x = 0 ∧ y = 0 ∧ z = 1 :=
  c_chord_unique_thick he hef hco h

/-- Base walk trichotomy: x·(ef)+y·(f²−e²)+z·f² = e(3f²−e²) forces one of 3 cases. -/
theorem cchord_base_trichotomy {e f x y z : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f) (hsep : 2 * e * f + e * e < f * f)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)) :
    (x = 0 ∧ y = e ∧ z = 2 * e) ∨
    (x = f ∧ y = e ∧ z = e) ∨
    (x = 2 * f ∧ y = e ∧ z = 0) :=
  base_trichotomy he hef hco hsep h

/-- Base dichotomy at thick (separated): forces (0,e,2e) or (f,e,e), given z≥1. -/
theorem cchord_base_dichotomy_thick {e f x y z : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f) (hsep : 2 * e * f + e * e < f * f) (hz : 1 ≤ z)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)) :
    (x = 0 ∧ y = e ∧ z = 2 * e) ∨ (x = f ∧ y = e ∧ z = e) :=
  base_dichotomy_thick he hef hco hsep hz h

/-- Base dichotomy at 2e<f: same conclusion, given z≥1. -/
theorem cchord_base_dichotomy_2e {e f x y z : ℕ} (he : 1 ≤ e) (hef2 : 2 * e < f)
    (hco : Nat.Coprime e f) (hz : 1 ≤ z)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)) :
    (x = 0 ∧ y = e ∧ z = 2 * e) ∨ (x = f ∧ y = e ∧ z = e) :=
  base_dichotomy_2e he hef2 hco hz h

/-- Non-vacuity: e=1, f=3 satisfies sep hypothesis (9 > 6+1). -/
theorem cchord_witness : Nat.Coprime 1 3 ∧ (1:ℕ) ≤ 1 ∧ (1:ℕ) < 3 ∧
    2 * 1 * 3 + 1 * 1 < (3:ℕ) * 3 := by norm_num [Nat.Coprime]

#print axioms cchord_dichotomy
#print axioms cchord_base_dichotomy_thick
#print axioms cchord_base_dichotomy_2e

end Erdos634.Draft.CChordWrap
