/-
Draft/SplusR2Arith.lean -- written 20 October 2026.  UNAUDITED.  Not in `All`; in `AllSplusR2`.

**Theorem R2, stage 1: the arithmetic.**  Tile `(a, b, c) = (e f, f^2 - e^2, f^2)`, coprime `e < f`.
* `A5'` : `j c - b` is not in `<a, b, c>` for `1 ≤ j ≤ f - 1`  (from `SideRunGArith.A5`).
* `Aa'` : `j a - b` is not in `<a, b, c>` for `1 ≤ j ≤ f - 1`  (from `SideRunGArith.Aa`).
* `c_single_rep` (N): for `e ≥ 2`, `c` has only the representation `c`  (from `A5`, `e ∤ f`).
* `r2_arith`: the count step of the corollary: `M < f`, `M (f - e) ≤ e + 2`, `z ≥ e+1`, `z ≥ e+2` (if `e+2 ≤ f`),
  `z ≥ e+3` (if `e+3 ≤ f`) contradict a representation of `M f b`.  Uses `SplusThick.C_AQ'` (`z ≤ M (f-e)` under `M (f-e) < f`:
  this CLOSES gap G2 of `project working notes`) and shows `f - e ≥ 3` when `M (f-e) = e + 2` (G1).

Credit: Beeson-Rosu (framework), Paliy, the E2R6 room (A1/A5/Aa), SPLUS/SPLUS2, the AI assistant (Lemmas Z, R, Z'), the two audits.
No sorry, no native_decide.
-/
import Erdos634.Draft.SplusThickArith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SplusR2
open Erdos634.Draft.SideRunGArith

/-- **(A5')** `x a + y b + z c + b = j c` is impossible for `1 ≤ j ≤ f - 1` (`j c - b ∉ <a,b,c>`). -/
theorem A5' {e f j x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 + (f ^ 2 - e ^ 2) = j * f ^ 2) : False := by
  have := A5 he hef hco hj1 hj (x := x) (y := y + 1) (z := z) (by rw [← h]; ring)
  omega

/-- **(Aa')** `x a + y b + z c + b = j a` is impossible for `1 ≤ j ≤ f - 1` (`j a - b ∉ <a,b,c>`). -/
theorem Aa' {e f j x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 + (f ^ 2 - e ^ 2) = j * (e * f)) : False := by
  have := Aa he hef hco hj1 hj (x := x) (y := y + 1) (z := z) (by rw [← h]; ring)
  omega

/-- **(N)** for `e ≥ 2`: `c` is represented only as `c` -/
theorem c_single_rep {e f x y z : ℕ} (he : 2 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = f ^ 2) : x = 0 ∧ y = 0 ∧ z = 1 := by
  have hy : y = 0 := A5 (j := 1) (by omega) hef hco le_rfl (by omega) (by simpa using h)
  subst hy
  have hf : 0 < f := by omega
  have h2 : x * e + z * f = f := by
    have : f * (x * e + z * f) = f * f := by nlinarith [h]
    exact Nat.eq_of_mul_eq_mul_left hf this
  have hz : z ≤ 1 := by
    by_contra hz
    have : 2 * f ≤ z * f := Nat.mul_le_mul_right f (by omega)
    omega
  rcases Nat.lt_or_ge z 1 with hz0 | hz1
  · have hz0' : z = 0 := by omega
    subst hz0'
    have hd : e ∣ f := ⟨x, by rw [Nat.mul_comm]; omega⟩
    have := Nat.Coprime.eq_one_of_dvd hco hd
    omega
  · have hz1' : z = 1 := by omega
    subst hz1'
    refine ⟨?_, rfl, rfl⟩
    · have : x * e = 0 := by omega
      rcases Nat.mul_eq_zero.mp this with h0 | h0
      · exact h0
      · omega

/-- **`r2_arith`**: the arithmetic of the corollary.  Hypotheses of the audited statement (G1): `e ≥ 2`, `M < f`, `M (f - e) ≤ e + 2`. -/
theorem r2_arith {e f M x y z : ℕ} (he : 2 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hMf : M < f) (hM : M * (f - e) ≤ e + 2)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2))
    (hz1 : e + 1 ≤ z) (hz2 : e + 2 ≤ f → e + 2 ≤ z) (hz3 : e + 3 ≤ f → e + 3 ≤ z) : False := by
  by_cases h1 : M * (f - e) ≤ e + 1
  · exact Erdos634.Draft.SplusThick.no_rep_z_ge (by omega) hef hco hMf h1 h hz1 hz2
  · have hEq : M * (f - e) = e + 2 := by omega
    have hf3 : e + 3 ≤ f := by
      by_contra hlt
      rcases Nat.lt_or_ge f (e + 2) with h2 | h2
      · have hfe : f = e + 1 := by omega
        subst hfe
        simp at hEq
        omega
      · have hfe : f = e + 2 := by omega
        subst hfe
        have h3 : M * 2 = e + 2 := by simpa using hEq
        have hd : 2 ∣ Nat.gcd e (e + 2) :=
          Nat.dvd_gcd ⟨M - 1, by omega⟩ ⟨M, by omega⟩
        rw [hco.gcd_eq_one] at hd
        omega
    have hlt : M * (f - e) < f := by omega
    have hz := (Erdos634.Draft.SplusThick.C_AQ' (by omega) hef hco h).2 hlt
    have := hz3 hf3
    omega

-- non-vacuity of the arithmetic hypotheses (G1 statement): the covered instances and an r = e + 1 control
example : Nat.Coprime 4 7 ∧ 2 ≤ 4 ∧ 4 < 7 ∧ 2 < 7 ∧ 7 ≤ 2 * 4 ∧ 2 * (7 - 4) ≤ 4 + 2 ∧ 2 * (7 - 4) = 4 + 2 := by decide
example : Nat.Coprime 7 10 ∧ 2 ≤ 7 ∧ 7 < 10 ∧ 3 < 10 ∧ 10 ≤ 3 * 7 ∧ 3 * (10 - 7) ≤ 7 + 2 ∧ 3 * (10 - 7) = 7 + 2 := by decide
example : Nat.Coprime 8 13 ∧ 2 ≤ 8 ∧ 8 < 13 ∧ 2 < 13 ∧ 13 ≤ 2 * 8 ∧ 2 * (13 - 8) ≤ 8 + 2 ∧ 2 * (13 - 8) = 8 + 2 := by decide
example : Nat.Coprime 5 8 ∧ 2 ≤ 5 ∧ 5 < 8 ∧ 2 < 8 ∧ 8 ≤ 2 * 5 ∧ 2 * (8 - 5) ≤ 5 + 1 := by decide
-- (5,9,2) is NOT covered: M (f - e) = 8 > e + 2 = 7
example : ¬ (2 * (9 - 5) ≤ 5 + 2) := by decide
-- the semigroup facts at (4,7): c = 49 only as c, c - b = 16 and a - b not representable
example : ¬ ∃ x y z : ℕ, x * 28 + y * 33 + z * 49 + 33 = 49 := fun ⟨x, y, z, h⟩ => by omega

end Erdos634.Draft.SplusR2

#print axioms Erdos634.Draft.SplusR2.A5'
#print axioms Erdos634.Draft.SplusR2.Aa'
#print axioms Erdos634.Draft.SplusR2.c_single_rep
#print axioms Erdos634.Draft.SplusR2.r2_arith
