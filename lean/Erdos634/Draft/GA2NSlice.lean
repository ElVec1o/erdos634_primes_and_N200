/-
The **i >= 3 slice of GapA2** (N = 15, Case A, n = 2^i 3^j 5^r with i >= 3, j, r >= 1).

`gapA2_slice_i3`: for a CongruentDissection D of N = 15 whose model's angles are a_k pi / n with gcd(a) = 1 and
n = 5^r * (2^(k+3) * 3^j), r, j >= 1: False.  Proof: `GA2NP7.lemmaS5_i3` supplies `hSn : relSpace n a = trivSpace n a`
(Lemma S' at p = 5 via Theorem A), and `CaseAN15.r0c_core15` (with `Chain15.lemmaH15_holds`) closes it.
This does not prove `GapA2`: the slices i <= 2, n = 15, 30, 60 are not covered.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NP7
import Erdos634.Draft.Chain15H

open scoped BigOperators

namespace Erdos634.GA2NSlice

open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

theorem gapA2_slice_i3 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hform : ∃ r k j : ℕ, 1 ≤ r ∧ 1 ≤ j ∧ n = 5 ^ r * (2 ^ (k + 3) * 3 ^ j)) : False := by
  obtain ⟨r, k, j, hr, hj, hnform⟩ := hform
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hSn : relSpace n a = trivSpace n a := by
    subst hnform
    exact Erdos634.GA2NP7.lemmaS5_i3 r k j hr hj a hpos hsum hgcd
  have h7 : 7 ≤ n := by
    rw [hnform]
    have h5 : 5 ≤ 5 ^ r := by
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    have h2 : 8 ≤ 2 ^ (k + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    calc 7 ≤ 5 * (8 * 3) := by norm_num
      _ ≤ 5 ^ r * (2 ^ (k + 3) * 3 ^ j) := Nat.mul_le_mul h5 (Nat.mul_le_mul h2 h3)
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

end Erdos634.GA2NSlice

#print axioms Erdos634.GA2NSlice.gapA2_slice_i3
