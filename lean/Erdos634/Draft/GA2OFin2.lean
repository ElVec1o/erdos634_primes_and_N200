/-
From a certificate `allCert n = true` to the n-instance of GapA2 (generic), and the instances n = 45, 75, 90.
n = 90 = 2*3^2*5 lies in the row i = 1, r = 1, j >= 2, entry divisible by 3, which the general argument does not cover; this is only that single value.
-/
import Mathlib
import Erdos634.Draft.GA2OFin

namespace Erdos634.GA2OFin2

open Erdos634.Geometry Erdos634.LemmaS Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

theorem gapA2_of_cert (m : ℕ) (hm7 : 7 ≤ m) (hc : allCert m = true) (D : CongruentDissection 15)
    (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (hnm : n = m) : False := by
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  subst hnm
  exact r0c_core15 D rfl hn a ha (of_allCert hc a hpos hsum hgcd) hm7
    Erdos634.Draft.Chain15.lemmaH15_holds

theorem gapA2_n45 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (h : n = 45) : False :=
  gapA2_of_cert 45 (by norm_num) Erdos634.GA2OFin.allCert_45 D n a hn hgcd ha h
theorem gapA2_n75 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (h : n = 75) : False :=
  gapA2_of_cert 75 (by norm_num) Erdos634.GA2OFin.allCert_75 D n a hn hgcd ha h
theorem gapA2_n90 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (h : n = 90) : False :=
  gapA2_of_cert 90 (by norm_num) Erdos634.GA2OFin.allCert_90 D n a hn hgcd ha h

end Erdos634.GA2OFin2

#print axioms Erdos634.GA2OFin2.gapA2_of_cert
#print axioms Erdos634.GA2OFin2.gapA2_n45
#print axioms Erdos634.GA2OFin2.gapA2_n75
#print axioms Erdos634.GA2OFin2.gapA2_n90
