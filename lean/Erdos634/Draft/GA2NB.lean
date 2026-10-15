/-
GA2N, item (3): the **general component formula** at 5^r with composite M = 2^(k+3) 3^j, for ARBITRARY eta2 mod 2^(k+3)
and eta3 mod 3^j (not only the top family), and the three consequences used by Theorem A:
  `bracket_gen`           : [a/n]_{psi (eta2 x eta3)} = [f | d] w psi(b) eta2*(b) eta3*(b) prod_{l in Euler(d,f)} (1 - conj(psi eta*)(l)),
                            f = cond(eta2) cond(eta3), d = M / gcd(M,a), b = a / gcd(M,a), w = phi(M)/phi(d).
  `bracket_eq_zero_of_not_dvd` : f !| d  =>  0.
  `bracket_ne_zero_of_eq`      : f = d   =>  != 0   (no Euler primes, all factors units).
  `dm_odd`                : a odd => d = 2^(k+3) * (3^j / gcd(3^j, a)).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NF1
import Erdos634.Draft.GA2MTop
import Erdos634.Draft.LemmaSIso

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NB

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2MTop

theorem bracket_gen (r k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) :
    bracket (chi ψ (chi η2 η3)) a =
      if η2.conductor * η3.conductor ∣ dm (2 ^ (k + 3) * 3 ^ j) a then
        (((2 ^ (k + 3) * 3 ^ j).totient : ℂ) / ((dm (2 ^ (k + 3) * 3 ^ j) a).totient : ℂ)) *
          ψ ((a / (2 ^ (k + 3) * 3 ^ j).gcd a : ℕ) : ZMod (5 ^ r)) *
          (η2.primitiveCharacter ((a / (2 ^ (k + 3) * 3 ^ j).gcd a : ℕ) : ZMod η2.conductor) *
            η3.primitiveCharacter ((a / (2 ^ (k + 3) * 3 ^ j).gcd a : ℕ) : ZMod η3.conductor)) *
          ∏ ℓ ∈ eulerPrimes (dm (2 ^ (k + 3) * 3 ^ j) a) (η2.conductor * η3.conductor),
            (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹ * (η2.primitiveCharacter (ℓ : ZMod η2.conductor) *
              η3.primitiveCharacter (ℓ : ZMod η3.conductor))⁻¹)
      else 0 := by
  haveI : NeZero (2 ^ (k + 3)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set η : DirichletCharacter ℂ (2 ^ (k + 3) * 3 ^ j) := chi η2 η3 with hη
  have hcop : Nat.Coprime (2 ^ (k + 3)) (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  have e : η = changeLevel (Nat.dvd_mul_right (2 ^ (k + 3)) (3 ^ j)) η2 *
      changeLevel (Nat.dvd_mul_left (3 ^ j) (2 ^ (k + 3))) η3 := rfl
  have hc : η.conductor = η2.conductor * η3.conductor := Erdos634.DirichletCRT.conductor_eq hcop e
  have hstar : ∀ b : ℕ, η.primitiveCharacter (b : ZMod η.conductor) =
      η2.primitiveCharacter (b : ZMod η2.conductor) * η3.primitiveCharacter (b : ZMod η3.conductor) :=
    fun b => primChar_mul_nat hcop e b
  rw [bracket_unit (not5_dvd k j) hψ η a ha5]
  simp only [MulChar.inv_apply_eq_inv', hstar]
  rw [hc]

theorem bracket_eq_zero_of_not_dvd (r k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (h : ¬ η2.conductor * η3.conductor ∣ dm (2 ^ (k + 3) * 3 ^ j) a) :
    bracket (chi ψ (chi η2 η3)) a = 0 := by
  rw [bracket_gen r k j ψ hψ η2 η3 a ha5, if_neg h]

/-- Divisibility facts for M = 2^(k+3) 3^j. -/
theorem dm_dvd (k j a : ℕ) : dm (2 ^ (k + 3) * 3 ^ j) a ∣ 2 ^ (k + 3) * 3 ^ j :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

theorem bracket_ne_zero_of_eq (r k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (h : η2.conductor * η3.conductor = dm (2 ^ (k + 3) * 3 ^ j) a) :
    bracket (chi ψ (chi η2 η3)) a ≠ 0 := by
  haveI : NeZero (2 ^ (k + 3)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set M := 2 ^ (k + 3) * 3 ^ j with hM
  have hMpos : 0 < M := by positivity
  rw [bracket_gen r k j ψ hψ η2 η3 a ha5, if_pos (h ▸ dvd_rfl)]
  have hE : eulerPrimes (dm M a) (η2.conductor * η3.conductor) = ∅ := by
    rw [h]
    refine Finset.eq_empty_of_forall_notMem (fun ℓ hℓ => ?_)
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hℓ
    exact hℓ.2 hℓ.1.2.1
  rw [hE, Finset.prod_empty, mul_one]
  have hgpos : 0 < M.gcd a := Nat.gcd_pos_of_pos_left _ hMpos
  have hbd : (dm M a).Coprime (a / M.gcd a) := Nat.coprime_div_gcd_div_gcd hgpos
  have hφ : ((M.totient : ℕ) : ℂ) / (((dm M a).totient : ℕ) : ℂ) ≠ 0 := by
    have h1 : ((M.totient : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'
    have hd0 : 0 < dm M a := Nat.div_pos (Nat.le_of_dvd hMpos (Nat.gcd_dvd_left _ _)) hgpos
    have h2 : (((dm M a).totient : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hd0).ne'
    exact div_ne_zero h1 h2
  have hb5 : ¬ 5 ∣ a / M.gcd a := by
    intro h5
    exact ha5 (h5.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
  have hpsi : ψ ((a / M.gcd a : ℕ) : ZMod (5 ^ r)) ≠ 0 := by
    have hu : IsUnit (((a / M.gcd a : ℕ)) : ZMod (5 ^ r)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hb5).symm
    exact Erdos634.GA2LCore.nz ψ _ hu
  have hc2 : (a / M.gcd a).Coprime η2.conductor := by
    have : η2.conductor ∣ dm M a := h ▸ dvd_mul_right _ _
    exact (hbd.coprime_dvd_left this).symm
  have hc3 : (a / M.gcd a).Coprime η3.conductor := by
    have : η3.conductor ∣ dm M a := h ▸ dvd_mul_left _ _
    exact (hbd.coprime_dvd_left this).symm
  have h2 := Erdos634.LemmaSIso.primChar_ne_zero η2 _ hc2
  have h3 := Erdos634.LemmaSIso.primChar_ne_zero η3 _ hc3
  exact mul_ne_zero (mul_ne_zero hφ hpsi) (mul_ne_zero h2 h3)

/-- a odd: the 2-part of d is all of 2^(k+3) and the 3-part is 3^j / gcd(3^j, a). -/
theorem dm_odd (k j a : ℕ) (ha : Odd a) :
    dm (2 ^ (k + 3) * 3 ^ j) a = 2 ^ (k + 3) * (3 ^ j / Nat.gcd (3 ^ j) a) := by
  unfold dm
  have hc : Nat.Coprime (2 ^ (k + 3)) a := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 ha)
  rw [Nat.Coprime.gcd_mul_left_cancel (3 ^ j) hc]
  exact Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _)

end Erdos634.GA2NB

#print axioms Erdos634.GA2NB.bracket_gen
#print axioms Erdos634.GA2NB.bracket_eq_zero_of_not_dvd
#print axioms Erdos634.GA2NB.bracket_ne_zero_of_eq
#print axioms Erdos634.GA2NB.dm_odd
