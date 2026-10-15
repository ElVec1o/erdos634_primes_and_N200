/-
GA2P, atom 3a: the **component formula with a general 2-part 2^i** (i arbitrary, in particular i in {0,1,2}) and
the **top bracket for primitive eta2, eta3**:

  `bracket_gen2`     : [a/n]_{psi (eta2 x eta3)}, eta2 mod 2^i, eta3 mod 3^j, psi prim mod 5^r, 5 !| a
                       = [f | d] w psi(b) eta2*(b) eta3*(b) prod_{l in Euler(d,f)} (1 - conj(psi eta*)(l)),  (GA2NB.bracket_gen with 2^(k+3) -> 2^i)
  `bracket_top_prim` : eta2 primitive mod 2^i, eta3 primitive mod 3^j (conductors = moduli), 5 !| a:
                       [a/n] = if gcd(2^i 3^j, a) = 1 then psi(a) eta2(a) eta3(a) else 0.   (no Euler factors, w = 1)
For i = 0 (eta2 = the character mod 1) and i = 2 (eta2 = the primitive character mod 4) these are the TOP characters of
GA2Y_NOTES Theorems C and B.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NB
import Erdos634.Draft.GA2NB2

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PA

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi

theorem not5_dvd' (i j : ℕ) : ¬ 5 ∣ 2 ^ i * 3 ^ j := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h; omega
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h; omega

theorem bracket_gen2 (r i j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ i)) (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) :
    bracket (chi ψ (chi η2 η3)) a =
      if η2.conductor * η3.conductor ∣ dm (2 ^ i * 3 ^ j) a then
        (((2 ^ i * 3 ^ j).totient : ℂ) / ((dm (2 ^ i * 3 ^ j) a).totient : ℂ)) *
          ψ ((a / (2 ^ i * 3 ^ j).gcd a : ℕ) : ZMod (5 ^ r)) *
          (η2.primitiveCharacter ((a / (2 ^ i * 3 ^ j).gcd a : ℕ) : ZMod η2.conductor) *
            η3.primitiveCharacter ((a / (2 ^ i * 3 ^ j).gcd a : ℕ) : ZMod η3.conductor)) *
          ∏ ℓ ∈ eulerPrimes (dm (2 ^ i * 3 ^ j) a) (η2.conductor * η3.conductor),
            (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹ * (η2.primitiveCharacter (ℓ : ZMod η2.conductor) *
              η3.primitiveCharacter (ℓ : ZMod η3.conductor))⁻¹)
      else 0 := by
  haveI : NeZero (2 ^ i) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set η : DirichletCharacter ℂ (2 ^ i * 3 ^ j) := chi η2 η3 with hη
  have hcop : Nat.Coprime (2 ^ i) (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  have e : η = changeLevel (Nat.dvd_mul_right (2 ^ i) (3 ^ j)) η2 *
      changeLevel (Nat.dvd_mul_left (3 ^ j) (2 ^ i)) η3 := rfl
  have hc : η.conductor = η2.conductor * η3.conductor := Erdos634.DirichletCRT.conductor_eq hcop e
  have hstar : ∀ b : ℕ, η.primitiveCharacter (b : ZMod η.conductor) =
      η2.primitiveCharacter (b : ZMod η2.conductor) * η3.primitiveCharacter (b : ZMod η3.conductor) :=
    fun b => primChar_mul_nat hcop e b
  rw [bracket_unit (not5_dvd' i j) hψ η a ha5]
  simp only [MulChar.inv_apply_eq_inv', hstar]
  rw [hc]

theorem bracket_top_prim (r i j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ i)) (hη2 : η2.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3.IsPrimitive) (a : ℕ) (ha5 : ¬ 5 ∣ a) :
    bracket (chi ψ (chi η2 η3)) a =
      if Nat.Coprime (2 ^ i * 3 ^ j) a then
        ψ (a : ZMod (5 ^ r)) * (η2 (a : ZMod (2 ^ i)) * η3 (a : ZMod (3 ^ j)))
      else 0 := by
  haveI : NeZero (2 ^ i) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hMpos : 0 < 2 ^ i * 3 ^ j := by positivity
  have hc2 : η2.conductor = 2 ^ i := hη2
  have hc3 : η3.conductor = 3 ^ j := hη3
  have hfc : η2.conductor * η3.conductor = 2 ^ i * 3 ^ j := by rw [hc2, hc3]
  rw [bracket_gen2 r i j ψ hψ η2 η3 a ha5, hfc]
  by_cases hg : Nat.Coprime (2 ^ i * 3 ^ j) a
  · rw [if_pos hg]
    have hg1 : (2 ^ i * 3 ^ j).gcd a = 1 := hg
    have hdm : dm (2 ^ i * 3 ^ j) a = 2 ^ i * 3 ^ j := by
      unfold dm; rw [hg1, Nat.div_one]
    rw [hdm, hg1, Nat.div_one, if_pos dvd_rfl]
    have hE : eulerPrimes (2 ^ i * 3 ^ j) (2 ^ i * 3 ^ j) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun ℓ hℓ => ?_)
      simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hℓ
      exact hℓ.2 hℓ.1.2.1
    rw [hE, Finset.prod_empty, mul_one, div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'),
      one_mul]
    have e2 := primChar_nat_of_isPrimitive hη2 a
    have e3 := primChar_nat_of_isPrimitive hη3 a
    rw [e2, e3]
  · rw [if_neg hg, if_neg]
    intro hdv
    have hgpos : 0 < (2 ^ i * 3 ^ j).gcd a := Nat.gcd_pos_of_pos_left _ hMpos
    have hg2 : 2 ≤ (2 ^ i * 3 ^ j).gcd a := by
      rcases Nat.lt_or_ge ((2 ^ i * 3 ^ j).gcd a) 2 with h | h
      · exact absurd (by omega : (2 ^ i * 3 ^ j).gcd a = 1) hg
      · exact h
    have hd0 : 0 < dm (2 ^ i * 3 ^ j) a :=
      Nat.div_pos (Nat.le_of_dvd hMpos (Nat.gcd_dvd_left _ _)) hgpos
    have hle := Nat.le_of_dvd hd0 hdv
    unfold dm at hle
    have : (2 ^ i * 3 ^ j) / (2 ^ i * 3 ^ j).gcd a < 2 ^ i * 3 ^ j :=
      Nat.div_lt_self hMpos (by omega)
    omega


#print axioms Erdos634.GA2PA.bracket_gen2
#print axioms Erdos634.GA2PA.bracket_top_prim

/-! ### the trivial characters, general 2-part -/

theorem dm_dvd2 (i j a : ℕ) : dm (2 ^ i * 3 ^ j) a ∣ 2 ^ i * 3 ^ j :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

theorem primeFactors_dm2 (i j a : ℕ) (p : ℕ) (hp : p ∈ (dm (2 ^ i * 3 ^ j) a).primeFactors) :
    p = 2 ∨ p = 3 := by
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  have hM : p ∣ 2 ^ i * 3 ^ j := hpd.trans (dm_dvd2 i j a)
  rcases (Nat.Prime.dvd_mul hpp).1 hM with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h)
  · right; exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h)

theorem bracket_triv_formula2 (r i j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (a : ℕ) (ha5 : ¬ 5 ∣ a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ i)) (1 : DirichletCharacter ℂ (3 ^ j)))) a =
      (((2 ^ i * 3 ^ j).totient : ℂ) / ((dm (2 ^ i * 3 ^ j) a).totient : ℂ)) *
        ψ ((a / (2 ^ i * 3 ^ j).gcd a : ℕ) : ZMod (5 ^ r)) *
        ∏ ℓ ∈ (dm (2 ^ i * 3 ^ j) a).primeFactors, (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹) := by
  haveI : NeZero (2 ^ i) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [bracket_gen2 r i j ψ hψ _ _ a ha5]
  have hc2 : (1 : DirichletCharacter ℂ (2 ^ i)).conductor = 1 := DirichletCharacter.conductor_one
  have hc3 : (1 : DirichletCharacter ℂ (3 ^ j)).conductor = 1 := DirichletCharacter.conductor_one
  simp only [Erdos634.GA2NB2.star_one, mul_one, inv_one]
  rw [hc2, hc3, mul_one, if_pos (one_dvd _)]
  have hE : eulerPrimes (dm (2 ^ i * 3 ^ j) a) 1 = (dm (2 ^ i * 3 ^ j) a).primeFactors := by
    ext ℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, fun h1 => h.1.one_lt.ne' (Nat.dvd_one.1 h1)⟩
  rw [hE]

theorem bracket_triv_ne_zero2 (r i j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (h2 : ψ (2 : ZMod (5 ^ r)) ≠ 1) (h3 : ψ (3 : ZMod (5 ^ r)) ≠ 1)
    (a : ℕ) (ha5 : ¬ 5 ∣ a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ i)) (1 : DirichletCharacter ℂ (3 ^ j)))) a ≠ 0 := by
  rw [bracket_triv_formula2 r i j ψ hψ a ha5]
  set M := 2 ^ i * 3 ^ j with hM
  have hMpos : 0 < M := by positivity
  have hgpos : 0 < M.gcd a := Nat.gcd_pos_of_pos_left _ hMpos
  have hd0 : 0 < dm M a := Nat.div_pos (Nat.le_of_dvd hMpos (Nat.gcd_dvd_left _ _)) hgpos
  have hφ : ((M.totient : ℕ) : ℂ) / (((dm M a).totient : ℕ) : ℂ) ≠ 0 := by
    have h1 : ((M.totient : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'
    have h2' : (((dm M a).totient : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hd0).ne'
    exact div_ne_zero h1 h2'
  have hb5 : ¬ 5 ∣ a / M.gcd a := by
    intro h5
    exact ha5 (h5.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
  have hpsi : ψ ((a / M.gcd a : ℕ) : ZMod (5 ^ r)) ≠ 0 := by
    have hu : IsUnit (((a / M.gcd a : ℕ)) : ZMod (5 ^ r)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hb5).symm
    exact Erdos634.GA2LCore.nz ψ _ hu
  have hprod : ∏ ℓ ∈ (dm M a).primeFactors, (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ℓ hℓ
    rcases primeFactors_dm2 i j a ℓ hℓ with rfl | rfl
    · intro h0
      apply h2
      have : (ψ ((2 : ℕ) : ZMod (5 ^ r)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
      have h' := inv_eq_one.1 this
      simpa using h'
    · intro h0
      apply h3
      have : (ψ ((3 : ℕ) : ZMod (5 ^ r)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
      have h' := inv_eq_one.1 this
      simpa using h'
  exact mul_ne_zero (mul_ne_zero hφ hpsi) hprod

end Erdos634.GA2PA

#print axioms Erdos634.GA2PA.bracket_triv_formula2
#print axioms Erdos634.GA2PA.bracket_triv_ne_zero2
