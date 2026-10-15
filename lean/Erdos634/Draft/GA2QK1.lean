/-
GA2Q, K-version of part 1 (i = 1): the component formula at 5^r (any r >= 1) for ARBITRARY eta3 mod 3^j and the trivial character mod 2.
  `bracket_D` : for psi primitive mod 5 and ANY eta3 mod 3^j (j >= 1) there is kappa != 0 (independent of the entry) with
     a odd, 3 !| a, 5 !| a :  [a/n]_{psi (1 x eta3)} = kappa psi(a) eta3(a) (1 - psi(2)^-1 eta3(2)^-1)
     a = 2b, 3 !| b, 5 !| a :  [a/n] = kappa psi(b) eta3(b).
  (kappa = the Euler factor at 3, equal to 1 - conj psi(3) if eta3 = 1 and to 1 otherwise; nonzero since psi(3) != 1.)
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PJ
import Erdos634.Draft.GA2NF1

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2QK1

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PD

theorem euler_odd (j : ℕ) (f : ℕ) (hf : f ∣ 3 ^ j) :
    eulerPrimes (2 ^ 1 * 3 ^ j) f = insert 2 (eulerPrimes (3 ^ j) f) := by
  have hf2 : ¬ 2 ∣ f := fun h => by
    have := (h.trans hf)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    omega
  ext ℓ
  simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hl, hld, -⟩, hnf⟩
    rcases (Nat.Prime.dvd_mul hl).1 hld with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h)
    · right; exact ⟨⟨hl, h, by positivity⟩, hnf⟩
  · rintro (rfl | ⟨⟨hl, hld, -⟩, hnf⟩)
    · exact ⟨⟨Nat.prime_two, Dvd.dvd.mul_right (by norm_num) _, by positivity⟩, hf2⟩
    · exact ⟨⟨hl, Dvd.dvd.mul_left hld _, by positivity⟩, hnf⟩

theorem two_not_mem_euler (j f : ℕ) : 2 ∉ eulerPrimes (3 ^ j) f := by
  intro h
  simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors] at h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h.1.2.1
  omega

theorem bracket_D (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) :
    ∃ κ : ℂ, κ ≠ 0 ∧
      (∀ a : ℕ, ¬ 5 ∣ a → Nat.Coprime (2 ^ 1 * 3 ^ j) a →
        bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) a =
          κ * (ψ (a : ZMod (5 ^ r)) * η3 (a : ZMod (3 ^ j)) *
            (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η3 (2 : ZMod (3 ^ j)))⁻¹))) ∧
      (∀ b : ℕ, ¬ 5 ∣ 2 * b → ¬ 3 ∣ b →
        bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) (2 * b) =
          κ * (ψ (b : ZMod (5 ^ r)) * η3 (b : ZMod (3 ^ j)))) := by
  haveI : NeZero (2 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hfd : η3.conductor ∣ 3 ^ j := conductor_dvd_level η3
  set f : ℕ := η3.conductor with hf
  set κ : ℂ := ∏ ℓ ∈ eulerPrimes (3 ^ j) f, (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹ *
    (η3.primitiveCharacter (ℓ : ZMod f))⁻¹) with hκ
  have hstar : ∀ b : ℕ, Nat.Coprime 3 b → η3.primitiveCharacter (b : ZMod f) = η3 (b : ZMod (3 ^ j)) :=
    fun b hb => star_eq_of_coprime η3 b (Nat.Coprime.pow_right _ hb.symm)
  refine ⟨κ, ?_, ?_, ?_⟩
  · rw [hκ, Finset.prod_ne_zero_iff]
    intro ℓ hℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hℓ
    obtain ⟨⟨hlp, hlM, -⟩, hnf⟩ := hℓ
    have hl3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hlp Nat.prime_three).1 (hlp.dvd_of_dvd_pow hlM)
    subst hl3
    have hc3 : f = 1 := by
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hfd
      rcases Nat.eq_zero_or_pos k with rfl | hkp
      · simpa using hk'
      · exfalso
        apply hnf
        rw [hk']
        exact dvd_pow_self 3 (by omega)
    have hsub : Subsingleton (ZMod f) := by rw [hc3]; infer_instance
    rw [Subsingleton.elim (((3 : ℕ)) : ZMod f) 1, MulChar.map_one]
    simp only [mul_one, inv_one]
    intro h0
    apply Erdos634.GA2NF1.psi_three_ne_one r hr ψ hψ
    have : (ψ ((3 : ℕ) : ZMod (5 ^ r)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    have h' := inv_eq_one.1 this
    simpa using h'
  · intro a ha5 hcop
    have hg1 : (2 ^ 1 * 3 ^ j).gcd a = 1 := hcop
    have hdm : dm (2 ^ 1 * 3 ^ j) a = 2 ^ 1 * 3 ^ j := by unfold dm; rw [hg1, Nat.div_one]
    have hMpos : 0 < 2 ^ 1 * 3 ^ j := by positivity
    have hdvd : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * η3.conductor ∣ dm (2 ^ 1 * 3 ^ j) a := by
      rw [hdm, hc1, one_mul]
      exact hfd.trans (Dvd.intro_left _ rfl)
    have hc3a : Nat.Coprime 3 a := Nat.Coprime.coprime_dvd_left
      (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 2) hcop
    have h2c : Nat.Coprime 3 2 := by norm_num
    have heq : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * η3.conductor = f := by rw [hc1, one_mul]
    rw [bracket_gen2 r 1 j ψ hψ 1 η3 a ha5, if_pos hdvd, hdm, hg1, Nat.div_one,
      div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'), heq, euler_odd j f hfd,
      Finset.prod_insert (two_not_mem_euler j f)]
    have s1 : (1 : DirichletCharacter ℂ (2 ^ 1)).primitiveCharacter
        (2 : ZMod (1 : DirichletCharacter ℂ (2 ^ 1)).conductor) = 1 := by
      have := Erdos634.GA2NB2.star_one (n := 2 ^ 1) 2
      simpa using this
    have s2 : η3.primitiveCharacter (2 : ZMod f) = η3 (2 : ZMod (3 ^ j)) := by
      have := hstar 2 h2c
      simpa using this
    simp only [Erdos634.GA2NB2.star_one, one_mul, hstar a hc3a, Nat.cast_ofNat, s1, s2]
    rw [← hκ]
    ring
  · intro b hb5 hb3
    have hcb : Nat.Coprime (3 ^ j) b := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3)
    have hM : (2 ^ 1 * 3 ^ j) = 2 * 3 ^ j := by norm_num
    have hg : (2 ^ 1 * 3 ^ j).gcd (2 * b) = 2 := by
      rw [hM, Nat.gcd_mul_left, hcb, mul_one]
    have hdm : dm (2 ^ 1 * 3 ^ j) (2 * b) = 3 ^ j := by
      unfold dm; rw [hg, hM, Nat.mul_div_cancel_left _ (by norm_num)]
    have hdvd : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * η3.conductor ∣ dm (2 ^ 1 * 3 ^ j) (2 * b) := by
      rw [hdm, hc1, one_mul]; exact hfd
    have hcop2 : Nat.Coprime 2 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    have htot : (((2 ^ 1 * 3 ^ j).totient : ℕ) : ℂ) / (((3 ^ j).totient : ℕ) : ℂ) = 1 := by
      rw [hM, Nat.totient_mul hcop2]
      have : (2 : ℕ).totient = 1 := by decide
      rw [this]
      have h3 : (((3 ^ j).totient : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
      push_cast
      field_simp
    have hb3' : Nat.Coprime 3 b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3
    have heq : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * η3.conductor = f := by rw [hc1, one_mul]
    rw [bracket_gen2 r 1 j ψ hψ 1 η3 (2 * b) hb5, if_pos hdvd, hdm, hg, Nat.mul_div_cancel_left _ (by norm_num),
      htot, heq]
    simp only [Erdos634.GA2NB2.star_one, one_mul, hstar b hb3']
    rw [← hκ]
    ring




/-- i = 0 (trivial 2-part, modulus 2^0): for arbitrary eta3 mod 3^j and psi primitive mod 5^r there is kappa != 0 with
 [a/n] = kappa psi(a) eta3(a) for every a prime to 5 and to 3 (generalizes GA2PD.bracket_C_visible to r >= 1). -/
theorem bracket_K0 (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ a : ℕ, ¬ 5 ∣ a → Nat.Coprime 3 a →
      bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η3)) a =
        κ * (ψ (a : ZMod (5 ^ r)) * η3 (a : ZMod (3 ^ j))) := by
  haveI : NeZero (2 ^ 0) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor = 1 := DirichletCharacter.conductor_one
  set M : ℕ := 2 ^ 0 * 3 ^ j with hM
  set f : ℕ := (1 : DirichletCharacter ℂ (2 ^ 0)).conductor * η3.conductor with hf
  refine ⟨∏ ℓ ∈ eulerPrimes M f, (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹ *
    ((1 : DirichletCharacter ℂ (2 ^ 0)).primitiveCharacter (ℓ : ZMod (1 : DirichletCharacter ℂ (2 ^ 0)).conductor) *
      η3.primitiveCharacter (ℓ : ZMod η3.conductor))⁻¹), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro ℓ hℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hℓ
    obtain ⟨⟨hlp, hlM, -⟩, hnf⟩ := hℓ
    have hl3 : ℓ = 3 := by
      have h3j : ℓ ∣ 3 ^ j := by
        have : ℓ ∣ 2 ^ 0 * 3 ^ j := hlM
        simpa using this
      exact (Nat.prime_dvd_prime_iff_eq hlp Nat.prime_three).1 (hlp.dvd_of_dvd_pow h3j)
    subst hl3
    have hc3 : η3.conductor = 1 := by
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (conductor_dvd_level η3)
      rcases Nat.eq_zero_or_pos k with rfl | hkp
      · simpa using hk'
      · exfalso
        apply hnf
        rw [hf, hc1, hk', one_mul]
        exact dvd_pow_self 3 (by omega)
    have hsub : Subsingleton (ZMod η3.conductor) := by rw [hc3]; infer_instance
    have hsub1 : Subsingleton (ZMod (1 : DirichletCharacter ℂ (2 ^ 0)).conductor) := by rw [hc1]; infer_instance
    rw [Subsingleton.elim (((3 : ℕ)) : ZMod η3.conductor) 1, MulChar.map_one,
      Subsingleton.elim (((3 : ℕ)) : ZMod (1 : DirichletCharacter ℂ (2 ^ 0)).conductor) 1, MulChar.map_one]
    simp only [mul_one, inv_one]
    intro h0
    apply Erdos634.GA2NF1.psi_three_ne_one r hr ψ hψ
    have : (ψ ((3 : ℕ) : ZMod (5 ^ r)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    have h' := inv_eq_one.1 this
    simpa using h'
  · intro a ha5 ha3
    have hcopM : Nat.Coprime M a := by
      rw [hM, pow_zero, one_mul]
      exact Nat.Coprime.pow_left _ ha3
    have hg1 : M.gcd a = 1 := hcopM
    have hdm : dm M a = M := by unfold dm; rw [hg1, Nat.div_one]
    have hMpos : 0 < M := by positivity
    rw [bracket_gen2 r 0 j ψ hψ 1 η3 a ha5]
    have hdvd : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor * η3.conductor ∣ dm M a := by
      rw [hdm, hc1, one_mul]
      exact (conductor_dvd_level η3).trans (by rw [hM, pow_zero, one_mul])
    rw [if_pos hdvd, hdm, hg1, Nat.div_one,
      div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne')]
    rw [Erdos634.GA2NB2.star_one (n := 2 ^ 0) a, star_eq_of_coprime η3 a (Nat.Coprime.pow_right _ ha3.symm)]
    ring

end Erdos634.GA2QK1

#print axioms Erdos634.GA2QK1.bracket_D
#print axioms Erdos634.GA2QK1.bracket_K0
