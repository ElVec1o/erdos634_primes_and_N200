/-
GA2P, atom 3a, case i = 1: the component formula with eta2 = 1 (mod 2^1) and a PRIMITIVE 3-adic top eta3 mod 3^j.
(For i = 0, 2 this is `GA2PA.bracket_top_prim`; here the 2-part is the trivial character mod 2, conductor 1, so Euler factors appear.)
  `bracket_i1_odd`  : a odd, 3 !| a, 5 !| a :  [a/n] = psi(a) eta3(a) (1 - conj psi(2) conj eta3(2))
  `bracket_i1_even` : a = 2b, 3 !| b, 5 !| a :  [a/n] = psi(b) eta3(b)
  `bracket_i1_three`: 3 | a, 5 !| a : [a/n] = 0.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PD

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PJ

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PD

theorem bracket_i1_three (r j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3.IsPrimitive) (a : ℕ) (ha5 : ¬ 5 ∣ a) (h3 : 3 ∣ a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) a = 0 := by
  haveI : NeZero (2 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [bracket_gen2 r 1 j ψ hψ 1 η3 a ha5, if_neg]
  intro hdv
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hc3 : η3.conductor = 3 ^ j := hη3
  rw [hc1, hc3, one_mul] at hdv
  have hg : (2 ^ 1 * 3 ^ j).gcd a ∣ 2 ^ 1 * 3 ^ j := Nat.gcd_dvd_left _ _
  have h3g : 3 ∣ (2 ^ 1 * 3 ^ j).gcd a :=
    Nat.dvd_gcd (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _) h3
  have hmul : dm (2 ^ 1 * 3 ^ j) a * (2 ^ 1 * 3 ^ j).gcd a = 2 ^ 1 * 3 ^ j := Nat.div_mul_cancel hg
  have h9 : 3 ^ j * 3 ∣ 2 ^ 1 * 3 ^ j := by
    rw [← hmul]; exact Nat.mul_dvd_mul hdv h3g
  have : 3 ∣ 2 ^ 1 := by
    have h' : 3 ^ j * 3 ∣ 3 ^ j * 2 ^ 1 := by simpa [mul_comm] using h9
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h'
  omega

theorem bracket_i1_odd (r j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3.IsPrimitive) (a : ℕ) (ha5 : ¬ 5 ∣ a)
    (hcop : Nat.Coprime (2 ^ 1 * 3 ^ j) a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) a =
      ψ (a : ZMod (5 ^ r)) * η3 (a : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η3 (2 : ZMod (3 ^ j)))⁻¹) := by
  haveI : NeZero (2 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hc3 : η3.conductor = 3 ^ j := hη3
  have hg1 : (2 ^ 1 * 3 ^ j).gcd a = 1 := hcop
  have hdm : dm (2 ^ 1 * 3 ^ j) a = 2 ^ 1 * 3 ^ j := by unfold dm; rw [hg1, Nat.div_one]
  have hMpos : 0 < 2 ^ 1 * 3 ^ j := by positivity
  have hfc : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * η3.conductor = 3 ^ j := by rw [hc1, hc3, one_mul]
  rw [bracket_gen2 r 1 j ψ hψ 1 η3 a ha5, hfc, hdm, hg1, Nat.div_one,
    if_pos (Dvd.intro_left 2 (by ring)),
    div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne')]
  have hE : eulerPrimes (2 ^ 1 * 3 ^ j) (3 ^ j) = {2} := by
    ext ℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hl, hld, -⟩, hnf⟩
      rcases (Nat.Prime.dvd_mul hl).1 hld with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h)
      · exact absurd h hnf
    · rintro rfl
      refine ⟨⟨Nat.prime_two, Dvd.dvd.mul_right (by norm_num) _, by positivity⟩, ?_⟩
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
      omega
  rw [hE, Finset.prod_singleton, one_mul, Erdos634.GA2NB2.star_one (n := 2 ^ 1) a,
    primChar_nat_of_isPrimitive hη3 a, Erdos634.GA2NB2.star_one (n := 2 ^ 1) 2,
    primChar_nat_of_isPrimitive hη3 2]
  simp only [Nat.cast_ofNat, one_mul]

theorem bracket_i1_even (r j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3.IsPrimitive) (b : ℕ) (hb5 : ¬ 5 ∣ 2 * b)
    (hb3 : ¬ 3 ∣ b) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) (2 * b) =
      ψ (b : ZMod (5 ^ r)) * η3 (b : ZMod (3 ^ j)) := by
  haveI : NeZero (2 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hc3 : η3.conductor = 3 ^ j := hη3
  have hcb : Nat.Coprime (3 ^ j) b := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3)
  have hM : (2 ^ 1 * 3 ^ j) = 2 * 3 ^ j := by norm_num
  have hg : (2 ^ 1 * 3 ^ j).gcd (2 * b) = 2 := by
    rw [hM, Nat.gcd_mul_left, hcb, mul_one]
  have hdm : dm (2 ^ 1 * 3 ^ j) (2 * b) = 3 ^ j := by
    unfold dm; rw [hg, hM, Nat.mul_div_cancel_left _ (by norm_num)]
  have hfc : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * η3.conductor = 3 ^ j := by rw [hc1, hc3, one_mul]
  have hcop2 : Nat.Coprime 2 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  have htot : (((2 ^ 1 * 3 ^ j).totient : ℕ) : ℂ) / (((3 ^ j).totient : ℕ) : ℂ) = 1 := by
    rw [hM, Nat.totient_mul hcop2]
    have : (2 : ℕ).totient = 1 := by decide
    rw [this]
    have h3 : (((3 ^ j).totient : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
    push_cast
    field_simp
  rw [bracket_gen2 r 1 j ψ hψ 1 η3 (2 * b) hb5, hfc, hdm, hg, Nat.mul_div_cancel_left _ (by norm_num),
    if_pos dvd_rfl, htot]
  have hE : eulerPrimes (3 ^ j) (3 ^ j) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun ℓ hℓ => ?_)
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hℓ
    exact hℓ.2 hℓ.1.2.1
  rw [hE, Finset.prod_empty, mul_one, one_mul, Erdos634.GA2NB2.star_one (n := 2 ^ 1) b,
    primChar_nat_of_isPrimitive hη3 b]
  ring

end Erdos634.GA2PJ

#print axioms Erdos634.GA2PJ.bracket_i1_three
#print axioms Erdos634.GA2PJ.bracket_i1_odd
#print axioms Erdos634.GA2PJ.bracket_i1_even
