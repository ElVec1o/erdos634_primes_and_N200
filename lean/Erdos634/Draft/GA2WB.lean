/-
GA2W, part B: the explicit brackets for the trivial character mod 3 at j = 1, and the quadratic character mod 3.
  K-b (n = 3 * 5^r, i = 0):  `br_b_unit` (3 !| a):  psi(a) (1 - psi(3)^-1);   `br_b_three` (a = 3 t):  2 psi(t).
  K-c (n = 6 * 5^r, i = 1):  `br_c_unit` (a odd, 3 !| a):  psi(a) (1 - psi(2)^-1)(1 - psi(3)^-1);   `br_c_six` (a = 6 s):  2 psi(s).
  `eta3_neg_one` : a primitive character mod 3 is odd;  `mod3_cases`;  `exists_odd_psi`, `exists_even_psi`.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2WA

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2WB

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm)
open Erdos634.GA2PA (bracket_gen2 not5_dvd')

theorem br_b_unit (r : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) (a : ℕ)
    (h5 : ¬ 5 ∣ a) (h3 : ¬ 3 ∣ a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) (1 : DirichletCharacter ℂ (3 ^ 1)))) a =
      ψ (a : ZMod (5 ^ r)) * (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹) := by
  haveI : NeZero (2 ^ 0) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor = 1 := DirichletCharacter.conductor_one
  have hc2 : (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hf : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor * (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := by
    rw [hc1, hc2]
  have hcop : Nat.Coprime (2 ^ 0 * 3 ^ 1) a := by
    norm_num
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hg1 : (2 ^ 0 * 3 ^ 1).gcd a = 1 := hcop
  have hdm : dm (2 ^ 0 * 3 ^ 1) a = 3 := by unfold dm; rw [hg1]; norm_num
  have hE : eulerPrimes 3 1 = {3} := by
    ext ℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hl, hld, -⟩, -⟩; exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).1 hld
    · rintro rfl; exact ⟨⟨Nat.prime_three, dvd_rfl, by norm_num⟩, by norm_num⟩
  have htot : (((2 ^ 0 * 3 ^ 1 : ℕ).totient : ℂ)) / (((3 : ℕ).totient : ℕ) : ℂ) = 1 := by
    have : (2 ^ 0 * 3 ^ 1 : ℕ) = 3 := by norm_num
    rw [this]
    exact div_self (by exact_mod_cast (Nat.totient_pos.2 (by norm_num : 0 < 3)).ne')
  rw [bracket_gen2 r 0 1 ψ hψ 1 1 a h5, hf, hdm, if_pos (by simp), hg1, Nat.div_one, hE, htot]
  simp only [Erdos634.GA2NB2.star_one, Finset.prod_singleton, mul_one, one_mul, inv_one, Nat.cast_ofNat]

theorem br_b_three (r : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) (t : ℕ)
    (h5 : ¬ 5 ∣ 3 * t) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) (1 : DirichletCharacter ℂ (3 ^ 1)))) (3 * t) =
      2 * ψ (t : ZMod (5 ^ r)) := by
  haveI : NeZero (2 ^ 0) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor = 1 := DirichletCharacter.conductor_one
  have hc2 : (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hf : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor * (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := by
    rw [hc1, hc2]
  have hM : (2 ^ 0 * 3 ^ 1 : ℕ) = 3 := by norm_num
  have hg : (2 ^ 0 * 3 ^ 1).gcd (3 * t) = 3 := by
    rw [hM]; exact Nat.gcd_eq_left (dvd_mul_right 3 t)
  have hdm : dm (2 ^ 0 * 3 ^ 1) (3 * t) = 1 := by unfold dm; rw [hg, hM]
  have hE : eulerPrimes 1 1 = ∅ := by simp [eulerPrimes]
  have htot : (((2 ^ 0 * 3 ^ 1 : ℕ).totient : ℂ)) / (((1 : ℕ).totient : ℕ) : ℂ) = 2 := by
    rw [hM]
    have : (3 : ℕ).totient = 2 := by decide
    rw [this]; simp
  rw [bracket_gen2 r 0 1 ψ hψ 1 1 (3 * t) h5, hf, hdm, if_pos (by simp), hg,
    Nat.mul_div_cancel_left _ (by norm_num), hE, htot]
  simp only [Erdos634.GA2NB2.star_one, Finset.prod_empty, mul_one]

theorem br_c_unit (r : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) (a : ℕ)
    (h5 : ¬ 5 ∣ a) (h3 : ¬ 3 ∣ a) (h2 : a % 2 = 1) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) (1 : DirichletCharacter ℂ (3 ^ 1)))) a =
      ψ (a : ZMod (5 ^ r)) * ((1 - (ψ (2 : ZMod (5 ^ r)))⁻¹) * (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹)) := by
  haveI : NeZero (2 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hc2 : (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hf : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := by
    rw [hc1, hc2]
  have hM : (2 ^ 1 * 3 ^ 1 : ℕ) = 6 := by norm_num
  have hg1 : (2 ^ 1 * 3 ^ 1).gcd a = 1 := by
    rw [hM]
    have h6 : Nat.Coprime 6 a := by
      have : Nat.Coprime 2 a := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
      have h3' : Nat.Coprime 3 a := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
      exact Nat.Coprime.mul_left this h3'
    exact h6
  have hdm : dm (2 ^ 1 * 3 ^ 1) a = 6 := by unfold dm; rw [hg1, hM]
  have hE : eulerPrimes 6 1 = {2, 3} := by
    ext ℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hl, hld, -⟩, -⟩
      have h6 : ℓ ∣ 2 * 3 := hld
      rcases (Nat.Prime.dvd_mul hl).1 h6 with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h
      · right; exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).1 h
    · rintro (rfl | rfl)
      · exact ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, by norm_num⟩
      · exact ⟨⟨Nat.prime_three, by norm_num, by norm_num⟩, by norm_num⟩
  have htot : (((2 ^ 1 * 3 ^ 1 : ℕ).totient : ℂ)) / (((6 : ℕ).totient : ℕ) : ℂ) = 1 := by
    rw [hM]
    exact div_self (by exact_mod_cast (Nat.totient_pos.2 (by norm_num : 0 < 6)).ne')
  rw [bracket_gen2 r 1 1 ψ hψ 1 1 a h5, hf, hdm, if_pos (by simp), hg1, Nat.div_one, hE, htot]
  rw [Finset.prod_pair (by norm_num)]
  simp only [Erdos634.GA2NB2.star_one]
  simp only [mul_one, one_mul, inv_one, Nat.cast_ofNat]

theorem br_c_six (r : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) (s : ℕ)
    (h5 : ¬ 5 ∣ 6 * s) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) (1 : DirichletCharacter ℂ (3 ^ 1)))) (6 * s) =
      2 * ψ (s : ZMod (5 ^ r)) := by
  haveI : NeZero (2 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hc2 : (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hf : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * (1 : DirichletCharacter ℂ (3 ^ 1)).conductor = 1 := by
    rw [hc1, hc2]
  have hM : (2 ^ 1 * 3 ^ 1 : ℕ) = 6 := by norm_num
  have hg : (2 ^ 1 * 3 ^ 1).gcd (6 * s) = 6 := by
    rw [hM]; exact Nat.gcd_eq_left (dvd_mul_right 6 s)
  have hdm : dm (2 ^ 1 * 3 ^ 1) (6 * s) = 1 := by unfold dm; rw [hg, hM]
  have hE : eulerPrimes 1 1 = ∅ := by simp [eulerPrimes]
  have htot : (((2 ^ 1 * 3 ^ 1 : ℕ).totient : ℂ)) / (((1 : ℕ).totient : ℕ) : ℂ) = 2 := by
    rw [hM]
    have : (6 : ℕ).totient = 2 := by decide
    rw [this]; simp
  rw [bracket_gen2 r 1 1 ψ hψ 1 1 (6 * s) h5, hf, hdm, if_pos (by simp), hg,
    Nat.mul_div_cancel_left _ (by norm_num), hE, htot]
  simp only [Erdos634.GA2NB2.star_one, Finset.prod_empty, mul_one]

theorem eta3_neg_one (η : DirichletCharacter ℂ (3 ^ 1)) (hη : η.IsPrimitive) : η (-1) = -1 := by
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : Fact (1 < 3 ^ 1) := ⟨by norm_num⟩
  rcases Erdos634.GA2LCore.sign_val η with h | h
  · exfalso
    have h1 : η = 1 := by
      refine MulChar.ext' (fun a => ?_)
      have hcases : ∀ a : ZMod (3 ^ 1), a = 0 ∨ a = 1 ∨ a = -1 := by decide
      rcases hcases a with rfl | rfl | rfl
      · rw [MulChar.map_nonunit η (by simp), MulChar.map_nonunit (1 : DirichletCharacter ℂ (3 ^ 1)) (by simp)]
      · rw [map_one, map_one]
      · rw [h, MulChar.one_apply (isUnit_one.neg)]
    have hc : η.conductor = 3 ^ 1 := hη
    rw [h1, DirichletCharacter.conductor_one] at hc
    norm_num at hc
  · exact h

theorem eta3_two (η : DirichletCharacter ℂ (3 ^ 1)) (hη : η.IsPrimitive) :
    η (2 : ZMod (3 ^ 1)) = -1 := by
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  have : (2 : ZMod (3 ^ 1)) = -1 := by decide
  rw [this]; exact eta3_neg_one η hη

theorem mod3_cases (X Y : ℕ) (hX : ¬ 3 ∣ X) (hY : ¬ 3 ∣ Y) :
    (Y : ZMod (3 ^ 1)) = (X : ZMod (3 ^ 1)) ∨ (Y : ZMod (3 ^ 1)) = -(X : ZMod (3 ^ 1)) := by
  have hx : X % 3 = 1 ∨ X % 3 = 2 := by omega
  have hy : Y % 3 = 1 ∨ Y % 3 = 2 := by omega
  by_cases hxy : X % 3 = Y % 3
  · left
    refine (ZMod.natCast_eq_natCast_iff _ _ _).2 ?_
    unfold Nat.ModEq
    simp only [pow_one]
    omega
  · right
    refine (Erdos634.GA2PD.natcast_neg_iff (3 ^ 1) Y X).2 ?_
    simp only [pow_one]
    omega

theorem exists_odd_psi (r : ℕ) (hr : 1 ≤ r) :
    ∃ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive ∧ ψ (-1) = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 r hr (-1) (Or.inr rfl)
  exact ⟨ψ, Erdos634.GA2LCore.mem_PrimPar.1 hψ⟩

theorem exists_even_psi (r : ℕ) (hr : 1 ≤ r) :
    ∃ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive ∧ ψ (-1) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 r hr 1 (Or.inl rfl)
  exact ⟨ψ, Erdos634.GA2LCore.mem_PrimPar.1 hψ⟩

end Erdos634.GA2WB

#print axioms Erdos634.GA2WB.br_b_unit
#print axioms Erdos634.GA2WB.br_b_three
#print axioms Erdos634.GA2WB.br_c_unit
#print axioms Erdos634.GA2WB.br_c_six
#print axioms Erdos634.GA2WB.eta3_neg_one
#print axioms Erdos634.GA2WB.mod3_cases
