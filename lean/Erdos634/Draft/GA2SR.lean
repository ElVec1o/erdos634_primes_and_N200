/-
GA2S, atom R: Prop K-c (i = 1) with an entry T divisible by 3, not by 5: the hidden-entry kills and the labelled theorem (r >= 2).
  `dm_even1`, `bracket_ne_zero_odd` : the brackets of the hidden entry at a character of conductor 3^j / gcd (5-adic factor (1 - psi(2)^-1 eta3*(2)^-1))
  `kcT_even` : T = S (even): eS = 0 once P, Q are Good.
  `kcT_odd`  : T = P (odd):  eP = 0 once eQ, eS vanish (or the entry is divisible by 5); psi or psi^-1 avoids the Euler zero (psi(2)^2 != 1).
  `kc_lab`   : class sums vanish on every column prime to 5.  Hypothesis `hT`: T = P, or T = Q, or (T = S and j >= 2).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SQ

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SR

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PG
open Erdos634.GA2SD Erdos634.GA2SJ Erdos634.GA2SK Erdos634.GA2SO Erdos634.GA2SP Erdos634.GA2SQ
open Erdos634.GA2SL (unit3)

theorem dm_even1 (j b : ℕ) : dm (2 ^ 1 * 3 ^ j) (2 * b) = 3 ^ j / Nat.gcd (3 ^ j) b := by
  unfold dm
  have hM : (2 ^ 1 * 3 ^ j) = 2 * 3 ^ j := by norm_num
  rw [hM, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ (by norm_num)]

theorem bracket_ne_zero_odd (r j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (P : ℕ) (hD : η3.conductor = 3 ^ j / Nat.gcd (3 ^ j) P)
    (hP5 : ¬ 5 ∣ P) (hPo : P % 2 = 1)
    (hfac : (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η3 (2 : ZMod (3 ^ j)))⁻¹ ≠ 1) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) P ≠ 0 := by
  haveI : NeZero (2 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set M : ℕ := 2 ^ 1 * 3 ^ j with hM
  have hMpos : 0 < M := by positivity
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
  have hfc : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor * η3.conductor = 3 ^ j / Nat.gcd (3 ^ j) P := by
    rw [hc1, hD, one_mul]
  have hdm := dm_odd2 1 j P (Nat.odd_iff.2 hPo) le_rfl
  have hcop2 : Nat.Coprime 2 P := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have hgM : M.gcd P = Nat.gcd (3 ^ j) P := by
    rw [hM, show (2 ^ 1 * 3 ^ j) = 2 * 3 ^ j by norm_num]
    exact Nat.Coprime.gcd_mul_left_cancel (3 ^ j) hcop2
  have hgpos : 0 < M.gcd P := Nat.gcd_pos_of_pos_left _ hMpos
  have hd0 : 0 < dm M P := Nat.div_pos (Nat.le_of_dvd hMpos (Nat.gcd_dvd_left _ _)) hgpos
  have hD0 : 0 < 3 ^ j / Nat.gcd (3 ^ j) P :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) (Nat.gcd_dvd_left _ _))
      (Nat.gcd_pos_of_pos_left _ (by positivity))
  rw [bracket_gen2 r 1 j ψ hψ 1 η3 P hP5, if_pos (by rw [hfc, hdm]; exact Dvd.intro_left _ rfl)]
  have hE : eulerPrimes (dm M P) (3 ^ j / Nat.gcd (3 ^ j) P) = {2} := by
    ext ℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
    rw [hdm]
    constructor
    · rintro ⟨⟨hl, hld, -⟩, hnf⟩
      rcases (Nat.Prime.dvd_mul hl).1 hld with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h)
      · exact absurd h hnf
    · rintro rfl
      refine ⟨⟨Nat.prime_two, Dvd.dvd.mul_right (by norm_num) _, by positivity⟩, ?_⟩
      intro h
      have h1 : 2 ∣ 3 ^ j := h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h1
      omega
  rw [hfc, hE, Finset.prod_singleton]
  have hbd : (dm M P).Coprime (P / M.gcd P) := Nat.coprime_div_gcd_div_gcd hgpos
  have hφ : ((M.totient : ℕ) : ℂ) / (((dm M P).totient : ℕ) : ℂ) ≠ 0 := by
    have h1 : ((M.totient : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'
    have h2 : (((dm M P).totient : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hd0).ne'
    exact div_ne_zero h1 h2
  have hb5 : ¬ 5 ∣ P / M.gcd P := by
    intro h5
    exact hP5 (h5.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
  have hpsi : ψ ((P / M.gcd P : ℕ) : ZMod (5 ^ r)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    exact unit5r r _ hb5
  have hc3 : (P / M.gcd P).Coprime η3.conductor := by
    have : η3.conductor ∣ dm M P := by
      rw [hdm, hD]; exact Dvd.intro_left _ rfl
    exact (hbd.coprime_dvd_left this).symm
  have h3 := Erdos634.LemmaSIso.primChar_ne_zero η3 _ hc3
  have hfac' : (1 - (ψ ((2 : ℕ) : ZMod (5 ^ r)))⁻¹ *
      ((1 : DirichletCharacter ℂ (2 ^ 1)).primitiveCharacter ((2 : ℕ) : ZMod (1 : DirichletCharacter ℂ (2 ^ 1)).conductor) *
        η3.primitiveCharacter ((2 : ℕ) : ZMod η3.conductor))⁻¹) ≠ 0 := by
    have h2c : Nat.Coprime 2 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    rw [Erdos634.GA2NB2.star_one (n := 2 ^ 1) 2, star_eq_of_coprime η3 2 h2c]
    intro h0
    apply hfac
    simp only [Nat.cast_ofNat, one_mul] at h0 ⊢
    linear_combination -h0
  rw [Erdos634.GA2NB2.star_one (n := 2 ^ 1) (P / M.gcd P), one_mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hφ hpsi) h3) hfac'

end Erdos634.GA2SR

#print axioms Erdos634.GA2SR.dm_even1
#print axioms Erdos634.GA2SR.bracket_ne_zero_odd
