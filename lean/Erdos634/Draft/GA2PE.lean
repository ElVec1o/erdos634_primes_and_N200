/-
GA2P, Theorem B (GA2Y_NOTES Section 5, i = 2, r = 1, j >= 2), part 1: number theory and bracket values.
  `shape_plus`, `shape_minus`      : the two arithmetic shapes (a_p = a_q +- n/2, a_p + a_q = n/2), n = 4 m0, m0 odd.
  `chi4`, `chi4_val`               : the primitive character mod 4, its values on odd numbers.
  `bracket_triv_odd`, `bracket_triv_four` : the trivial-character bracket at an odd entry / at an entry divisible by 4.
  `bracket_ne_zero_of_eq2`         : f = d  =>  nonzero (general 2-part).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PA

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PE

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA

theorem modEq_m0 (j : ℕ) (x y : ℕ) (h3 : x ≡ y [MOD 3 ^ j]) (h5 : x ≡ y [MOD 5]) :
    x ≡ y [MOD 5 * 3 ^ j] := by
  have hc : Nat.Coprime 5 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  exact (Nat.modEq_and_modEq_iff_modEq_mul hc).1 ⟨h5, h3⟩

theorem dvd_m0 (j : ℕ) (s : ℕ) (h3 : 3 ^ j ∣ s) (h5 : 5 ∣ s) : 5 * 3 ^ j ∣ s := by
  have hc : Nat.Coprime 5 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h5 h3

theorem shape_plus (m0 aP aQ : ℕ) (hm0 : m0 % 2 = 1) (hP : aP % 2 = 1) (hQ : aQ % 2 = 1)
    (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hPl : aP < 4 * m0) (hQl : aQ < 4 * m0)
    (h : aP ≡ aQ [MOD m0]) : aP = aQ ∨ aP = aQ + 2 * m0 ∨ aQ = aP + 2 * m0 := by
  rw [Nat.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  have hm : (0 : ℤ) < m0 := by omega
  have hl : k < 4 := by
    by_contra hh
    push Not at hh
    nlinarith
  have hl' : -4 < k := by
    by_contra hh
    push Not at hh
    nlinarith
  interval_cases k <;> omega

theorem shape_minus (m0 aP aQ : ℕ) (hm0 : m0 % 2 = 1) (hP : aP % 2 = 1) (hQ : aQ % 2 = 1)
    (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hs : aP + aQ < 4 * m0) (h : m0 ∣ aP + aQ) :
    aP + aQ = 2 * m0 := by
  obtain ⟨k, hk⟩ := h
  have hm : 0 < m0 := by omega
  have hl : k < 4 := by
    by_contra hh
    push Not at hh
    nlinarith
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  interval_cases k <;> omega

/-- A primitive character mod 4, odd. -/
theorem exists_chi4 : ∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive ∧ χ (-1) = -1 := by
  obtain ⟨ω, hω⟩ := Erdos634.LemmaSGpp.exists_primitive_pp (q := 2) (v := 2) (by norm_num) (by norm_num)
  exact ⟨ω, hω, Erdos634.GA2NB2.four_odd ω hω⟩

theorem chi4_val (χ : DirichletCharacter ℂ (2 ^ 2)) (hχ : χ (-1) = -1) (a : ℕ) (ha : a % 2 = 1) :
    χ (a : ZMod (2 ^ 2)) = if a % 4 = 1 then 1 else -1 := by
  have hcast : (a : ZMod (2 ^ 2)) = ((a % 4 : ℕ) : ZMod (2 ^ 2)) := by
    rw [ZMod.natCast_mod]
  have h4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  rcases h4 with h | h
  · rw [hcast, h, if_pos rfl]; simp
  · rw [hcast, h, if_neg (by omega)]
    have : ((3 : ℕ) : ZMod (2 ^ 2)) = -1 := by decide
    rw [this, hχ]

theorem dm_odd2 (i j a : ℕ) (ha : Odd a) (hi : 1 ≤ i) :
    dm (2 ^ i * 3 ^ j) a = 2 ^ i * (3 ^ j / Nat.gcd (3 ^ j) a) := by
  unfold dm
  have hc : Nat.Coprime (2 ^ i) a := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 ha)
  rw [Nat.Coprime.gcd_mul_left_cancel (3 ^ j) hc]
  exact Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _)

theorem bracket_ne_zero_of_eq2 (r i j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ i)) (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (h : η2.conductor * η3.conductor = dm (2 ^ i * 3 ^ j) a) :
    bracket (chi ψ (chi η2 η3)) a ≠ 0 := by
  haveI : NeZero (2 ^ i) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set M := 2 ^ i * 3 ^ j with hM
  have hMpos : 0 < M := by positivity
  rw [bracket_gen2 r i j ψ hψ η2 η3 a ha5, if_pos (h ▸ dvd_rfl)]
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


theorem pf_M (j : ℕ) (hj : 1 ≤ j) : (2 ^ 2 * 3 ^ j).primeFactors = {2, 3} := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by omega) Nat.prime_three]
  ext x; simp

theorem bracket_triv_odd (j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (a : ℕ) (ha5 : ¬ 5 ∣ a) (hcop : Nat.Coprime (2 ^ 2 * 3 ^ j) a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 2)) (1 : DirichletCharacter ℂ (3 ^ j)))) a =
      ψ (a : ZMod (5 ^ 1)) * ((1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹) * (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹)) := by
  rw [bracket_triv_formula2 1 2 j ψ hψ a ha5]
  have hg1 : (2 ^ 2 * 3 ^ j).gcd a = 1 := hcop
  have hdm : dm (2 ^ 2 * 3 ^ j) a = 2 ^ 2 * 3 ^ j := by unfold dm; rw [hg1, Nat.div_one]
  have hMpos : 0 < 2 ^ 2 * 3 ^ j := by positivity
  rw [hdm, hg1, Nat.div_one, div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'), pf_M j hj,
    Finset.prod_pair (by norm_num)]
  simp only [Nat.cast_ofNat, one_mul]

theorem bracket_triv_four (j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (b : ℕ) (hb5 : ¬ 5 ∣ 4 * b) (hb3 : ¬ 3 ∣ b) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 2)) (1 : DirichletCharacter ℂ (3 ^ j)))) (4 * b) =
      2 * ψ (b : ZMod (5 ^ 1)) * (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹) := by
  rw [bracket_triv_formula2 1 2 j ψ hψ (4 * b) hb5]
  have hcb : Nat.Coprime (3 ^ j) b := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3)
  have hM : (2 ^ 2 * 3 ^ j) = 4 * 3 ^ j := by norm_num
  have hg : (2 ^ 2 * 3 ^ j).gcd (4 * b) = 4 := by
    rw [hM, Nat.gcd_mul_left, hcb, mul_one]
  have hdm : dm (2 ^ 2 * 3 ^ j) (4 * b) = 3 ^ j := by
    unfold dm; rw [hg, hM, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcop4 : Nat.Coprime 4 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  have htot : (((2 ^ 2 * 3 ^ j).totient : ℕ) : ℂ) / (((3 ^ j).totient : ℕ) : ℂ) = 2 := by
    rw [hM, Nat.totient_mul hcop4]
    have : (4 : ℕ).totient = 2 := by decide
    rw [this]
    push_cast
    have h3 : (((3 ^ j).totient : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
    field_simp
  rw [hdm, hg, Nat.mul_div_cancel_left _ (by norm_num), htot,
    Nat.primeFactors_prime_pow (by omega) Nat.prime_three, Finset.prod_singleton]
  simp only [Nat.cast_ofNat]

end Erdos634.GA2PE

#print axioms Erdos634.GA2PE.shape_plus
#print axioms Erdos634.GA2PE.shape_minus
#print axioms Erdos634.GA2PE.chi4_val
#print axioms Erdos634.GA2PE.bracket_ne_zero_of_eq2
#print axioms Erdos634.GA2PE.bracket_triv_odd
#print axioms Erdos634.GA2PE.bracket_triv_four
