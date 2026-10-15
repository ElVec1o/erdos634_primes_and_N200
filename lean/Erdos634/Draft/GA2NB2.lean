/-
GA2N, item (3): further component formulas and the character-existence lemmas used by Theorem A.
  `bracket_triv_formula`  : eta2 = eta3 = 1 : [a/n]_psi = w psi(b) prod_{l | d} (1 - conj psi(l)).
  `bracket_triv_ne_zero`  : psi(2) != 1, psi(3) != 1  =>  [a/n]_psi != 0     (A1, x even; BOTTOM nonvanishing)
  `bracket_val_noeuler`   : f | d and every prime of d divides f  =>  [a/n] = w psi(b) eta2*(b) eta3*(b)   (MID)
  `exists_eta3`           : for D | 3^j there is eta3 mod 3^j of conductor exactly D.
  `exists_top`            : top character instance (psi prim mod 5^r, eta2 prim mod 2^(k+3), eta3 of conductor D, odd).
  `exists_mid`            : MID characters (eta2 odd of conductor 2^(k+2), eta3 odd of conductor 3).
  `star_neg_one`          : eta*(-1) = eta(-1).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NB
import Erdos634.Draft.GA2NR1

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NB2

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2MTop Erdos634.GA2NB Erdos634.GA2NR1 Erdos634.GA2NF1 Erdos634.GA2LCore Erdos634.GA2LGroup
open Erdos634.GA2NJ1 (three_odd)

/-! ## star of the trivial character, parity of the star -/

theorem star_one {n : ℕ} [NeZero n] (b : ℕ) :
    (1 : DirichletCharacter ℂ n).primitiveCharacter
      (b : ZMod (1 : DirichletCharacter ℂ n).conductor) = 1 := by
  have hc : (1 : DirichletCharacter ℂ n).conductor = 1 := conductor_one
  have hsub : Subsingleton (ZMod (1 : DirichletCharacter ℂ n).conductor) := by rw [hc]; infer_instance
  rw [Subsingleton.elim (b : ZMod (1 : DirichletCharacter ℂ n).conductor) 1, MulChar.map_one]

theorem star_neg_one {N : ℕ} [NeZero N] (η : DirichletCharacter ℂ N) :
    η.primitiveCharacter (-1 : ZMod η.conductor) = η (-1) := by
  haveI : NeZero η.conductor := ⟨conductor_ne_zero η⟩
  have h := changeLevel_primitiveCharacter η
  have e := changeLevel_eq_cast_of_dvd η.primitiveCharacter (conductor_dvd_level η) (-1 : (ZMod N)ˣ)
  rw [h] at e
  have hc : (((-1 : (ZMod N)ˣ) : ZMod N).cast : ZMod η.conductor) = -1 := by
    have : ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := by simp
    rw [this]
    have h1 : (ZMod.castHom (conductor_dvd_level η) (ZMod η.conductor)) (-1 : ZMod N) = -1 := by
      rw [map_neg, map_one]
    simpa [ZMod.castHom_apply] using h1
  rw [hc] at e
  simpa using e.symm

/-! ## eta2 = eta3 = 1 -/

theorem primeFactors_dm (k j a : ℕ) (hj : 1 ≤ j) (p : ℕ) (hp : p ∈ (dm (2 ^ (k + 3) * 3 ^ j) a).primeFactors) :
    p = 2 ∨ p = 3 := by
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  have hM : p ∣ 2 ^ (k + 3) * 3 ^ j := hpd.trans (dm_dvd k j a)
  rcases (Nat.Prime.dvd_mul hpp).1 hM with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h)
  · right; exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h)

theorem bracket_triv_formula (r k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (a : ℕ) (ha5 : ¬ 5 ∣ a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ (k + 3))) (1 : DirichletCharacter ℂ (3 ^ j)))) a =
      (((2 ^ (k + 3) * 3 ^ j).totient : ℂ) / ((dm (2 ^ (k + 3) * 3 ^ j) a).totient : ℂ)) *
        ψ ((a / (2 ^ (k + 3) * 3 ^ j).gcd a : ℕ) : ZMod (5 ^ r)) *
        ∏ ℓ ∈ (dm (2 ^ (k + 3) * 3 ^ j) a).primeFactors, (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹) := by
  haveI : NeZero (2 ^ (k + 3)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [bracket_gen r k j ψ hψ _ _ a ha5]
  have hc2 : (1 : DirichletCharacter ℂ (2 ^ (k + 3))).conductor = 1 := conductor_one
  have hc3 : (1 : DirichletCharacter ℂ (3 ^ j)).conductor = 1 := conductor_one
  simp only [star_one, mul_one, inv_one]
  rw [hc2, hc3, mul_one, if_pos (one_dvd _)]
  have hE : eulerPrimes (dm (2 ^ (k + 3) * 3 ^ j) a) 1 = (dm (2 ^ (k + 3) * 3 ^ j) a).primeFactors := by
    ext ℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, fun h1 => h.1.one_lt.ne' (Nat.dvd_one.1 h1)⟩
  rw [hE]

theorem bracket_triv_ne_zero (r k j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (h2 : ψ (2 : ZMod (5 ^ r)) ≠ 1) (h3 : ψ (3 : ZMod (5 ^ r)) ≠ 1)
    (a : ℕ) (ha5 : ¬ 5 ∣ a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ (k + 3))) (1 : DirichletCharacter ℂ (3 ^ j)))) a ≠ 0 := by
  rw [bracket_triv_formula r k j ψ hψ a ha5]
  set M := 2 ^ (k + 3) * 3 ^ j with hM
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
    exact nz ψ _ hu
  have hprod : ∏ ℓ ∈ (dm M a).primeFactors, (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ℓ hℓ
    rcases primeFactors_dm k j a hj ℓ hℓ with rfl | rfl
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

/-! ## values without Euler primes (MID) -/

theorem bracket_val_noeuler (r k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (hj : 1 ≤ j)
    (hdvd : η2.conductor * η3.conductor ∣ dm (2 ^ (k + 3) * 3 ^ j) a)
    (h2 : 2 ∣ η2.conductor * η3.conductor) (h3 : 3 ∣ η2.conductor * η3.conductor) :
    bracket (chi ψ (chi η2 η3)) a =
      (((2 ^ (k + 3) * 3 ^ j).totient : ℂ) / ((dm (2 ^ (k + 3) * 3 ^ j) a).totient : ℂ)) *
        ψ ((a / (2 ^ (k + 3) * 3 ^ j).gcd a : ℕ) : ZMod (5 ^ r)) *
        (η2.primitiveCharacter ((a / (2 ^ (k + 3) * 3 ^ j).gcd a : ℕ) : ZMod η2.conductor) *
          η3.primitiveCharacter ((a / (2 ^ (k + 3) * 3 ^ j).gcd a : ℕ) : ZMod η3.conductor)) := by
  rw [bracket_gen r k j ψ hψ η2 η3 a ha5, if_pos hdvd]
  have hE : eulerPrimes (dm (2 ^ (k + 3) * 3 ^ j) a) (η2.conductor * η3.conductor) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun ℓ hℓ => ?_)
    simp only [eulerPrimes, Finset.mem_filter] at hℓ
    obtain ⟨hl, hnf⟩ := hℓ
    rcases primeFactors_dm k j a hj ℓ hl with rfl | rfl
    · exact hnf h2
    · exact hnf h3
  rw [hE, Finset.prod_empty, mul_one]

/-! ## existence of characters -/

theorem exists_eta3 (j D : ℕ) (hD : D ∣ 3 ^ j) :
    ∃ η3 : DirichletCharacter ℂ (3 ^ j), η3.conductor = D := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨μ, hμ, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hD
  rcases Nat.eq_zero_or_pos μ with rfl | hμpos
  · exact ⟨1, by simpa using (conductor_one : (1 : DirichletCharacter ℂ (3 ^ j)).conductor = 1)⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ω, hω⟩ := Erdos634.LemmaSGpp.exists_primitive_pp (q := 3) (v := μ) hμpos (by
      intro h
      have : 3 ^ 1 ≤ 3 ^ μ := Nat.pow_le_pow_right (by norm_num) hμpos
      omega)
    haveI : NeZero (3 ^ μ) := ⟨pow_ne_zero _ (by norm_num)⟩
    exact ⟨changeLevel (pow_dvd_pow 3 hμ) ω,
      Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive (pow_dvd_pow 3 hμ) hω⟩

/-- A TOP instance: psi primitive mod 5^r, eta2 primitive mod 2^(k+3), eta3 of conductor exactly D, chi odd. -/
theorem exists_top (r k j D : ℕ) (hr : 1 ≤ r) (hD : D ∣ 3 ^ j) :
    ∃ (ψ : DirichletCharacter ℂ (5 ^ r)) (η2 : DirichletCharacter ℂ (2 ^ (k + 3)))
      (η3 : DirichletCharacter ℂ (3 ^ j)), ψ.IsPrimitive ∧ η2.IsPrimitive ∧ η3.conductor = D ∧
        ψ (-1) * η2 (-1) * η3 (-1) = -1 := by
  obtain ⟨η3, hη3⟩ := exists_eta3 j D hD
  obtain ⟨η2, hη2⟩ := nonempty_par2 k 1 (Or.inl rfl)
  obtain ⟨hη2p, hη2s⟩ := mem_PrimPar.1 hη2
  obtain ⟨ψ, hψ⟩ := nonempty5 r hr (-(η2 (-1) * η3 (-1))) (by
    rcases sign_val η2 with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num)
  obtain ⟨hψp, hψs⟩ := mem_PrimPar.1 hψ
  refine ⟨ψ, η2, η3, hψp, hη2p, hη3, ?_⟩
  rw [hψs]
  rcases sign_val η2 with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num

theorem four_odd (χ : DirichletCharacter ℂ (2 ^ 2)) (hχ : χ.IsPrimitive) : χ (-1) = -1 := by
  haveI : Fact (1 < 2 ^ 2) := ⟨by norm_num⟩
  rcases sign_val χ with h | h
  · exfalso
    have hone : χ = 1 := by
      ext a
      have key : ∀ a : ZMod (2 ^ 2), a = 0 ∨ a = 1 ∨ a = 2 ∨ a = -1 := by decide
      rcases key (a : ZMod (2 ^ 2)) with h0 | h0 | h0 | h0
      · exfalso; have := a.isUnit; rw [h0] at this; exact not_isUnit_zero this
      · rw [h0, MulChar.map_one, MulChar.map_one]
      · exfalso
        have := a.isUnit
        rw [h0] at this
        have h22 : ¬ IsUnit (2 : ZMod (2 ^ 2)) := by
          rw [show (2 : ZMod (2 ^ 2)) = ((2 : ℕ) : ZMod (2 ^ 2)) by norm_num, ZMod.isUnit_iff_coprime]
          norm_num
        exact h22 this
      · rw [h0, h, MulChar.one_apply (isUnit_one.neg)]
    have hc := (eq_one_iff_conductor_eq_one).1 hone
    rw [show χ.conductor = 2 ^ 2 from hχ] at hc
    omega
  · exact h

theorem changeLevel_neg_one {d n : ℕ} [NeZero d] [NeZero n] (h : d ∣ n) (ω : DirichletCharacter ℂ d) :
    changeLevel h ω (-1) = ω (-1) := by
  have e := changeLevel_eq_cast_of_dvd ω h (-1 : (ZMod n)ˣ)
  have hc : (((-1 : (ZMod n)ˣ) : ZMod n).cast : ZMod d) = -1 := by
    have : ((-1 : (ZMod n)ˣ) : ZMod n) = -1 := by simp
    rw [this]
    have h1 : (ZMod.castHom h (ZMod d)) (-1 : ZMod n) = -1 := by
      rw [map_neg, map_one]
    simpa [ZMod.castHom_apply] using h1
  rw [hc] at e
  simpa using e

/-- MID characters: eta2 mod 2^(k+3) odd of conductor exactly 2^(k+2) (>= 4). -/
theorem exists_mid_eta2 (k : ℕ) :
    ∃ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.conductor = 2 ^ (k + 2) ∧ η2 (-1) = -1 := by
  rcases k with _ | k'
  · obtain ⟨ω, hω⟩ := Erdos634.LemmaSGpp.exists_primitive_pp (q := 2) (v := 2) (by norm_num) (by norm_num)
    haveI : NeZero (2 ^ 2) := ⟨by norm_num⟩
    haveI : NeZero (2 ^ (0 + 3)) := ⟨by norm_num⟩
    refine ⟨changeLevel (pow_dvd_pow 2 (by norm_num : 2 ≤ 0 + 3)) ω, ?_, ?_⟩
    · exact Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive (pow_dvd_pow 2 (by norm_num : 2 ≤ 0 + 3)) hω
    · rw [changeLevel_neg_one, four_odd ω hω]
  · obtain ⟨ω, hω⟩ := nonempty_par2 k' (-1) (Or.inr rfl)
    obtain ⟨hωp, hωs⟩ := mem_PrimPar.1 hω
    haveI : NeZero (2 ^ (k' + 3)) := ⟨by positivity⟩
    haveI : NeZero (2 ^ (k' + 1 + 3)) := ⟨by positivity⟩
    refine ⟨changeLevel (pow_dvd_pow 2 (by omega : k' + 3 ≤ k' + 1 + 3)) ω, ?_, ?_⟩
    · exact Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive (pow_dvd_pow 2 (by omega : k' + 3 ≤ k' + 1 + 3)) hωp
    · rw [changeLevel_neg_one, hωs]

/-- MID eta3: odd, conductor exactly 3, as a character mod 3^j (j >= 1). -/
theorem exists_mid_eta3 (j : ℕ) (hj : 1 ≤ j) :
    ∃ η3 : DirichletCharacter ℂ (3 ^ j), η3.conductor = 3 ∧ η3 (-1) = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := Erdos634.LemmaSGpp.exists_primitive_pp (q := 3) (v := 1) le_rfl (by norm_num)
  haveI : NeZero (3 ^ 1) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hne : ω ≠ 1 := by
    intro h1
    have hc := (eq_one_iff_conductor_eq_one).1 h1
    rw [show ω.conductor = 3 ^ 1 from hω] at hc
    omega
  have hdvd : 3 ^ 1 ∣ 3 ^ j := pow_dvd_pow 3 hj
  refine ⟨changeLevel hdvd ω, ?_, ?_⟩
  · simpa using Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive hdvd hω
  · rw [changeLevel_neg_one, three_odd ω hne]

theorem exists_mid (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    ∃ (ψ : DirichletCharacter ℂ (5 ^ r)) (η2 : DirichletCharacter ℂ (2 ^ (k + 3)))
      (η3 : DirichletCharacter ℂ (3 ^ j)), ψ.IsPrimitive ∧ η2.conductor = 2 ^ (k + 2) ∧ η3.conductor = 3 ∧
        ψ (-1) = -1 ∧ η2 (-1) = -1 ∧ η3 (-1) = -1 := by
  obtain ⟨η2, h2c, h2o⟩ := exists_mid_eta2 k
  obtain ⟨η3, h3c, h3o⟩ := exists_mid_eta3 j hj
  obtain ⟨ψ, hψ⟩ := nonempty5 r hr (-1) (Or.inr rfl)
  obtain ⟨hψp, hψs⟩ := mem_PrimPar.1 hψ
  exact ⟨ψ, η2, η3, hψp, h2c, h3c, hψs, h2o, h3o⟩

end Erdos634.GA2NB2

#print axioms Erdos634.GA2NB2.star_neg_one
#print axioms Erdos634.GA2NB2.bracket_triv_formula
#print axioms Erdos634.GA2NB2.bracket_triv_ne_zero
#print axioms Erdos634.GA2NB2.bracket_val_noeuler
#print axioms Erdos634.GA2NB2.exists_eta3
#print axioms Erdos634.GA2NB2.exists_top
#print axioms Erdos634.GA2NB2.exists_mid
