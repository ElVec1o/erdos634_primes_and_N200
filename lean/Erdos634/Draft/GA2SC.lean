/-
GA2S, atom C: component formulas at 5^r (r >= 2) with 2-part chi_4 or trivial, for Prop K-a (i = 2, n = 4 * 5^r * 3^j, j >= 1).

  `H3K`               : the labelled hypothesis (triple (X, Y, S), psi primitive mod 5^r, eta2 mod 4, eta3 mod 3^j, odd product).
  `bracket_Ka`        : chi_4 primitive odd, ANY eta3 mod 3^j: there is kappa != 0 (independent of the entry) with
                        [a/n]_{psi chi4 eta3} = kappa psi(a) chi4(a) eta3(a) for every a prime to 5 and to 6.
                        (kappa = the Euler factor at 3: 1 + conj psi(3) if eta3 = 1, else 1; nonzero since psi(3) != -1 for r >= 2.)
  `bracket_triv_odd_r`, `bracket_triv_four_r` : the trivial-character brackets at 5^r (copies of GA2PE at r).
  `bracket_even_zero_r` : chi_4 kills even entries.
  `exists_L1char_r`   : psi primitive mod 5^r and eta3 of any prescribed conductor D | 3^j with psi chi4 eta3 odd.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SA
import Erdos634.Draft.GA2PG

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SC

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PF

def H3K (r j : ℕ) (aX aY aS : ℕ) (eX eY eS : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
    ∀ η2 : DirichletCharacter ℂ (2 ^ 2), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η2 (-1) * η3 (-1) = -1 →
      eX * bracket (chi ψ (chi η2 η3)) aX + eY * bracket (chi ψ (chi η2 η3)) aY +
        eS * bracket (chi ψ (chi η2 η3)) aS = 0

theorem H3K_swap {r j : ℕ} {aX aY aS : ℕ} {eX eY eS : ℂ} (H : H3K r j aX aY aS eX eY eS) :
    H3K r j aY aX aS eY eX eS := by
  intro ψ hψ η2 η3 hodd
  have := H ψ hψ η2 η3 hodd
  linear_combination this

theorem bracket_Ka (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4 : χ4.IsPrimitive) (hχ4o : χ4 (-1) = -1)
    (η3 : DirichletCharacter ℂ (3 ^ j)) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ a : ℕ, ¬ 5 ∣ a → Nat.Coprime (2 ^ 2 * 3 ^ j) a →
      bracket (chi ψ (chi χ4 η3)) a =
        κ * (ψ (a : ZMod (5 ^ r)) * (χ4 (a : ZMod (2 ^ 2)) * η3 (a : ZMod (3 ^ j)))) := by
  haveI : NeZero (2 ^ 2) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc4 : χ4.conductor = 2 ^ 2 := hχ4
  have hfd : η3.conductor ∣ 3 ^ j := conductor_dvd_level η3
  refine ⟨∏ ℓ ∈ eulerPrimes (2 ^ 2 * 3 ^ j) (χ4.conductor * η3.conductor),
    (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹ * (χ4.primitiveCharacter (ℓ : ZMod χ4.conductor) *
      η3.primitiveCharacter (ℓ : ZMod η3.conductor))⁻¹), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro ℓ hℓ
    simp only [eulerPrimes, Finset.mem_filter] at hℓ
    obtain ⟨hlM, hnf⟩ := hℓ
    have hl' := hlM
    rw [pf_M j hj] at hl'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with rfl | rfl
    · exfalso
      apply hnf
      rw [hc4]
      exact Dvd.dvd.mul_right (by norm_num) _
    · have hc3 : η3.conductor = 1 := by
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hfd
        rcases Nat.eq_zero_or_pos k with rfl | hkp
        · simpa using hk'
        · exfalso
          apply hnf
          rw [hk']
          exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
      have hsub : Subsingleton (ZMod η3.conductor) := by rw [hc3]; infer_instance
      rw [Subsingleton.elim (((3 : ℕ)) : ZMod η3.conductor) 1, MulChar.map_one,
        primChar_nat_of_isPrimitive hχ4 3]
      have h3m : χ4 ((3 : ℕ) : ZMod (2 ^ 2)) = -1 := by
        have : ((3 : ℕ) : ZMod (2 ^ 2)) = -1 := by decide
        rw [this, hχ4o]
      rw [h3m]
      intro h0
      apply Erdos634.GA2SA.psi_three_ne_neg_one r hr ψ hψ
      have h1 : (ψ ((3 : ℕ) : ZMod (5 ^ r)))⁻¹ = -1 := by linear_combination h0
      have h2 := inv_eq_iff_eq_inv.1 h1
      simpa using h2
  · intro a ha5 hcop
    have hg1 : (2 ^ 2 * 3 ^ j).gcd a = 1 := hcop
    have hdm : dm (2 ^ 2 * 3 ^ j) a = 2 ^ 2 * 3 ^ j := by unfold dm; rw [hg1, Nat.div_one]
    have hMpos : 0 < 2 ^ 2 * 3 ^ j := by positivity
    have hdvd : χ4.conductor * η3.conductor ∣ dm (2 ^ 2 * 3 ^ j) a := by
      rw [hdm, hc4]; exact Nat.mul_dvd_mul_left _ hfd
    have hc3a : Nat.Coprime (3 ^ j) a := Nat.Coprime.coprime_dvd_left
      (Dvd.dvd.mul_left (dvd_refl _) _) hcop
    rw [bracket_gen2 r 2 j ψ hψ χ4 η3 a ha5, if_pos hdvd, hdm, hg1, Nat.div_one,
      div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'),
      primChar_nat_of_isPrimitive hχ4 a, star_eq_of_coprime η3 a hc3a.symm]
    ring

theorem bracket_triv_odd_r (r j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (a : ℕ) (ha5 : ¬ 5 ∣ a) (hcop : Nat.Coprime (2 ^ 2 * 3 ^ j) a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 2)) (1 : DirichletCharacter ℂ (3 ^ j)))) a =
      ψ (a : ZMod (5 ^ r)) * ((1 - (ψ (2 : ZMod (5 ^ r)))⁻¹) * (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹)) := by
  rw [bracket_triv_formula2 r 2 j ψ hψ a ha5]
  have hg1 : (2 ^ 2 * 3 ^ j).gcd a = 1 := hcop
  have hdm : dm (2 ^ 2 * 3 ^ j) a = 2 ^ 2 * 3 ^ j := by unfold dm; rw [hg1, Nat.div_one]
  have hMpos : 0 < 2 ^ 2 * 3 ^ j := by positivity
  rw [hdm, hg1, Nat.div_one, div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne'), pf_M j hj,
    Finset.prod_pair (by norm_num)]
  simp only [Nat.cast_ofNat, one_mul]

theorem bracket_triv_four_r (r j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (b : ℕ) (hb5 : ¬ 5 ∣ 4 * b) (hb3 : ¬ 3 ∣ b) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 2)) (1 : DirichletCharacter ℂ (3 ^ j)))) (4 * b) =
      2 * ψ (b : ZMod (5 ^ r)) * (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹) := by
  rw [bracket_triv_formula2 r 2 j ψ hψ (4 * b) hb5]
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

theorem bracket_even_zero_r (r j : ℕ) (hr : 1 ≤ r) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4 : χ4.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ) (hSe : a % 2 = 0) :
    bracket (chi ψ (chi χ4 η3)) a = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases h5 : 5 ∣ a
  · exact bracket_p_dvd (p := 5) (r := r) hr (not5_dvd' 2 j) hψ _ a h5
  · rw [bracket_gen2 r 2 j ψ hψ χ4 η3 a h5, if_neg]
    intro hdv
    have hc4 : χ4.conductor = 2 ^ 2 := hχ4
    have h4 : 4 ∣ dm (2 ^ 2 * 3 ^ j) a := by
      have : 2 ^ 2 ∣ χ4.conductor * η3.conductor := by rw [hc4]; exact dvd_mul_right _ _
      simpa using this.trans hdv
    have hg : (2 ^ 2 * 3 ^ j).gcd a ∣ 2 ^ 2 * 3 ^ j := Nat.gcd_dvd_left _ _
    have h2g : 2 ∣ (2 ^ 2 * 3 ^ j).gcd a :=
      Nat.dvd_gcd (Dvd.dvd.mul_right (by norm_num) _) (by omega)
    have hmul : dm (2 ^ 2 * 3 ^ j) a * (2 ^ 2 * 3 ^ j).gcd a = 2 ^ 2 * 3 ^ j := Nat.div_mul_cancel hg
    have h8 : 2 * 4 ∣ 2 ^ 2 * 3 ^ j := by
      rw [← hmul]; exact Nat.mul_dvd_mul h2g h4 |>.trans (by rw [mul_comm])
    have h2j : 2 ∣ 3 ^ j := by
      have : 2 ^ 2 * 2 ∣ 2 ^ 2 * 3 ^ j := by simpa [mul_comm] using h8
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2j
    omega

theorem exists_L1char_r (r : ℕ) (hr : 1 ≤ r) (j : ℕ) (D : ℕ) (hD : D ∣ 3 ^ j)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4o : χ4 (-1) = -1) :
    ∃ (ψ : DirichletCharacter ℂ (5 ^ r)) (η3 : DirichletCharacter ℂ (3 ^ j)),
      ψ.IsPrimitive ∧ η3.conductor = D ∧ ψ (-1) * χ4 (-1) * η3 (-1) = -1 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨l, hl, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hD
  rcases Nat.eq_zero_or_pos l with rfl | hlp
  · obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 r hr 1 (Or.inl rfl)
    obtain ⟨hψp, hψs⟩ := Erdos634.GA2LCore.mem_PrimPar.1 hψ
    refine ⟨ψ, 1, hψp, by simpa using (DirichletCharacter.conductor_one : (1 : DirichletCharacter ℂ (3 ^ j)).conductor = 1), ?_⟩
    rw [hψs, hχ4o, MulChar.one_apply (isUnit_one.neg)]; norm_num
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hodd3 : 3 ^ l % 2 = 1 := by
      have : Odd (3 ^ l) := Odd.pow (by decide)
      exact Nat.odd_iff.1 this
    obtain ⟨ω, hωp, hωo⟩ := (Erdos634.LemmaSParity.exists_odd_primitive_iff
      (d := 3 ^ l) (pow_ne_zero _ (by norm_num)) (by omega)).2
      ⟨by
        intro h
        have : 3 ^ 1 ≤ 3 ^ l := Nat.pow_le_pow_right (by norm_num) hlp
        omega, by omega⟩
    haveI : NeZero (3 ^ l) := ⟨pow_ne_zero _ (by norm_num)⟩
    obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 r hr (-1) (Or.inr rfl)
    obtain ⟨hψp, hψs⟩ := Erdos634.GA2LCore.mem_PrimPar.1 hψ
    refine ⟨ψ, changeLevel (pow_dvd_pow 3 hl) ω, hψp,
      Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive (pow_dvd_pow 3 hl) hωp, ?_⟩
    have hω1 : ω (-1) = -1 := hωo
    rw [Erdos634.GA2NB2.changeLevel_neg_one, hω1, hψs, hχ4o]; norm_num

end Erdos634.GA2SC

#print axioms Erdos634.GA2SC.bracket_Ka
#print axioms Erdos634.GA2SC.bracket_triv_odd_r
#print axioms Erdos634.GA2SC.bracket_triv_four_r
#print axioms Erdos634.GA2SC.bracket_even_zero_r
#print axioms Erdos634.GA2SC.exists_L1char_r
