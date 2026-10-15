/-
GA2N, item (2c): **the full analytic Lemma A3 (TOP) for general r >= 1, general j >= 1, i = k+3 >= 3**
(GA2Y_NOTES Theorem A, Lemma A3), the r >= 2 / j >= 1 extension of `GA2MTop.top_chain` and `GA2NJ1.top_chain_j1`.

* `bracket_top_R`, `bracket_even_R`, `bracket_top_triv_R`: component formula at 5^r (the existing `LemmaSPhi.bracket_unit`
  is r-generic); eta3 != 1: [a/n]_chi = psi(a) eta2(a) eta3(a); eta3 = 1: extra Euler factor (1 - conj(psi eta2)(3)).
* `shape_arith_R`: shape arithmetic with n = 2^(k+3) 3^j 5^r.
* `top_shape_R`, `top_chain_R`: sum equation (all odd top chi; eta3 = 1 included iff j = 1) with eP != 0
  => shape A (eQ = eP, |aP - aQ| = n/2) or shape B (eQ = -eP, aP + aQ = n/2).
* Witnesses: r = 2, k = 0, j in {1, 2}, n = 600 / 1800, shapes A and B; the whole analytic equation holds and `top_chain_R` applies.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NR1

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NR2

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2LGroup Erdos634.GA2MChain Erdos634.GA2LCore Erdos634.GA2MTop Erdos634.GA2LPar
open Erdos634.GA2LShape Erdos634.GA2MF4 Erdos634.GA2NG Erdos634.GA2NJ1 Erdos634.GA2NR1

/-! ## A. component formulas at 5^r -/

theorem bracket_top_R (r k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3 ≠ 1) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (hcop : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a) :
    bracket (chi ψ (chi η2 η3)) a =
      ψ (a : ZMod (5 ^ r)) * η2 (a : ZMod (2 ^ (k + 3))) * η3 (a : ZMod (3 ^ j)) := by
  set η : DirichletCharacter ℂ (2 ^ (k + 3) * 3 ^ j) := chi η2 η3 with hη
  rw [bracket_unit (not5_dvd k j) hψ η a ha5]
  have hdm : dm (2 ^ (k + 3) * 3 ^ j) a = 2 ^ (k + 3) * 3 ^ j := by
    unfold dm; rw [hcop, Nat.div_one]
  have hg : (2 ^ (k + 3) * 3 ^ j).gcd a = 1 := hcop
  rw [hdm, hg, Nat.div_one]
  have hf : η.conductor ∣ 2 ^ (k + 3) * 3 ^ j := conductor_dvd_level η
  rw [if_pos hf]
  have hE : eulerPrimes (2 ^ (k + 3) * 3 ^ j) η.conductor = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun ℓ hℓ => ?_)
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hℓ
    obtain ⟨⟨hl, hld, -⟩, hnf⟩ := hℓ
    have hc : η.conductor = 2 ^ (k + 3) * η3.conductor := cond_eta k j η2 hη2 η3
    rcases (Nat.Prime.dvd_mul hl).1 hld with h | h
    · have := Nat.Prime.dvd_of_dvd_pow hl h
      have h2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 this
      subst h2
      exact hnf (hc ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
    · have := Nat.Prime.dvd_of_dvd_pow hl h
      have h3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).1 this
      subst h3
      have hne : η3.conductor ≠ 1 := fun h1 => hη3 ((eq_one_iff_conductor_eq_one).2 h1)
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (conductor_dvd_level η3)
      have hi0 : i ≠ 0 := by rintro rfl; exact hne (by simpa using hi')
      exact hnf (hc ▸ dvd_mul_of_dvd_right (hi' ▸ dvd_pow_self 3 hi0) _)
  rw [hE, Finset.prod_empty, mul_one]
  have hφ : ((2 ^ (k + 3) * 3 ^ j).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
  rw [div_self hφ, one_mul]
  have hstar : η.primitiveCharacter (a : ZMod η.conductor) = η (a : ZMod (2 ^ (k + 3) * 3 ^ j)) := by
    conv_rhs => rw [← changeLevel_primitiveCharacter η]
    rw [changeLevel_nat _ _ a hcop.symm]
  have hmul : η (a : ZMod (2 ^ (k + 3) * 3 ^ j)) =
      η2 (a : ZMod (2 ^ (k + 3))) * η3 (a : ZMod (3 ^ j)) := by
    have e : η = changeLevel (Nat.dvd_mul_right (2 ^ (k + 3)) (3 ^ j)) η2 *
        changeLevel (Nat.dvd_mul_left (3 ^ j) (2 ^ (k + 3))) η3 := rfl
    rw [e, MulChar.mul_apply, changeLevel_nat _ _ a hcop.symm, changeLevel_nat _ _ a hcop.symm]
  rw [hstar, hmul]; ring

theorem bracket_even_R (r : ℕ) (hr : 1 ≤ r) (k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ) (ha : 2 ∣ a) :
    bracket (chi ψ (chi η2 η3)) a = 0 := by
  set η : DirichletCharacter ℂ (2 ^ (k + 3) * 3 ^ j) := chi η2 η3 with hη
  by_cases h5 : 5 ∣ a
  · exact bracket_p_dvd hr (not5_dvd k j) hψ η a h5
  rw [bracket_unit (not5_dvd k j) hψ η a h5, if_neg]
  intro hf
  have hc : η.conductor = 2 ^ (k + 3) * η3.conductor := cond_eta k j η2 hη2 η3
  have h1 : 2 ^ (k + 3) ∣ dm (2 ^ (k + 3) * 3 ^ j) a :=
    (hc ▸ dvd_mul_right (2 ^ (k + 3)) _).trans hf
  have hg : 2 ∣ (2 ^ (k + 3) * 3 ^ j).gcd a :=
    Nat.dvd_gcd (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _) ha
  have hprod : dm (2 ^ (k + 3) * 3 ^ j) a * (2 ^ (k + 3) * 3 ^ j).gcd a = 2 ^ (k + 3) * 3 ^ j :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := hg
  rw [hu, hv] at hprod
  have : 2 ∣ 3 ^ j := by
    have h2 : 2 ^ (k + 3) * (2 * (u * v)) = 2 ^ (k + 3) * 3 ^ j := by rw [← hprod]; ring
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    exact ⟨u * v, this.symm⟩
  exact not2_dvd j this

theorem bracket_top_triv_R (r k j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (hcop : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a) :
    bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) a =
      ψ (a : ZMod (5 ^ r)) * η2 (a : ZMod (2 ^ (k + 3))) *
        (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹) := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set η3 : DirichletCharacter ℂ (3 ^ j) := 1 with hη3
  set η : DirichletCharacter ℂ (2 ^ (k + 3) * 3 ^ j) := chi η2 η3 with hη
  have hc3 : η3.conductor = 1 := conductor_one
  have hc : η.conductor = 2 ^ (k + 3) := by rw [cond_eta k j η2 hη2 η3, hc3, mul_one]
  rw [bracket_unit (not5_dvd k j) hψ η a ha5]
  have hdm : dm (2 ^ (k + 3) * 3 ^ j) a = 2 ^ (k + 3) * 3 ^ j := by
    unfold dm; rw [hcop, Nat.div_one]
  have hg : (2 ^ (k + 3) * 3 ^ j).gcd a = 1 := hcop
  rw [hdm, hg, Nat.div_one]
  have hf : η.conductor ∣ 2 ^ (k + 3) * 3 ^ j := conductor_dvd_level η
  rw [if_pos hf]
  have hE : eulerPrimes (2 ^ (k + 3) * 3 ^ j) η.conductor = {3} := by
    ext ℓ
    simp only [eulerPrimes, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hl, hld, -⟩, hnf⟩
      rcases (Nat.Prime.dvd_mul hl).1 hld with h | h
      · exfalso; apply hnf; rw [hc]; exact h
      · exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).1 (Nat.Prime.dvd_of_dvd_pow hl h)
    · rintro rfl
      refine ⟨⟨Nat.prime_three, dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) _, by positivity⟩, ?_⟩
      rw [hc]; intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
  rw [hE, Finset.prod_singleton]
  have hφ : ((2 ^ (k + 3) * 3 ^ j).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
  rw [div_self hφ, one_mul]
  have hstar : ∀ b : ℕ, η.primitiveCharacter (b : ZMod η.conductor) =
      η2 (b : ZMod (2 ^ (k + 3))) := by
    intro b
    have e : η = changeLevel (Nat.dvd_mul_right (2 ^ (k + 3)) (3 ^ j)) η2 *
        changeLevel (Nat.dvd_mul_left (3 ^ j) (2 ^ (k + 3))) η3 := rfl
    rw [primChar_mul_nat (Nat.Coprime.pow (k + 3) j (by norm_num)) e b,
      primChar_nat_of_isPrimitive hη2 b]
    have hsub : Subsingleton (ZMod η3.conductor) := by rw [hc3]; infer_instance
    rw [Subsingleton.elim (b : ZMod η3.conductor) 1, MulChar.map_one, mul_one]
  simp only [MulChar.inv_apply_eq_inv']
  rw [hstar a, hstar 3]
  simp only [Nat.cast_ofNat]

theorem isUnit_three_5R (r : ℕ) : IsUnit (3 : ZMod (5 ^ r)) := by
  have := (ZMod.isUnit_iff_coprime 3 (5 ^ r)).2 (Nat.Coprime.pow_right _ (by norm_num))
  simpa using this

/-! ## B. equations -/

def HypPR (r k j : ℕ) (ap aq : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
  ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
    ψ (-1) * η2 (-1) * η3 (-1) = -1 →
    ψ (ap : ZMod (5 ^ r)) * η2 (ap : ZMod (2 ^ (k + 3))) * η3 (ap : ZMod (3 ^ j)) =
      c * (ψ (aq : ZMod (5 ^ r)) * η2 (aq : ZMod (2 ^ (k + 3))) * η3 (aq : ZMod (3 ^ j)))

def HypTPR (r k : ℕ) (ap aq : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
    ψ (-1) * η2 (-1) = -1 →
    ψ (3 : ZMod (5 ^ r)) * η2 (3 : ZMod (2 ^ (k + 3))) ≠ 1 →
    ψ (ap : ZMod (5 ^ r)) * η2 (ap : ZMod (2 ^ (k + 3))) =
      c * (ψ (aq : ZMod (5 ^ r)) * η2 (aq : ZMod (2 ^ (k + 3))))

theorem top_equation_R (r k j : ℕ) (hr : 1 ≤ r) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hPc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aP) (hQc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aQ)
    (hS : 2 ∣ aS) (hePne : eP ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    HypPR r k j (aP : ℤ) (aQ : ℤ) (-(eQ / eP)) := by
  intro ψ hψ η2 hη2 η3 hη3 hodd
  have h := H ψ hψ η2 hη2 η3 hη3 hodd
  rw [bracket_top_R r k j ψ hψ η2 hη2 η3 hη3 aP hP5 hPc, bracket_top_R r k j ψ hψ η2 hη2 η3 hη3 aQ hQ5 hQc,
    bracket_even_R r hr k j ψ hψ η2 hη2 η3 aS hS, mul_zero, add_zero] at h
  simp only [Int.cast_natCast]
  field_simp
  linear_combination h

theorem triv_equation_R (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hPc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aP) (hQc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aQ)
    (hS : 2 ∣ aS) (hePne : eP ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
        ψ (-1) * η2 (-1) * (1 : DirichletCharacter ℂ (3 ^ j)) (-1) = -1 →
        eP * bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) aP +
          eQ * bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) aQ +
          eS * bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) aS = 0) :
    HypTPR r k (aP : ℤ) (aQ : ℤ) (-(eQ / eP)) := by
  intro ψ hψ η2 hη2 hodd hne
  have h := H ψ hψ η2 hη2 (by rw [MulChar.one_apply (isUnit_one.neg)]; simpa using hodd)
  rw [bracket_top_triv_R r k j hj ψ hψ η2 hη2 aP hP5 hPc, bracket_top_triv_R r k j hj ψ hψ η2 hη2 aQ hQ5 hQc,
    bracket_even_R r hr k j ψ hψ η2 hη2 1 aS hS, mul_zero, add_zero] at h
  set F : ℂ := 1 - (ψ (3 : ZMod (5 ^ r)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹ with hF
  have hFne : F ≠ 0 := by
    intro h0
    apply hne
    have h1 : (ψ (3 : ZMod (5 ^ r)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹ = 1 := by
      linear_combination (-1 : ℂ) * h0
    rw [← mul_inv, inv_eq_one] at h1
    exact h1
  have h2 : (eP * (ψ (aP : ZMod (5 ^ r)) * η2 (aP : ZMod (2 ^ (k + 3)))) +
      eQ * (ψ (aQ : ZMod (5 ^ r)) * η2 (aQ : ZMod (2 ^ (k + 3))))) * F = 0 := by
    linear_combination h
  have h3 := (mul_eq_zero.1 h2).resolve_right hFne
  simp only [Int.cast_natCast]
  field_simp
  linear_combination h3

/-! ## C. shape arithmetic with 5^r -/

theorem shape_arith_R (k j r : ℕ) (s e : ℕ) (hs : s < 2) (he : e < 2) (ap aq : ℤ)
    (hpo : Odd ap) (hqo : Odd aq) (hp : 0 < ap) (hq : 0 < aq)
    (hsum : ap + aq < 2 ^ (k + 3) * (3 ^ j * 5 ^ r)) (hne : ap ≠ aq)
    (c5 : ap ≡ (-1) ^ s * aq [ZMOD 5 ^ r]) (c3 : ap ≡ (-1) ^ s * aq [ZMOD 3 ^ j])
    (c2 : ap ≡ (-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e [ZMOD 2 ^ (k + 3)]) :
    e = 1 ∧ ((s = 0 ∧ (ap = aq + 2 ^ (k + 2) * (3 ^ j * 5 ^ r) ∨
        aq = ap + 2 ^ (k + 2) * (3 ^ j * 5 ^ r))) ∨
      (s = 1 ∧ ap + aq = 2 ^ (k + 2) * (3 ^ j * 5 ^ r))) := by
  set T : ℤ := 2 ^ (k + 2) with hT
  set m : ℤ := 3 ^ j * 5 ^ r with hm
  have hTpos : 0 < T := by positivity
  have hmpos : 0 < m := by positivity
  have hn : (2 : ℤ) ^ (k + 3) = 2 * T := by rw [hT]; ring
  have hmo : Odd m := by
    have h3 : Odd ((3 : ℤ) ^ j) := Odd.pow (by decide)
    have h5 : Odd ((5 : ℤ) ^ r) := Odd.pow (by decide)
    exact h3.mul h5
  have hcopT : IsCoprime m T := odd_cop m hmo (k + 2)
  have hcop2T : IsCoprime m (2 * T) := by
    have : IsCoprime m 2 := by
      obtain ⟨b, hb⟩ := hmo
      exact ⟨1, -b, by rw [hb]; ring⟩
    exact this.mul_right hcopT
  rw [hn] at hsum c2
  have hm1 : m ∣ ap - (-1) ^ s * aq := by
    have d5 : (5 : ℤ) ^ r ∣ ap - (-1) ^ s * aq := (Int.modEq_iff_dvd.1 c5.symm)
    have d3 : (3 : ℤ) ^ j ∣ ap - (-1) ^ s * aq := (Int.modEq_iff_dvd.1 c3.symm)
    have hc : IsCoprime ((3 : ℤ) ^ j) ((5 : ℤ) ^ r) :=
      IsCoprime.pow (show IsCoprime (3 : ℤ) 5 from ⟨2, -1, by norm_num⟩)
    rw [hm, mul_comm]
    exact hc.symm.mul_dvd d5 d3
  have d2 : 2 * T ∣ ap - (-1) ^ s * aq * (1 + T) ^ e := by
    have := Int.modEq_iff_dvd.1 c2.symm
    exact this
  obtain ⟨b, hb⟩ := hqo
  obtain ⟨b', hb'⟩ := hpo
  have hsum' : ap + aq < 2 * T * m := by rw [hm]; nlinarith [hsum]
  have hN : 0 < 2 * T * m := by positivity
  have hq2 : 2 * T ∣ aq * T - T := ⟨b, by rw [hb]; ring⟩
  have hq3 : 2 * T ∣ aq * T + T := ⟨b + 1, by rw [hb]; ring⟩
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
    · exfalso
      norm_num at hm1 d2
      have h0 := shape_e0 T m (ap - aq) hTpos hmpos hcop2T hm1 d2
      have := Int.eq_zero_of_abs_lt_dvd h0 (by rw [abs_lt]; constructor <;> linarith)
      exact hne (by linarith)
    · norm_num at hm1 d2
      have h2 : 2 * T ∣ (ap - aq) - T := by
        have := dvd_add d2 hq2
        convert this using 1; ring
      have := shape_e1 T m (ap - aq) hTpos hmpos hcopT hm1 h2
        (by rw [abs_lt]; constructor <;> nlinarith)
      refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
      rcases this with h | h
      · left; linarith
      · right; linarith
  · obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
    · exfalso
      norm_num at hm1 d2
      have hm1' : m ∣ ap + aq := by simpa using hm1
      have d2' : 2 * T ∣ ap + aq := by simpa using d2
      have h0 := shape_e0 T m (ap + aq) hTpos hmpos hcop2T hm1' d2'
      have := Int.eq_zero_of_abs_lt_dvd h0 (by rw [abs_lt]; constructor <;> linarith)
      linarith
    · norm_num at hm1 d2
      have hm1' : m ∣ ap + aq := by simpa using hm1
      have h2 : 2 * T ∣ (ap + aq) - T := by
        have := dvd_sub d2 hq3
        convert this using 1; ring
      have := shape_e1 T m (ap + aq) hTpos hmpos hcopT hm1' h2
        (by rw [abs_lt]; constructor <;> nlinarith)
      refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
      rcases this with h | h
      · linarith
      · exfalso; nlinarith

/-! ## D. chaining -/

theorem hyp_h_R (r k j : ℕ) (ap aq u : ℤ) (c : ℂ) (H : HypPR r k j ap aq c)
    (e5 : ((aq * u : ℤ) : ZMod (5 ^ r)) = 1) (e2 : ((aq * u : ℤ) : ZMod (2 ^ (k + 3))) = 1)
    (e3 : ((aq * u : ℤ) : ZMod (3 ^ j)) = 1) :
    HypR r k j (ap * u) (ap * u) (ap * u) c := by
  intro ψ hψ η2 hη2 η3 hη3 hodd
  have h := H ψ hψ η2 hη2 η3 hη3 hodd
  have k5 : ψ (aq * u : ℤ) = ψ (aq : ZMod (5 ^ r)) * ψ (u : ZMod (5 ^ r)) := by
    rw [← map_mul]; push_cast; rfl
  have k2 : η2 (aq * u : ℤ) = η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  have k3 : η3 (aq * u : ℤ) = η3 (aq : ZMod (3 ^ j)) * η3 (u : ZMod (3 ^ j)) := by
    rw [← map_mul]; push_cast; rfl
  rw [e5, map_one] at k5
  rw [e2, map_one] at k2
  rw [e3, map_one] at k3
  have m5 : ψ ((ap * u : ℤ) : ZMod (5 ^ r)) = ψ (ap : ZMod (5 ^ r)) * ψ (u : ZMod (5 ^ r)) := by
    rw [← map_mul]; push_cast; rfl
  have m2 : η2 ((ap * u : ℤ) : ZMod (2 ^ (k + 3))) =
      η2 (ap : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  have m3 : η3 ((ap * u : ℤ) : ZMod (3 ^ j)) = η3 (ap : ZMod (3 ^ j)) * η3 (u : ZMod (3 ^ j)) := by
    rw [← map_mul]; push_cast; rfl
  rw [m5, m2, m3]
  have := congrArg (fun x => x * (ψ (u : ZMod (5 ^ r)) * η2 (u : ZMod (2 ^ (k + 3))) *
      η3 (u : ZMod (3 ^ j)))) h
  simp only at this
  calc _ = (ψ (ap : ZMod (5 ^ r)) * η2 (ap : ZMod (2 ^ (k + 3))) * η3 (ap : ZMod (3 ^ j))) *
        (ψ (u : ZMod (5 ^ r)) * η2 (u : ZMod (2 ^ (k + 3))) * η3 (u : ZMod (3 ^ j))) := by ring
    _ = _ := this
    _ = c * ((ψ (aq : ZMod (5 ^ r)) * ψ (u : ZMod (5 ^ r))) *
        (η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3)))) *
        (η3 (aq : ZMod (3 ^ j)) * η3 (u : ZMod (3 ^ j)))) := by ring
    _ = c := by rw [← k5, ← k2, ← k3]; simp

theorem hypT_h_R (r k : ℕ) (ap aq u : ℤ) (c : ℂ) (H : HypTPR r k ap aq c)
    (e5 : ((aq * u : ℤ) : ZMod (5 ^ r)) = 1) (e2 : ((aq * u : ℤ) : ZMod (2 ^ (k + 3))) = 1) :
    HypTR r k (ap * u) (ap * u) c := by
  intro ψ hψ η2 hη2 hodd hne
  have h := H ψ hψ η2 hη2 hodd hne
  have k5 : ψ (aq * u : ℤ) = ψ (aq : ZMod (5 ^ r)) * ψ (u : ZMod (5 ^ r)) := by
    rw [← map_mul]; push_cast; rfl
  have k2 : η2 (aq * u : ℤ) = η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  rw [e5, map_one] at k5
  rw [e2, map_one] at k2
  have m5 : ψ ((ap * u : ℤ) : ZMod (5 ^ r)) = ψ (ap : ZMod (5 ^ r)) * ψ (u : ZMod (5 ^ r)) := by
    rw [← map_mul]; push_cast; rfl
  have m2 : η2 ((ap * u : ℤ) : ZMod (2 ^ (k + 3))) =
      η2 (ap : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  rw [m5, m2]
  have := congrArg (fun x => x * (ψ (u : ZMod (5 ^ r)) * η2 (u : ZMod (2 ^ (k + 3))))) h
  simp only at this
  calc _ = (ψ (ap : ZMod (5 ^ r)) * η2 (ap : ZMod (2 ^ (k + 3)))) *
        (ψ (u : ZMod (5 ^ r)) * η2 (u : ZMod (2 ^ (k + 3)))) := by ring
    _ = _ := this
    _ = c * ((ψ (aq : ZMod (5 ^ r)) * ψ (u : ZMod (5 ^ r))) *
        (η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))))) := by ring
    _ = c := by rw [← k5, ← k2]; simp

theorem top_shape_R (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (ap aq : ℤ) (c : ℂ)
    (hpo : Odd ap) (hqo : Odd aq) (hp : 0 < ap) (hq : 0 < aq)
    (hp3 : IsCoprime ap 3) (hq3 : IsCoprime aq 3) (hp5 : IsCoprime ap 5) (hq5 : IsCoprime aq 5)
    (hsum : ap + aq < 2 ^ (k + 3) * (3 ^ j * 5 ^ r)) (hne : ap ≠ aq)
    (H : HypPR r k j ap aq c) (HT : j = 1 → HypTPR r k ap aq c) :
    ∃ s e : ℕ, s < 2 ∧ e = 1 ∧ c = (-1) ^ (s + e) ∧
      ((s = 0 ∧ (ap = aq + 2 ^ (k + 2) * (3 ^ j * 5 ^ r) ∨ aq = ap + 2 ^ (k + 2) * (3 ^ j * 5 ^ r))) ∨
        (s = 1 ∧ ap + aq = 2 ^ (k + 2) * (3 ^ j * 5 ^ r))) := by
  have cp2 : ∀ a : ℤ, Odd a → IsCoprime a ((2 ^ (k + 3) : ℕ) : ℤ) := fun a ha => by
    have := odd_cop a ha (k + 3); push_cast; exact this
  have cp3 : ∀ a : ℤ, IsCoprime a 3 → IsCoprime a ((3 ^ j : ℕ) : ℤ) := fun a ha => by
    have := ha.pow_right (n := j); push_cast; exact this
  have cp5 : ∀ a : ℤ, IsCoprime a 5 → IsCoprime a ((5 ^ r : ℕ) : ℤ) := fun a ha => by
    have := ha.pow_right (n := r); push_cast; exact this
  have cpn : IsCoprime aq (((2 ^ (k + 3) * (3 ^ j * 5 ^ r) : ℕ)) : ℤ) := by
    have h1 := (cp2 aq hqo)
    have h2 : IsCoprime aq (((3 ^ j * 5 ^ r : ℕ)) : ℤ) := by
      have := (hq3.pow_right (n := j)).mul_right (hq5.pow_right (n := r))
      push_cast; exact this
    push_cast at h1 h2 ⊢
    exact h1.mul_right h2
  obtain ⟨u, v, huv⟩ := cpn
  have dvd_n : ∀ m : ℕ, (m : ℤ) ∣ ((2 ^ (k + 3) * (3 ^ j * 5 ^ r) : ℕ) : ℤ) →
      ((aq * u : ℤ) : ZMod m) = 1 := by
    intro m hm
    have h1 : (aq * u : ℤ) = 1 - v * ((2 ^ (k + 3) * (3 ^ j * 5 ^ r) : ℕ) : ℤ) := by linarith
    have : (((2 ^ (k + 3) * (3 ^ j * 5 ^ r) : ℕ) : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hm
    rw [h1]; push_cast at this ⊢; rw [this]; simp
  have e5 := dvd_n (5 ^ r) ⟨2 ^ (k + 3) * 3 ^ j, by push_cast; ring⟩
  have e2 := dvd_n (2 ^ (k + 3)) ⟨3 ^ j * 5 ^ r, by push_cast; ring⟩
  have e3 := dvd_n (3 ^ j) ⟨2 ^ (k + 3) * 5 ^ r, by push_cast; ring⟩
  have Hh := hyp_h_R r k j ap aq u c H e5 e2 e3
  have unit_h : ∀ (m : ℕ), ((aq * u : ℤ) : ZMod m) = 1 → IsCoprime ap (m : ℤ) →
      IsUnit ((ap * u : ℤ) : ZMod m) := by
    intro m em hc
    have hu : IsUnit (u : ZMod m) := by
      push_cast at em
      exact IsUnit.of_mul_eq_one (aq : ZMod m) (by rw [mul_comm]; exact em)
    push_cast
    exact (unit_of_coprime ap m hc).mul hu
  have rel : ∀ (m : ℕ), ((aq * u : ℤ) : ZMod m) = 1 →
      (ap : ZMod m) = ((ap * u : ℤ) : ZMod m) * (aq : ZMod m) := by
    intro m em
    push_cast at em ⊢
    linear_combination (-(ap : ZMod m)) * em
  obtain ⟨s, e, hs, he, g5, g3, g2, gc⟩ := group_core_R r k j hr hj (ap * u) (ap * u) (ap * u) c
    (unit_h (5 ^ r) e5 (cp5 ap hp5)) (unit_h (2 ^ (k + 3)) e2 (cp2 ap hpo))
    (unit_h (3 ^ j) e3 (cp3 ap hp3)) Hh
    (fun hj1 => hypT_h_R r k ap aq u c (HT hj1) e5 e2)
  have c5 : ap ≡ (-1) ^ s * aq [ZMOD 5 ^ r] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq : ℤ)) (5 ^ r)).1 (by
      rw [rel _ e5, g5]; push_cast; ring)
    simpa using this
  have c3 : ap ≡ (-1) ^ s * aq [ZMOD 3 ^ j] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq : ℤ)) (3 ^ j)).1 (by
      rw [rel _ e3, g3]; push_cast; ring)
    simpa using this
  have c2 : ap ≡ (-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e [ZMOD 2 ^ (k + 3)] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e : ℤ))
      (2 ^ (k + 3))).1 (by
      rw [rel _ e2, g2]; push_cast; ring)
    simpa using this
  obtain ⟨he1, hshape⟩ := shape_arith_R k j r s e hs he ap aq hpo hqo hp hq hsum hne c5 c3 c2
  subst he1
  refine ⟨s, 1, hs, rfl, gc, hshape⟩

/-- **Full analytic Lemma A3 (TOP), general r >= 1, j >= 1, i = k+3 >= 3.**  The sum equation over all odd top
characters (eta3 != 1 always; eta3 = 1 additionally when j = 1) with eP != 0 forces shape A or shape B. -/
theorem top_chain_R (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hP0 : 0 < aP) (hQ0 : 0 < aQ)
    (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hS : 2 ∣ aS) (hsum : aP + aQ < 2 ^ (k + 3) * (3 ^ j * 5 ^ r)) (hne : aP ≠ aQ) (hePne : eP ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), (η3 ≠ 1 ∨ j = 1) →
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    ((eQ = eP ∧ (aP = aQ + 2 ^ (k + 2) * (3 ^ j * 5 ^ r) ∨ aQ = aP + 2 ^ (k + 2) * (3 ^ j * 5 ^ r))) ∨
      (eQ = -eP ∧ aP + aQ = 2 ^ (k + 2) * (3 ^ j * 5 ^ r))) := by
  have cop : ∀ a : ℕ, Odd a → ¬ 3 ∣ a → Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a := by
    intro a ha h3
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ?_) (Nat.Coprime.pow_left _ ?_)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 ha)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hHyp := top_equation_R r k j hr aP aQ aS eP eQ eS hP5 hQ5 (cop aP hPo hP3) (cop aQ hQo hQ3) hS hePne
    (fun ψ hψ η2 hη2 η3 h3 hodd => H ψ hψ η2 hη2 η3 (Or.inl h3) hodd)
  have hHypT : j = 1 → HypTPR r k (aP : ℤ) (aQ : ℤ) (-(eQ / eP)) := fun hj1 =>
    triv_equation_R r k j hr hj aP aQ aS eP eQ eS hP5 hQ5 (cop aP hPo hP3) (cop aQ hQo hQ3)
      hS hePne (fun ψ hψ η2 hη2 hodd => H ψ hψ η2 hη2 1 (Or.inr hj1) hodd)
  have c3 : ∀ a : ℕ, ¬ 3 ∣ a → IsCoprime (a : ℤ) 3 := fun a h =>
    (Nat.isCoprime_iff_coprime).2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm
  have c5 : ∀ a : ℕ, ¬ 5 ∣ a → IsCoprime (a : ℤ) 5 := fun a h =>
    (Nat.isCoprime_iff_coprime).2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h).symm
  obtain ⟨s, e, hs, he, hc, hshape⟩ := top_shape_R r k j hr hj (aP : ℤ) (aQ : ℤ) _
    (by exact_mod_cast hPo) (by exact_mod_cast hQo) (by exact_mod_cast hP0) (by exact_mod_cast hQ0)
    (c3 aP hP3) (c3 aQ hQ3) (c5 aP hP5) (c5 aQ hQ5) (by exact_mod_cast hsum)
    (by exact_mod_cast hne) hHyp hHypT
  subst he
  have heQ : eQ = (-1) ^ s * eP := by
    have h1 : -(eQ / eP) = (-1) ^ (s + 1) := hc
    rw [pow_succ] at h1
    field_simp at h1
    linear_combination -h1
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · left
    rcases hshape with ⟨-, h⟩ | ⟨h, -⟩
    · refine ⟨by simpa using heQ, ?_⟩
      · rcases h with h | h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
    · omega
  · right
    rcases hshape with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact ⟨by simpa using heQ, by exact_mod_cast h⟩

/-! ## E. converse and witnesses -/

theorem hypT_raw_R (r k s e : ℕ) (ap aq : ℤ)
    (e5 : (ap : ZMod (5 ^ r)) = (-1) ^ s * aq)
    (e2 : (ap : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e * aq)
    (ψ : DirichletCharacter ℂ (5 ^ r)) (η2 : DirichletCharacter ℂ (2 ^ (k + 3)))
    (hη2 : η2.IsPrimitive) (hodd : ψ (-1) * η2 (-1) = -1) :
    ψ (ap : ZMod (5 ^ r)) * η2 (ap : ZMod (2 ^ (k + 3))) =
      (-1) ^ (s + e) * (ψ (aq : ZMod (5 ^ r)) * η2 (aq : ZMod (2 ^ (k + 3)))) := by
  rw [e5, e2]
  simp only [map_mul, map_pow]
  rw [eta2_val k η2 hη2]
  have key : ψ (-1) ^ s * ψ (aq : ZMod (5 ^ r)) *
      ((η2 (-1) ^ s * (-1) ^ e) * η2 (aq : ZMod (2 ^ (k + 3)))) =
      (ψ (-1) * η2 (-1)) ^ s * (-1) ^ e *
      (ψ (aq : ZMod (5 ^ r)) * η2 (aq : ZMod (2 ^ (k + 3)))) := by ring
  rw [key, hodd, pow_add (-1 : ℂ) s e]

theorem hypP_converse_R (r k j s e : ℕ) (ap aq : ℤ)
    (e5 : (ap : ZMod (5 ^ r)) = (-1) ^ s * aq) (e3 : (ap : ZMod (3 ^ j)) = (-1) ^ s * aq)
    (e2 : (ap : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e * aq) :
    HypPR r k j ap aq ((-1) ^ (s + e)) := by
  intro ψ _ η2 hη2 η3 _ hodd
  rw [e5, e2, e3]
  simp only [map_mul, map_pow]
  rw [eta2_val k η2 hη2]
  have key : ψ (-1) ^ s * ψ (aq : ZMod (5 ^ r)) *
      ((η2 (-1) ^ s * (-1) ^ e) * η2 (aq : ZMod (2 ^ (k + 3)))) *
      (η3 (-1) ^ s * η3 (aq : ZMod (3 ^ j))) =
      (ψ (-1) * η2 (-1) * η3 (-1)) ^ s * (-1) ^ e *
      (ψ (aq : ZMod (5 ^ r)) * η2 (aq : ZMod (2 ^ (k + 3))) * η3 (aq : ZMod (3 ^ j))) := by ring
  rw [key, hodd, pow_add (-1 : ℂ) s e]

/-- The full equation (all admissible odd top characters) from the converse data. -/
theorem top_equation_R_of (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (s e : ℕ) (aP aQ aS : ℕ) (eS : ℂ)
    (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hPc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aP) (hQc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aQ)
    (hS : 2 ∣ aS)
    (e5 : ((aP : ℤ) : ZMod (5 ^ r)) = (-1) ^ s * (aQ : ℤ))
    (e3 : ((aP : ℤ) : ZMod (3 ^ j)) = (-1) ^ s * (aQ : ℤ))
    (e2 : ((aP : ℤ) : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e * (aQ : ℤ)) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), (η3 ≠ 1 ∨ j = 1) →
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (1 : ℂ) * bracket (chi ψ (chi η2 η3)) aP + (-((-1) ^ (s + e))) * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0 := by
  intro ψ hψ η2 hη2 η3 hη3 hodd
  by_cases h3 : η3 = 1
  · subst h3
    have hodd' : ψ (-1) * η2 (-1) = -1 := by
      rw [MulChar.one_apply (isUnit_one.neg)] at hodd; simpa using hodd
    rw [bracket_top_triv_R r k j hj ψ hψ η2 hη2 aP hP5 hPc, bracket_top_triv_R r k j hj ψ hψ η2 hη2 aQ hQ5 hQc,
      bracket_even_R r hr k j ψ hψ η2 hη2 1 aS hS, mul_zero, add_zero]
    have hT := hypT_raw_R r k s e (aP : ℤ) (aQ : ℤ) e5 e2 ψ η2 hη2 hodd'
    simp only [Int.cast_natCast] at hT
    linear_combination (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹) * hT
  · have h := hypP_converse_R r k j s e (aP : ℤ) (aQ : ℤ) e5 e3 e2 ψ hψ η2 hη2 η3 h3 hodd
    rw [bracket_top_R r k j ψ hψ η2 hη2 η3 h3 aP hP5 hPc, bracket_top_R r k j ψ hψ η2 hη2 η3 h3 aQ hQ5 hQc,
      bracket_even_R r hr k j ψ hψ η2 hη2 η3 aS hS, mul_zero, add_zero]
    simp only [Int.cast_natCast] at h
    linear_combination h

/-- r = 2, k = 0, j = 2, n = 1800, shape A: entries (907, 7, 886). -/
theorem top_chain_R_907_7 :
    (((1 : ℂ) = 1 ∧ ((907 : ℕ) = 7 + 2 ^ (0 + 2) * (3 ^ 2 * 5 ^ 2) ∨
        (7 : ℕ) = 907 + 2 ^ (0 + 2) * (3 ^ 2 * 5 ^ 2))) ∨
      ((1 : ℂ) = -1 ∧ (907 : ℕ) + 7 = 2 ^ (0 + 2) * (3 ^ 2 * 5 ^ 2))) :=
  top_chain_R 2 0 2 (by norm_num) (by norm_num) 907 7 886 1 1 0 (by decide) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) one_ne_zero
    (by
      have := top_equation_R_of 2 0 2 (by norm_num) (by norm_num) 0 1 907 7 886 0 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      simpa using this)

/-- r = 2, k = 0, j = 2, shape B: entries (893, 7, 900). -/
theorem top_chain_R_893_7 :
    (((-1 : ℂ) = 1 ∧ ((893 : ℕ) = 7 + 2 ^ (0 + 2) * (3 ^ 2 * 5 ^ 2) ∨
        (7 : ℕ) = 893 + 2 ^ (0 + 2) * (3 ^ 2 * 5 ^ 2))) ∨
      ((-1 : ℂ) = -1 ∧ (893 : ℕ) + 7 = 2 ^ (0 + 2) * (3 ^ 2 * 5 ^ 2))) :=
  top_chain_R 2 0 2 (by norm_num) (by norm_num) 893 7 900 1 (-1) 0 (by decide) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) one_ne_zero
    (by
      have := top_equation_R_of 2 0 2 (by norm_num) (by norm_num) 1 1 893 7 900 0 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      simpa using this)

/-- r = 2, k = 0, j = 1, n = 600, shape A: entries (307, 7, 286) -- this uses the eta3 = 1 equation too. -/
theorem top_chain_R_307_7 :
    (((1 : ℂ) = 1 ∧ ((307 : ℕ) = 7 + 2 ^ (0 + 2) * (3 ^ 1 * 5 ^ 2) ∨
        (7 : ℕ) = 307 + 2 ^ (0 + 2) * (3 ^ 1 * 5 ^ 2))) ∨
      ((1 : ℂ) = -1 ∧ (307 : ℕ) + 7 = 2 ^ (0 + 2) * (3 ^ 1 * 5 ^ 2))) :=
  top_chain_R 2 0 1 (by norm_num) (by norm_num) 307 7 286 1 1 0 (by decide) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) one_ne_zero
    (by
      have := top_equation_R_of 2 0 1 (by norm_num) (by norm_num) 0 1 307 7 286 0 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      simpa using this)

/-- r = 2, k = 0, j = 1, shape B: entries (293, 7, 300). -/
theorem top_chain_R_293_7 :
    (((-1 : ℂ) = 1 ∧ ((293 : ℕ) = 7 + 2 ^ (0 + 2) * (3 ^ 1 * 5 ^ 2) ∨
        (7 : ℕ) = 293 + 2 ^ (0 + 2) * (3 ^ 1 * 5 ^ 2))) ∨
      ((-1 : ℂ) = -1 ∧ (293 : ℕ) + 7 = 2 ^ (0 + 2) * (3 ^ 1 * 5 ^ 2))) :=
  top_chain_R 2 0 1 (by norm_num) (by norm_num) 293 7 300 1 (-1) 0 (by decide) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) one_ne_zero
    (by
      have := top_equation_R_of 2 0 1 (by norm_num) (by norm_num) 1 1 293 7 300 0 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      simpa using this)

end Erdos634.GA2NR2

#print axioms Erdos634.GA2NR2.bracket_top_R
#print axioms Erdos634.GA2NR2.bracket_top_triv_R
#print axioms Erdos634.GA2NR2.shape_arith_R
#print axioms Erdos634.GA2NR2.top_shape_R
#print axioms Erdos634.GA2NR2.top_chain_R
#print axioms Erdos634.GA2NR2.top_chain_R_907_7
#print axioms Erdos634.GA2NR2.top_chain_R_893_7
#print axioms Erdos634.GA2NR2.top_chain_R_307_7
#print axioms Erdos634.GA2NR2.top_chain_R_293_7
