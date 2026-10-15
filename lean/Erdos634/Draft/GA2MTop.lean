/-
GA2M, atom (P1 at p = 5, composite m = 2^(k+3) 3^j, top characters): the existing prime-generic component
formula `LemmaSPhi.bracket_unit` (hypothesis only `¬ p ∣ m`; not restricted to p >= 7) is specialised to the
top family: chi = psi * (eta2 * eta3), psi primitive mod 5, eta2 primitive mod 2^(k+3), eta3 != 1 mod 3^j.  Results:
  `bracket_top`  : a coprime to 30 (and to m)  =>  [a/n]_chi = psi(a) eta2(a) eta3(a)   (w = 1, no Euler factor)
  `bracket_even` : a even                      =>  [a/n]_chi = 0                          (f ∤ d)
  `top_equation` : sum equation  eP [aP] + eQ [aQ] + eS [aS] = 0 for all odd top chi  =>  HypP k j aP aQ (-eQ/eP)
  `top_chain`    : + shape arithmetic  =>  shape A (eQ = eP) or shape B (eQ = -eP)  [full analytic Lemma A3]
  `top_equation_of_hypP` : converse (non-vacuity), and a concrete instance (aP, aQ, aS) = (187, 7, 166), n = 360.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.LemmaSPhi
import Erdos634.Draft.GA2MChain

open scoped BigOperators
open Finset

namespace Erdos634.GA2MTop

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2LGroup Erdos634.GA2MChain Erdos634.GA2LCore

theorem not5_dvd (k j : ℕ) : ¬ 5 ∣ 2 ^ (k + 3) * 3 ^ j := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h; omega
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h; omega

theorem not2_dvd (j : ℕ) : ¬ 2 ∣ 3 ^ j := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h; omega

/-- conductor of the 2-3 part: 2^(k+3) * conductor(eta3). -/
theorem cond_eta (k j : ℕ) (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) :
    (chi η2 η3).conductor = 2 ^ (k + 3) * η3.conductor :=
  conductor_chi (p := 2) (not2_dvd j) hη2 η3

theorem bracket_top (k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3 ≠ 1) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (hcop : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a) :
    bracket (chi ψ (chi η2 η3)) a =
      ψ (a : ZMod (5 ^ 1)) * η2 (a : ZMod (2 ^ (k + 3))) * η3 (a : ZMod (3 ^ j)) := by
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
  -- eta*(a) = eta(a) = eta2(a) eta3(a)
  have hstar : η.primitiveCharacter (a : ZMod η.conductor) = η (a : ZMod (2 ^ (k + 3) * 3 ^ j)) := by
    conv_rhs => rw [← changeLevel_primitiveCharacter η]
    rw [changeLevel_nat _ _ a hcop.symm]
  have hmul : η (a : ZMod (2 ^ (k + 3) * 3 ^ j)) =
      η2 (a : ZMod (2 ^ (k + 3))) * η3 (a : ZMod (3 ^ j)) := by
    have e : η = changeLevel (Nat.dvd_mul_right (2 ^ (k + 3)) (3 ^ j)) η2 *
        changeLevel (Nat.dvd_mul_left (3 ^ j) (2 ^ (k + 3))) η3 := rfl
    rw [e, MulChar.mul_apply, changeLevel_nat _ _ a hcop.symm, changeLevel_nat _ _ a hcop.symm]
  rw [hstar, hmul]; ring

theorem bracket_even (k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ) (ha : 2 ∣ a) :
    bracket (chi ψ (chi η2 η3)) a = 0 := by
  set η : DirichletCharacter ℂ (2 ^ (k + 3) * 3 ^ j) := chi η2 η3 with hη
  by_cases h5 : 5 ∣ a
  · exact bracket_p_dvd le_rfl (not5_dvd k j) hψ η a h5
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

theorem top_equation (k j : ℕ) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hPc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aP) (hQc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aQ)
    (hS : 2 ∣ aS) (hePne : eP ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    HypP k j (aP : ℤ) (aQ : ℤ) (-(eQ / eP)) := by
  intro ψ hψ η2 hη2 η3 hη3 hodd
  have h := H ψ hψ η2 hη2 η3 hη3 hodd
  rw [bracket_top k j ψ hψ η2 hη2 η3 hη3 aP hP5 hPc, bracket_top k j ψ hψ η2 hη2 η3 hη3 aQ hQ5 hQc,
    bracket_even k j ψ hψ η2 hη2 η3 aS hS, mul_zero, add_zero] at h
  simp only [Int.cast_natCast]
  field_simp
  linear_combination h

/-- **Full analytic Lemma A3 (TOP), r = 1, j >= 2, i = k+3 >= 3**: two odd entries aP != aQ (coprime to 30),
an even third entry, sizes as in a tile of n = 2^i 3^j 5, and the top equation for all odd top characters,
with eP != 0, give shape A (eQ = eP, |aP - aQ| = n/2) or shape B (eQ = -eP, aP + aQ = n/2). -/
theorem top_chain (k j : ℕ) (hj : 2 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hP0 : 0 < aP) (hQ0 : 0 < aQ)
    (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hS : 2 ∣ aS) (hsum : aP + aQ < 2 ^ (k + 3) * (3 ^ j * 5)) (hne : aP ≠ aQ) (hePne : eP ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    ((eQ = eP ∧ (aP = aQ + 2 ^ (k + 2) * (3 ^ j * 5) ∨ aQ = aP + 2 ^ (k + 2) * (3 ^ j * 5))) ∨
      (eQ = -eP ∧ aP + aQ = 2 ^ (k + 2) * (3 ^ j * 5))) := by
  have cop : ∀ a : ℕ, Odd a → ¬ 3 ∣ a → Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a := by
    intro a ha h3
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ?_) (Nat.Coprime.pow_left _ ?_)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 ha)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hHyp := top_equation k j aP aQ aS eP eQ eS hP5 hQ5 (cop aP hPo hP3) (cop aQ hQo hQ3) hS hePne H
  have c3 : ∀ a : ℕ, ¬ 3 ∣ a → IsCoprime (a : ℤ) 3 := fun a h =>
    (Nat.isCoprime_iff_coprime).2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm
  have c5 : ∀ a : ℕ, ¬ 5 ∣ a → IsCoprime (a : ℤ) 5 := fun a h =>
    (Nat.isCoprime_iff_coprime).2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h).symm
  obtain ⟨s, e, hs, he, hc, hshape⟩ := top_shape k j hj (aP : ℤ) (aQ : ℤ) _
    (by exact_mod_cast hPo) (by exact_mod_cast hQo) (by exact_mod_cast hP0) (by exact_mod_cast hQ0)
    (c3 aP hP3) (c3 aQ hQ3) (c5 aP hP5) (c5 aQ hQ5) (by exact_mod_cast hsum)
    (by exact_mod_cast hne) hHyp
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

/-! ## Converse / witness: the analytic hypothesis of `top_chain` is satisfiable. -/

theorem top_equation_of_hypP (k j : ℕ) (aP aQ aS : ℕ) (c eS : ℂ)
    (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hPc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aP) (hQc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aQ)
    (hS : 2 ∣ aS) (Hy : HypP k j (aP : ℤ) (aQ : ℤ) c) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (1 : ℂ) * bracket (chi ψ (chi η2 η3)) aP + (-c) * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0 := by
  intro ψ hψ η2 hη2 η3 hη3 hodd
  have h := Hy ψ hψ η2 hη2 η3 hη3 hodd
  rw [bracket_top k j ψ hψ η2 hη2 η3 hη3 aP hP5 hPc, bracket_top k j ψ hψ η2 hη2 η3 hη3 aQ hQ5 hQc,
    bracket_even k j ψ hψ η2 hη2 η3 aS hS, mul_zero, add_zero]
  simp only [Int.cast_natCast] at h
  linear_combination h

/-- Concrete witness, n = 360 (k = 0, j = 2): entries (187, 7, 166), e = (1, 1, eS): shape A, with the
whole analytic equation (all odd top characters) holding, and `top_chain` applies. -/
theorem top_equation_187_7 (eS : ℂ) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (0 + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ 2), η3 ≠ 1 →
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (1 : ℂ) * bracket (chi ψ (chi η2 η3)) 187 + (1 : ℂ) * bracket (chi ψ (chi η2 η3)) 7 +
          eS * bracket (chi ψ (chi η2 η3)) 166 = 0 := by
  have := top_equation_of_hypP 0 2 187 7 166 (-1) eS (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by exact_mod_cast hypP_187_7)
  simpa using this

theorem top_chain_187_7 :
    (((1 : ℂ) = 1 ∧ ((187 : ℕ) = 7 + 2 ^ (0 + 2) * (3 ^ 2 * 5) ∨ (7 : ℕ) = 187 + 2 ^ (0 + 2) * (3 ^ 2 * 5))) ∨
      ((1 : ℂ) = -1 ∧ (187 : ℕ) + 7 = 2 ^ (0 + 2) * (3 ^ 2 * 5))) :=
  top_chain 0 2 le_rfl 187 7 166 1 1 0 (by decide) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_ne_zero (top_equation_187_7 0)

end Erdos634.GA2MTop

#print axioms Erdos634.GA2MTop.bracket_top
#print axioms Erdos634.GA2MTop.bracket_even
#print axioms Erdos634.GA2MTop.top_equation
#print axioms Erdos634.GA2MTop.top_chain
#print axioms Erdos634.GA2MTop.top_equation_187_7
#print axioms Erdos634.GA2MTop.top_chain_187_7
