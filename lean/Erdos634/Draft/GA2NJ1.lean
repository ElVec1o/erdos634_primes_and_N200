/-
GA2N, item (1): **j = 1 assembly of the TOP step (Lemma A3, r = 1, n = 2^(k+3) 3 5)**.

For j = 1 the 3-part of a top character is eta3 in {1, Leg} (Leg = the nontrivial character mod 3).
* eta3 = Leg  (!= 1): the existing `GA2MTop.bracket_top` (no Euler factor) -- `HypP k 1 aP aQ c`.
* eta3 = 1   : the Euler set is {3}; `bracket_top_triv`:  [a/n]_chi = psi(a) eta2(a) (1 - conj(psi eta2)(3))
  for a coprime to 30.  Nonvanishing of the factor iff psi(3) eta2(3) != 1.  `triv_equation` gives `HypTP`.
* `group_core_j1`: Hyp (Leg only) + HypT (eta3 = 1, psi(3)eta2(3) != 1) => the same conclusion as `group_core`
  (z5 = z3 = (-1)^s, z2 = (-1)^s (1+2^(k+2))^e, c = (-1)^(s+e)).  Step 2 compares Leg with 1 using an EVEN psi
  (psi(3) = -1, `even_five_three`) and an ODD eta2 (eta2(3) != -1, F4 = `GA2MF4.eta2_three_ne`).
* `top_shape_j1`, `top_chain_j1`: the j = 1 analogue of `GA2MChain.top_shape`, `GA2MTop.top_chain`.
* Witnesses: n = 120, shape A (67,7,46) and shape B (53,7,60); the whole analytic equation (all odd top
  characters incl. eta3 = 1) holds and `top_chain_j1` applies.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2MTop
import Erdos634.Draft.GA2MF4

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NJ1

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2LGroup Erdos634.GA2MChain Erdos634.GA2LCore Erdos634.GA2MTop Erdos634.GA2LPar
open Erdos634.GA2LShape Erdos634.GA2MF4

/-! ## A. the eta3 = 1 component formula -/

theorem bracket_top_triv (k j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive) (a : ℕ)
    (ha5 : ¬ 5 ∣ a) (hcop : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a) :
    bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) a =
      ψ (a : ZMod (5 ^ 1)) * η2 (a : ZMod (2 ^ (k + 3))) *
        (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹) := by
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

theorem isUnit_three_5 : IsUnit (3 : ZMod (5 ^ 1)) := by
  have := (ZMod.isUnit_iff_coprime 3 (5 ^ 1)).2 (by norm_num)
  simpa using this

theorem isUnit_three_2 (k : ℕ) : IsUnit (3 : ZMod (2 ^ (k + 3))) := by
  have := (ZMod.isUnit_iff_coprime 3 (2 ^ (k + 3))).2
    (Nat.Coprime.pow_right _ (by norm_num))
  simpa using this

/-- `bracket_even` restated for any eta3 (the GA2MTop statement already is; alias for readability). -/
theorem bracket_even_any (k j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive)
    (a : ℕ) (ha : 2 ∣ a) :
    bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) a = 0 :=
  bracket_even k j ψ hψ η2 hη2 1 a ha

/-- Hypothesis (eta3 = 1): psi(ap) eta2(ap) = c psi(aq) eta2(aq) for odd psi eta2 with psi(3)eta2(3) != 1. -/
def HypTP (k : ℕ) (ap aq : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
    ψ (-1) * η2 (-1) = -1 →
    ψ (3 : ZMod (5 ^ 1)) * η2 (3 : ZMod (2 ^ (k + 3))) ≠ 1 →
    ψ (ap : ZMod (5 ^ 1)) * η2 (ap : ZMod (2 ^ (k + 3))) =
      c * (ψ (aq : ZMod (5 ^ 1)) * η2 (aq : ZMod (2 ^ (k + 3))))

theorem triv_equation (k j : ℕ) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hPc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aP) (hQc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) aQ)
    (hS : 2 ∣ aS) (hePne : eP ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
        ψ (-1) * η2 (-1) * (1 : DirichletCharacter ℂ (3 ^ j)) (-1) = -1 →
        eP * bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) aP +
          eQ * bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) aQ +
          eS * bracket (chi ψ (chi η2 (1 : DirichletCharacter ℂ (3 ^ j)))) aS = 0) :
    HypTP k (aP : ℤ) (aQ : ℤ) (-(eQ / eP)) := by
  intro ψ hψ η2 hη2 hodd hne
  have h := H ψ hψ η2 hη2 (by rw [MulChar.one_apply (isUnit_one.neg)]; simpa using hodd)
  rw [bracket_top_triv k j hj ψ hψ η2 hη2 aP hP5 hPc, bracket_top_triv k j hj ψ hψ η2 hη2 aQ hQ5 hQc,
    bracket_even_any k j ψ hψ η2 hη2 aS hS, mul_zero, add_zero] at h
  set F : ℂ := 1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹ with hF
  have hFne : F ≠ 0 := by
    intro h0
    apply hne
    have h1 : (ψ (3 : ZMod (5 ^ 1)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹ = 1 := by
      linear_combination (-1 : ℂ) * h0
    rw [← mul_inv, inv_eq_one] at h1
    exact h1
  have h2 : (eP * (ψ (aP : ZMod (5 ^ 1)) * η2 (aP : ZMod (2 ^ (k + 3)))) +
      eQ * (ψ (aQ : ZMod (5 ^ 1)) * η2 (aQ : ZMod (2 ^ (k + 3))))) * F = 0 := by
    linear_combination h
  have h3 := (mul_eq_zero.1 h2).resolve_right hFne
  simp only [Int.cast_natCast]
  field_simp
  linear_combination h3

/-! ## B. group core for j = 1 -/

theorem exists_ne_one3_j1 : ∃ η : DirichletCharacter ℂ (3 ^ 1), η ≠ 1 := by
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hN : Fintype.card (DirichletCharacter ℂ (3 ^ 1)) = (3 ^ 1).totient := by
    have := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (3 ^ 1)
    rwa [Nat.card_eq_fintype_card] at this
  have ht : (3 ^ 1).totient = 2 := by rw [pow_one, Nat.totient_prime (by norm_num)]
  haveI : Nontrivial (DirichletCharacter ℂ (3 ^ 1)) :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  exact exists_ne _

theorem zmod3_cases : ∀ a : ZMod (3 ^ 1), a = 0 ∨ a = 1 ∨ a = -1 := by decide

theorem three_odd (η : DirichletCharacter ℂ (3 ^ 1)) (hη : η ≠ 1) : η (-1) = -1 := by
  haveI : Fact (1 < 3 ^ 1) := ⟨by norm_num⟩
  rcases sign_val η with h | h
  · exfalso; apply hη
    ext a
    rcases zmod3_cases (a : ZMod (3 ^ 1)) with h0 | h0 | h0
    · exfalso; have := a.isUnit; rw [h0] at this; exact not_isUnit_zero this
    · rw [h0, MulChar.map_one, MulChar.map_one]
    · rw [h0, h, MulChar.one_apply (isUnit_one.neg)]
  · exact h

theorem even_five_three (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive) (he : ψ (-1) = 1) :
    ψ (3 : ZMod (5 ^ 1)) = -1 := by
  have hmem : ψ ∈ PrimPar 5 1 1 := mem_PrimPar.2 ⟨hψ, he⟩
  have hcard := card_five 1 (Or.inl rfl)
  rw [if_pos rfl] at hcard
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
  have hk := key5 1 (Or.inl rfl) 3 (by
    have := (ZMod.isUnit_iff_coprime 3 (5 ^ 1)).2 (by norm_num)
    simpa using this)
  rw [ha, Finset.sum_singleton] at hk
  rw [ha, Finset.mem_singleton] at hmem
  subst hmem
  have e1 : ¬ ((3 : ℤ) ≡ 1 [ZMOD 5]) := by decide
  have e2 : ¬ ((-3 : ℤ) ≡ 1 [ZMOD 5]) := by decide
  rw [if_neg e1, if_neg e2] at hk
  push_cast at hk
  linear_combination hk / 2

def HypT (k : ℕ) (z5 z2 : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
    ψ (-1) * η2 (-1) = -1 →
    ψ (3 : ZMod (5 ^ 1)) * η2 (3 : ZMod (2 ^ (k + 3))) ≠ 1 →
    ψ (z5 : ZMod (5 ^ 1)) * η2 (z2 : ZMod (2 ^ (k + 3))) = c

theorem group_core_j1 (k : ℕ) (z5 z2 z3 : ℤ) (c : ℂ)
    (u5 : IsUnit (z5 : ZMod (5 ^ 1))) (u2 : IsUnit (z2 : ZMod (2 ^ (k + 3))))
    (u3 : IsUnit (z3 : ZMod (3 ^ 1))) (H : Hyp k 1 z5 z2 z3 c) (HT : HypT k z5 z2 c) :
    ∃ s e : ℕ, s < 2 ∧ e < 2 ∧ (z5 : ZMod (5 ^ 1)) = (-1) ^ s ∧ (z3 : ZMod (3 ^ 1)) = (-1) ^ s ∧
      (z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e ∧ c = (-1) ^ (s + e) := by
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : Fact (1 < 3 ^ 1) := ⟨by norm_num⟩
  have claim : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ 1), η3 ≠ 1 →
      ∀ η2 ∈ PrimPar 2 (k + 3) (-(ψ (-1) * η3 (-1))),
        ψ (z5 : ZMod (5 ^ 1)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ 1)) = c := by
    intro ψ hψ η3 hη3 η2 hη2
    obtain ⟨hp2, hs2⟩ := mem_PrimPar.1 hη2
    refine H ψ hψ η2 hp2 η3 hη3 ?_
    rw [hs2]
    rcases sign_val ψ with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num
  have sgn : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ∀ η3 : DirichletCharacter ℂ (3 ^ 1),
      (-(ψ (-1) * η3 (-1))) = 1 ∨ (-(ψ (-1) * η3 (-1))) = -1 := by
    intro ψ η3
    rcases sign_val ψ with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num
  have ne5e : (PrimPar 5 1 1).Nonempty := by
    rw [← card_pos, card_five 1 (Or.inl rfl)]; norm_num
  obtain ⟨ψe, hψe⟩ := ne5e
  obtain ⟨hψe_p, hψe_s⟩ := mem_PrimPar.1 hψe
  obtain ⟨η30, hη30⟩ := exists_ne_one3_j1
  have A0 : ψe (z5 : ZMod (5 ^ 1)) ≠ 0 := nz ψe _ u5
  have step1 : ∃ s e : ℕ, s < 2 ∧ e < 2 ∧
      ((z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e) ∧
      ∀ ε' : ℂ, (ε' = 1 ∨ ε' = -1) → ∀ η ∈ PrimPar 2 (k + 3) ε',
        η (z2 : ZMod (2 ^ (k + 3))) = ε' ^ s * (-1) ^ e := by
    refine two_part_core k (-(ψe (-1) * η30 (-1))) (sgn ψe η30) z2 u2
      ⟨c / (ψe (z5 : ZMod (5 ^ 1)) * η30 (z3 : ZMod (3 ^ 1))), fun η hη => ?_⟩
    have h := claim ψe hψe_p η30 hη30 η hη
    have B0 : η30 (z3 : ZMod (3 ^ 1)) ≠ 0 := nz η30 _ u3
    rw [eq_div_iff (mul_ne_zero A0 B0)]
    linear_combination h
  obtain ⟨s, e, hs, he, h2eq, hval⟩ := step1
  have usg : IsUnit ((-1 : ZMod (3 ^ 1)) ^ s) := (isUnit_one.neg).pow s
  -- Step 2 (j = 1): compare eta3 = Leg with eta3 = 1, using an even psi and odd/even eta2.
  have hLeg : η30 (-1) = -1 := three_odd η30 hη30
  have hψe3 : ψe (3 : ZMod (5 ^ 1)) = -1 := even_five_three ψe hψe_p hψe_s
  have step2 : (z3 : ZMod (3 ^ 1)) * (-1) ^ s = 1 := by
    have sg1 : (-(ψe (-1) * η30 (-1))) = 1 := by rw [hψe_s, hLeg]; norm_num
    obtain ⟨η2e, hη2e⟩ := nonempty_par2 k (-(ψe (-1) * η30 (-1))) (sgn ψe η30)
    have hA := claim ψe hψe_p η30 hη30 η2e hη2e
    rw [hval _ (sgn ψe η30) η2e hη2e, sg1] at hA
    simp only [one_pow] at hA
    obtain ⟨η2o, hη2o⟩ := nonempty_par2 k (-1) (Or.inr rfl)
    obtain ⟨hη2o_p, hη2o_s⟩ := mem_PrimPar.1 hη2o
    have hB := HT ψe hψe_p η2o hη2o_p (by rw [hψe_s, hη2o_s]; norm_num)
      (by
        rw [hψe3]; intro h
        exact eta2_three_ne k η2o hη2o_p hη2o_s (by linear_combination -h))
    rw [hval (-1) (Or.inr rfl) η2o hη2o] at hB
    have hLz : η30 (z3 : ZMod (3 ^ 1)) = (-1) ^ s := by
      have hne : ψe (z5 : ZMod (5 ^ 1)) * (-1) ^ e ≠ 0 :=
        mul_ne_zero A0 (pow_ne_zero _ (by norm_num))
      apply mul_left_cancel₀ hne
      linear_combination hA - hB
    have hug : IsUnit ((z3 : ZMod (3 ^ 1)) * (-1) ^ s) := u3.mul usg
    have hg : η30 ((z3 : ZMod (3 ^ 1)) * (-1) ^ s) = 1 := by
      rw [map_mul, map_pow, hLz, hLeg, ← mul_pow]; norm_num
    rcases zmod3_cases ((z3 : ZMod (3 ^ 1)) * (-1) ^ s) with h | h | h
    · exfalso; rw [h] at hug; exact not_isUnit_zero hug
    · exact h
    · exfalso; rw [h, hLeg] at hg; norm_num at hg
  have z3eq : (z3 : ZMod (3 ^ 1)) = (-1) ^ s := by
    have hs2 : ((-1 : ZMod (3 ^ 1)) ^ s) * ((-1) ^ s) = 1 := by
      rw [← mul_pow]; simp
    calc (z3 : ZMod (3 ^ 1)) = (z3 * (-1) ^ s) * (-1) ^ s := by
          rw [mul_assoc, hs2, mul_one]
      _ = (-1) ^ s := by rw [step2, one_mul]
  -- Step 3: the 5-part (unchanged from `group_core`)
  have step3 : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ψ (z5 : ZMod (5 ^ 1)) * ((-(ψ (-1) * η30 (-1))) ^ s * (-1) ^ e * η30 (-1) ^ s) = c := by
    intro ψ hψ
    obtain ⟨η2, hη2⟩ := nonempty_par2 k (-(ψ (-1) * η30 (-1))) (sgn ψ η30)
    have h := claim ψ hψ η30 hη30 η2 hη2
    rw [hval _ (sgn ψ η30) η2 hη2, z3eq, map_pow] at h
    linear_combination h
  have sq1 : ∀ x : ℂ, (x = 1 ∨ x = -1) → ∀ n : ℕ, x ^ n * x ^ n = 1 := by
    intro x hx n; rw [← mul_pow]; rcases hx with rfl | rfl <;> simp
  have hX := sq1 (η30 (-1)) (sign_val η30) s
  have hb := sq1 (-1 : ℂ) (Or.inr rfl) e
  have odd5 : ∀ ψ ∈ PrimPar 5 1 (-1), ψ (z5 : ZMod (5 ^ 1)) = (-1) ^ e * c := by
    intro ψ hψ
    obtain ⟨hp, hs⟩ := mem_PrimPar.1 hψ
    have h := step3 ψ hp
    rw [hs, neg_one_mul, neg_neg] at h
    linear_combination (-1 : ℂ) ^ e * h - ψ (z5 : ZMod (5 ^ 1)) * (η30 (-1) ^ s * η30 (-1) ^ s) * hb
      - ψ (z5 : ZMod (5 ^ 1)) * hX
  have five := five_odd z5 u5 ((-1) ^ e * c) odd5
  have zm5 : ∀ {w : ℤ}, z5 ≡ w [ZMOD 5] → (z5 : ZMod (5 ^ 1)) = (w : ZMod (5 ^ 1)) := by
    intro w h
    rw [ZMod.intCast_eq_intCast_iff]; push_cast; simpa using h
  have hcc : c = (-1) ^ (s + e) := by
    have hz5 : (z5 : ZMod (5 ^ 1)) = 1 ∨ (z5 : ZMod (5 ^ 1)) = -1 := by
      rcases five with ⟨h, _⟩ | ⟨h, _⟩
      · left; simpa using zm5 h
      · right; simpa using zm5 h
    have hψ1 : ψe (z5 : ZMod (5 ^ 1)) = 1 := by
      rcases hz5 with h | h <;> rw [h]
      · exact map_one ψe
      · exact hψe_s
    have h := step3 ψe hψe_p
    rw [hψ1, hψe_s, one_mul, one_mul, neg_pow] at h
    rw [pow_add]
    linear_combination -h + (-1 : ℂ) ^ s * (-1) ^ e * hX
  refine ⟨s, e, hs, he, ?_, z3eq, h2eq, hcc⟩
  have hb1 : (-1 : ℂ) ^ e * (-1) ^ (s + e) = (-1) ^ s := by
    rw [pow_add]; linear_combination (-1 : ℂ) ^ s * hb
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · rcases five with ⟨h, h'⟩ | ⟨h, h'⟩
    · simpa using zm5 h
    · exfalso
      rw [hcc, hb1] at h'
      norm_num at h'
  · rcases five with ⟨h, h'⟩ | ⟨h, h'⟩
    · exfalso
      rw [hcc, hb1] at h'
      norm_num at h'
    · simpa using zm5 h

/-! ## C. chaining (j = 1) -/

theorem hypT_h (k : ℕ) (ap aq u : ℤ) (c : ℂ) (H : HypTP k ap aq c)
    (e5 : ((aq * u : ℤ) : ZMod (5 ^ 1)) = 1) (e2 : ((aq * u : ℤ) : ZMod (2 ^ (k + 3))) = 1) :
    HypT k (ap * u) (ap * u) c := by
  intro ψ hψ η2 hη2 hodd hne
  have h := H ψ hψ η2 hη2 hodd hne
  have k5 : ψ (aq * u : ℤ) = ψ (aq : ZMod (5 ^ 1)) * ψ (u : ZMod (5 ^ 1)) := by
    rw [← map_mul]; push_cast; rfl
  have k2 : η2 (aq * u : ℤ) = η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  rw [e5, map_one] at k5
  rw [e2, map_one] at k2
  have m5 : ψ ((ap * u : ℤ) : ZMod (5 ^ 1)) = ψ (ap : ZMod (5 ^ 1)) * ψ (u : ZMod (5 ^ 1)) := by
    rw [← map_mul]; push_cast; rfl
  have m2 : η2 ((ap * u : ℤ) : ZMod (2 ^ (k + 3))) =
      η2 (ap : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  rw [m5, m2]
  have := congrArg (fun x => x * (ψ (u : ZMod (5 ^ 1)) * η2 (u : ZMod (2 ^ (k + 3))))) h
  simp only at this
  calc _ = (ψ (ap : ZMod (5 ^ 1)) * η2 (ap : ZMod (2 ^ (k + 3)))) *
        (ψ (u : ZMod (5 ^ 1)) * η2 (u : ZMod (2 ^ (k + 3)))) := by ring
    _ = _ := this
    _ = c * ((ψ (aq : ZMod (5 ^ 1)) * ψ (u : ZMod (5 ^ 1))) *
        (η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))))) := by ring
    _ = c := by rw [← k5, ← k2]; simp

theorem top_shape_j1 (k : ℕ) (ap aq : ℤ) (c : ℂ)
    (hpo : Odd ap) (hqo : Odd aq) (hp : 0 < ap) (hq : 0 < aq)
    (hp3 : IsCoprime ap 3) (hq3 : IsCoprime aq 3) (hp5 : IsCoprime ap 5) (hq5 : IsCoprime aq 5)
    (hsum : ap + aq < 2 ^ (k + 3) * (3 ^ 1 * 5)) (hne : ap ≠ aq)
    (H : HypP k 1 ap aq c) (HT : HypTP k ap aq c) :
    ∃ s e : ℕ, s < 2 ∧ e = 1 ∧ c = (-1) ^ (s + e) ∧
      ((s = 0 ∧ (ap = aq + 2 ^ (k + 2) * (3 ^ 1 * 5) ∨ aq = ap + 2 ^ (k + 2) * (3 ^ 1 * 5))) ∨
        (s = 1 ∧ ap + aq = 2 ^ (k + 2) * (3 ^ 1 * 5))) := by
  have cp2 : ∀ a : ℤ, Odd a → IsCoprime a ((2 ^ (k + 3) : ℕ) : ℤ) := fun a ha => by
    have := odd_cop a ha (k + 3); push_cast; exact this
  have cp3 : ∀ a : ℤ, IsCoprime a 3 → IsCoprime a ((3 ^ 1 : ℕ) : ℤ) := fun a ha => by
    simpa using ha
  have cp5 : ∀ a : ℤ, IsCoprime a 5 → IsCoprime a ((5 ^ 1 : ℕ) : ℤ) := fun a ha => by
    simpa using ha
  have cpn : IsCoprime aq (((2 ^ (k + 3) * (3 ^ 1 * 5) : ℕ)) : ℤ) := by
    have h1 := (cp2 aq hqo)
    have h2 : IsCoprime aq (((3 ^ 1 * 5 : ℕ)) : ℤ) := by
      have := (hq3.pow_right (n := 1)).mul_right hq5
      push_cast; exact this
    push_cast at h1 h2 ⊢
    exact h1.mul_right h2
  obtain ⟨u, v, huv⟩ := cpn
  have dvd_n : ∀ m : ℕ, (m : ℤ) ∣ ((2 ^ (k + 3) * (3 ^ 1 * 5) : ℕ) : ℤ) →
      ((aq * u : ℤ) : ZMod m) = 1 := by
    intro m hm
    have h1 : (aq * u : ℤ) = 1 - v * ((2 ^ (k + 3) * (3 ^ 1 * 5) : ℕ) : ℤ) := by linarith
    have : (((2 ^ (k + 3) * (3 ^ 1 * 5) : ℕ) : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hm
    rw [h1]; push_cast at this ⊢; rw [this]; simp
  have e5 := dvd_n (5 ^ 1) ⟨2 ^ (k + 3) * 3 ^ 1, by push_cast; ring⟩
  have e2 := dvd_n (2 ^ (k + 3)) ⟨3 ^ 1 * 5, by push_cast; ring⟩
  have e3 := dvd_n (3 ^ 1) ⟨2 ^ (k + 3) * 5, by push_cast; ring⟩
  have Hh := hyp_h k 1 ap aq u c H e5 e2 e3
  have HhT := hypT_h k ap aq u c HT e5 e2
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
  obtain ⟨s, e, hs, he, g5, g3, g2, gc⟩ := group_core_j1 k (ap * u) (ap * u) (ap * u) c
    (unit_h (5 ^ 1) e5 (cp5 ap hp5)) (unit_h (2 ^ (k + 3)) e2 (cp2 ap hpo))
    (unit_h (3 ^ 1) e3 (cp3 ap hp3)) Hh HhT
  have c5 : ap ≡ (-1) ^ s * aq [ZMOD 5] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq : ℤ)) (5 ^ 1)).1 (by
      rw [rel _ e5, g5]; push_cast; ring)
    simpa using this
  have c3 : ap ≡ (-1) ^ s * aq [ZMOD 3 ^ 1] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq : ℤ)) (3 ^ 1)).1 (by
      rw [rel _ e3, g3]; push_cast; ring)
    simpa using this
  have c2 : ap ≡ (-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e [ZMOD 2 ^ (k + 3)] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e : ℤ))
      (2 ^ (k + 3))).1 (by
      rw [rel _ e2, g2]; push_cast; ring)
    simpa using this
  obtain ⟨he1, hshape⟩ := shape_arith k 1 s e hs he ap aq hpo hqo hp hq hsum hne c5 c3 c2
  subst he1
  refine ⟨s, 1, hs, rfl, gc, hshape⟩

/-- **j = 1 analogue of `GA2MTop.top_chain`** (full analytic Lemma A3 for r = 1, j = 1, i = k+3 >= 3). -/
theorem top_chain_j1 (k : ℕ) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hP0 : 0 < aP) (hQ0 : 0 < aQ)
    (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hS : 2 ∣ aS) (hsum : aP + aQ < 2 ^ (k + 3) * (3 ^ 1 * 5)) (hne : aP ≠ aQ) (hePne : eP ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ 1),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    ((eQ = eP ∧ (aP = aQ + 2 ^ (k + 2) * (3 ^ 1 * 5) ∨ aQ = aP + 2 ^ (k + 2) * (3 ^ 1 * 5))) ∨
      (eQ = -eP ∧ aP + aQ = 2 ^ (k + 2) * (3 ^ 1 * 5))) := by
  have cop : ∀ a : ℕ, Odd a → ¬ 3 ∣ a → Nat.Coprime (2 ^ (k + 3) * 3 ^ 1) a := by
    intro a ha h3
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ?_) (Nat.Coprime.pow_left _ ?_)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 ha)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hHyp := top_equation k 1 aP aQ aS eP eQ eS hP5 hQ5 (cop aP hPo hP3) (cop aQ hQo hQ3) hS hePne
    (fun ψ hψ η2 hη2 η3 _ hodd => H ψ hψ η2 hη2 η3 hodd)
  have hHypT := triv_equation k 1 le_rfl aP aQ aS eP eQ eS hP5 hQ5 (cop aP hPo hP3) (cop aQ hQo hQ3)
    hS hePne (fun ψ hψ η2 hη2 hodd => H ψ hψ η2 hη2 1 hodd)
  have c3 : ∀ a : ℕ, ¬ 3 ∣ a → IsCoprime (a : ℤ) 3 := fun a h =>
    (Nat.isCoprime_iff_coprime).2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm
  have c5 : ∀ a : ℕ, ¬ 5 ∣ a → IsCoprime (a : ℤ) 5 := fun a h =>
    (Nat.isCoprime_iff_coprime).2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h).symm
  obtain ⟨s, e, hs, he, hc, hshape⟩ := top_shape_j1 k (aP : ℤ) (aQ : ℤ) _
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

/-! ## D. converse and witnesses (j = 1, n = 120) -/

theorem hypT_raw (k s e : ℕ) (ap aq : ℤ)
    (e5 : (ap : ZMod (5 ^ 1)) = (-1) ^ s * aq)
    (e2 : (ap : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e * aq)
    (ψ : DirichletCharacter ℂ (5 ^ 1)) (η2 : DirichletCharacter ℂ (2 ^ (k + 3)))
    (hη2 : η2.IsPrimitive) (hodd : ψ (-1) * η2 (-1) = -1) :
    ψ (ap : ZMod (5 ^ 1)) * η2 (ap : ZMod (2 ^ (k + 3))) =
      (-1) ^ (s + e) * (ψ (aq : ZMod (5 ^ 1)) * η2 (aq : ZMod (2 ^ (k + 3)))) := by
  rw [e5, e2]
  simp only [map_mul, map_pow]
  rw [eta2_val k η2 hη2]
  have key : ψ (-1) ^ s * ψ (aq : ZMod (5 ^ 1)) *
      ((η2 (-1) ^ s * (-1) ^ e) * η2 (aq : ZMod (2 ^ (k + 3)))) =
      (ψ (-1) * η2 (-1)) ^ s * (-1) ^ e *
      (ψ (aq : ZMod (5 ^ 1)) * η2 (aq : ZMod (2 ^ (k + 3)))) := by ring
  rw [key, hodd, pow_add (-1 : ℂ) s e]

theorem hypT_converse (k s e : ℕ) (ap aq : ℤ)
    (e5 : (ap : ZMod (5 ^ 1)) = (-1) ^ s * aq)
    (e2 : (ap : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e * aq) :
    HypTP k ap aq ((-1) ^ (s + e)) := by
  intro ψ _ η2 hη2 hodd _
  exact hypT_raw k s e ap aq e5 e2 ψ η2 hη2 hodd

/-- The full j = 1 equation (all odd top characters incl. eta3 = 1) from the converse data. -/
theorem top_equation_j1_of (k : ℕ) (s e : ℕ) (aP aQ aS : ℕ) (eS : ℂ)
    (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hPc : Nat.Coprime (2 ^ (k + 3) * 3 ^ 1) aP) (hQc : Nat.Coprime (2 ^ (k + 3) * 3 ^ 1) aQ)
    (hS : 2 ∣ aS)
    (e5 : ((aP : ℤ) : ZMod (5 ^ 1)) = (-1) ^ s * (aQ : ℤ))
    (e3 : ((aP : ℤ) : ZMod (3 ^ 1)) = (-1) ^ s * (aQ : ℤ))
    (e2 : ((aP : ℤ) : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e * (aQ : ℤ)) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ 1),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (1 : ℂ) * bracket (chi ψ (chi η2 η3)) aP + (-((-1) ^ (s + e))) * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0 := by
  intro ψ hψ η2 hη2 η3 hodd
  by_cases h3 : η3 = 1
  · subst h3
    have hodd' : ψ (-1) * η2 (-1) = -1 := by
      rw [MulChar.one_apply (isUnit_one.neg)] at hodd; simpa using hodd
    rw [bracket_top_triv k 1 le_rfl ψ hψ η2 hη2 aP hP5 hPc, bracket_top_triv k 1 le_rfl ψ hψ η2 hη2 aQ hQ5 hQc,
      bracket_even_any k 1 ψ hψ η2 hη2 aS hS, mul_zero, add_zero]
    have hT := hypT_raw k s e (aP : ℤ) (aQ : ℤ) e5 e2 ψ η2 hη2 hodd'
    simp only [Int.cast_natCast] at hT
    linear_combination (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹ * (η2 (3 : ZMod (2 ^ (k + 3))))⁻¹) * hT
  · have := top_equation_of_hypP k 1 aP aQ aS ((-1) ^ (s + e)) eS hP5 hQ5 hPc hQc hS
      (hypP_converse k 1 s e (aP : ℤ) (aQ : ℤ) e5 e3 e2) ψ hψ η2 hη2 η3 h3 hodd
    exact this

/-- n = 120 (k = 0, j = 1), shape A: entries (67, 7, 46), e = (1, 1, eS): the whole equation holds. -/
theorem top_equation_67_7 (eS : ℂ) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (0 + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ 1),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (1 : ℂ) * bracket (chi ψ (chi η2 η3)) 67 + (1 : ℂ) * bracket (chi ψ (chi η2 η3)) 7 +
          eS * bracket (chi ψ (chi η2 η3)) 46 = 0 := by
  have := top_equation_j1_of 0 0 1 67 7 46 eS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)
  simpa using this

theorem top_chain_67_7 :
    (((1 : ℂ) = 1 ∧ ((67 : ℕ) = 7 + 2 ^ (0 + 2) * (3 ^ 1 * 5) ∨ (7 : ℕ) = 67 + 2 ^ (0 + 2) * (3 ^ 1 * 5))) ∨
      ((1 : ℂ) = -1 ∧ (67 : ℕ) + 7 = 2 ^ (0 + 2) * (3 ^ 1 * 5))) :=
  top_chain_j1 0 67 7 46 1 1 0 (by decide) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_ne_zero (top_equation_67_7 0)

/-- n = 120, shape B: entries (53, 7, 60), e = (1, -1, eS). -/
theorem top_equation_53_7 (eS : ℂ) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (0 + 3)), η2.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ 1),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (1 : ℂ) * bracket (chi ψ (chi η2 η3)) 53 + (-1 : ℂ) * bracket (chi ψ (chi η2 η3)) 7 +
          eS * bracket (chi ψ (chi η2 η3)) 60 = 0 := by
  have := top_equation_j1_of 0 1 1 53 7 60 eS (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)
  simpa using this

theorem top_chain_53_7 :
    (((-1 : ℂ) = 1 ∧ ((53 : ℕ) = 7 + 2 ^ (0 + 2) * (3 ^ 1 * 5) ∨ (7 : ℕ) = 53 + 2 ^ (0 + 2) * (3 ^ 1 * 5))) ∨
      ((-1 : ℂ) = -1 ∧ (53 : ℕ) + 7 = 2 ^ (0 + 2) * (3 ^ 1 * 5))) :=
  top_chain_j1 0 53 7 60 1 (-1) 0 (by decide) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_ne_zero (top_equation_53_7 0)

end Erdos634.GA2NJ1

#print axioms Erdos634.GA2NJ1.bracket_top_triv
#print axioms Erdos634.GA2NJ1.triv_equation
#print axioms Erdos634.GA2NJ1.group_core_j1
#print axioms Erdos634.GA2NJ1.top_shape_j1
#print axioms Erdos634.GA2NJ1.top_chain_j1
#print axioms Erdos634.GA2NJ1.top_chain_67_7
#print axioms Erdos634.GA2NJ1.top_chain_53_7
