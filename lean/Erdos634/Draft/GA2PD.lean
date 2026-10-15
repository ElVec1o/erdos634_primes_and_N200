/-
GA2P, Theorem C (GA2Y_NOTES Section 5, i = 0, r = 1, j >= 2), part 1: the top equations at i = 0.
Here the 2-part is the trivial modulus 2^0 and eta2 = 1.
  `one_mod_one`        : (1 : DC (2^0)) x = 1.
  `bracket_C_visible`  : for ANY eta3 mod 3^j, 5 !| a, 3 !| a:  [a/n]_{psi eta3} = kappa psi(a) eta3(a), kappa != 0 independent of a.
  `eqprim_C`           : primitive eta3 (no hypothesis on the tile): sum over the visible entries of e_t psi(a_t) eta3(a_t) = 0.
  `eqall_C`            : arbitrary eta3, when every entry prime to 5 is prime to 3.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PA
import Erdos634.Draft.GA2PC
import Erdos634.Draft.GA2NB2

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PD

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC

theorem one_mod_one (x : ZMod (2 ^ 0)) : (1 : DirichletCharacter ℂ (2 ^ 0)) x = 1 := by
  haveI : Subsingleton (ZMod (2 ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
  have : x = 1 := Subsingleton.elim x 1
  rw [this, MulChar.map_one]

theorem one_prim : (1 : DirichletCharacter ℂ (2 ^ 0)).IsPrimitive := by
  show (1 : DirichletCharacter ℂ (2 ^ 0)).conductor = 2 ^ 0
  rw [DirichletCharacter.conductor_one]
  norm_num

theorem star_eq_of_coprime {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (b : ℕ) (hb : b.Coprime N) :
    χ.primitiveCharacter (b : ZMod χ.conductor) = χ (b : ZMod N) := by
  conv_rhs => rw [← changeLevel_primitiveCharacter χ]
  rw [changeLevel_nat _ _ b hb]


theorem bracket_C_visible (j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ a : ℕ, ¬ 5 ∣ a → Nat.Coprime 3 a →
      bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η3)) a =
        κ * (ψ (a : ZMod (5 ^ 1)) * η3 (a : ZMod (3 ^ j))) := by
  haveI : NeZero (2 ^ 0) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor = 1 := DirichletCharacter.conductor_one
  set M : ℕ := 2 ^ 0 * 3 ^ j with hM
  set f : ℕ := (1 : DirichletCharacter ℂ (2 ^ 0)).conductor * η3.conductor with hf
  refine ⟨∏ ℓ ∈ eulerPrimes M f, (1 - (ψ (ℓ : ZMod (5 ^ 1)))⁻¹ *
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
    apply Erdos634.GA2NF1.psi_three_ne_one 1 le_rfl ψ hψ
    have : (ψ ((3 : ℕ) : ZMod (5 ^ 1)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    have h' := inv_eq_one.1 this
    simpa using h'
  · intro a ha5 ha3
    have hcopM : Nat.Coprime M a := by
      rw [hM, pow_zero, one_mul]
      exact Nat.Coprime.pow_left _ ha3
    have hg1 : M.gcd a = 1 := hcopM
    have hdm : dm M a = M := by unfold dm; rw [hg1, Nat.div_one]
    have hMpos : 0 < M := by positivity
    rw [bracket_gen2 1 0 j ψ hψ 1 η3 a ha5]
    have hdvd : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor * η3.conductor ∣ dm M a := by
      rw [hdm, hc1, one_mul]
      exact (conductor_dvd_level η3).trans (by rw [hM, pow_zero, one_mul])
    rw [if_pos hdvd, hdm, hg1, Nat.div_one,
      div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne')]
    rw [Erdos634.GA2NB2.star_one (n := 2 ^ 0) a, star_eq_of_coprime η3 a (Nat.Coprime.pow_right _ ha3.symm)]
    ring


/-- The Theorem-C hypothesis: all odd characters psi (1 x eta3), psi primitive mod 5, eta3 mod 3^j. -/
def HC (j : ℕ) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
    ∀ η2 : DirichletCharacter ℂ (2 ^ 0), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η2 (-1) * η3 (-1) = -1 →
      ∑ t, e t * bracket (chi ψ (chi η2 η3)) (a t) = 0

/-- the visible entries: prime to 5 and to 3. -/
def visC (a : Fin 3 → ℕ) : Finset (Fin 3) := univ.filter (fun t => ¬ 5 ∣ a t ∧ Nat.Coprime 3 (a t))

theorem cop_iff (j : ℕ) (hj : 1 ≤ j) (b : ℕ) : Nat.Coprime (2 ^ 0 * 3 ^ j) b ↔ Nat.Coprime 3 b := by
  rw [pow_zero, one_mul]
  exact Nat.coprime_pow_left_iff (by omega) 3 b

theorem eqprim_C (j : ℕ) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (H : HC j a e)
    (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3.IsPrimitive) (hodd : ψ (-1) * η3 (-1) = -1) :
    ∑ t ∈ visC a, e t * (ψ (a t : ZMod (5 ^ 1)) * η3 (a t : ZMod (3 ^ j))) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h := H ψ hψ 1 η3 (by rw [one_mod_one]; simpa using hodd)
  refine Eq.trans ?_ h
  unfold visC
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h5 : 5 ∣ a t
  · rw [bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 0 j) hψ _ (a t) h5]; simp [h5]
  · rw [bracket_top_prim 1 0 j ψ hψ 1 one_prim η3 hη3 (a t) h5]
    by_cases hc : Nat.Coprime 3 (a t)
    · rw [if_pos ((cop_iff j hj _).2 hc), if_pos ⟨h5, hc⟩, one_mod_one]; ring
    · rw [if_neg (fun h' => hc ((cop_iff j hj _).1 h')), if_neg (fun h' => hc h'.2)]; ring

theorem eqall_C (j : ℕ) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (H : HC j a e)
    (hall : ∀ t, ¬ 5 ∣ a t → Nat.Coprime 3 (a t))
    (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hodd : ψ (-1) * η3 (-1) = -1) :
    ∑ t ∈ visC a, e t * (ψ (a t : ZMod (5 ^ 1)) * η3 (a t : ZMod (3 ^ j))) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨κ, hκ, hform⟩ := bracket_C_visible j hj ψ hψ η3
  have h := H ψ hψ 1 η3 (by rw [one_mod_one]; simpa using hodd)
  have h2 : κ * ∑ t ∈ visC a, e t * (ψ (a t : ZMod (5 ^ 1)) * η3 (a t : ZMod (3 ^ j))) = 0 := by
    refine Eq.trans ?_ h
    unfold visC
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h5 : 5 ∣ a t
    · rw [bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 0 j) hψ _ (a t) h5]; simp [h5]
    · rw [hform (a t) h5 (hall t h5), if_pos ⟨h5, hall t h5⟩]; ring
  exact (mul_eq_zero.1 h2).resolve_left hκ


theorem hodd_of (ψ : DirichletCharacter ℂ (5 ^ 1)) {N : ℕ} (η : DirichletCharacter ℂ N)
    (h : η (-1) = -ψ (-1)) : ψ (-1) * η (-1) = -1 := by
  rw [h]
  rcases DirichletCharacter.even_or_odd ψ with h1 | h1 <;> rw [h1] <;> norm_num

theorem C_rel (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (H : HC j a e)
    (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive) (t : Fin 3) (ht : t ∈ visC a) :
    ∑ t' ∈ visC a, (e t' * ψ (a t' : ZMod (5 ^ 1))) *
      ((if (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) then 1 else 0) +
        (-ψ (-1)) * (if (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j)) then 1 else 0)) = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hu : ∀ t' ∈ visC a, IsUnit (a t' : ZMod (3 ^ j)) := by
    intro t' ht'
    unfold visC at ht'
    have := (Finset.mem_filter.1 ht').2.2
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ this.symm
  have hε : (-ψ (-1)) = 1 ∨ (-ψ (-1)) = -1 := by
    rcases DirichletCharacter.even_or_odd ψ with h1 | h1 <;> rw [h1] <;> norm_num
  set c : Fin 3 → ℂ := fun t' => e t' * ψ (a t' : ZMod (5 ^ 1)) with hc
  have hpt : ∀ v, PhiV (3 ^ j) a c (visC a) v + (-ψ (-1)) * PhiV (3 ^ j) a c (visC a) (-v) = 0 := by
    by_cases hcard : (visC a).card ≤ 2
    · refine pointwise_small j hj a c (visC a) hcard hu hε ?_
      intro η hη hη1
      have := eqprim_C j (by omega) a e H ψ hψ η hη (hodd_of ψ η hη1)
      rw [← this]
      exact Finset.sum_congr rfl (fun t' _ => by simp only [hc]; ring)
    · have h3 : (visC a).card = 3 := by
        have := Finset.card_le_univ (visC a)
        simp only [Fintype.card_fin] at this
        omega
      have hV : visC a = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h3)
      have hall : ∀ t', ¬ 5 ∣ a t' → Nat.Coprime 3 (a t') := by
        intro t' h5
        have : t' ∈ visC a := by rw [hV]; exact Finset.mem_univ _
        exact (Finset.mem_filter.1 this).2.2
      refine pointwise_all j a c (visC a) hu hε ?_
      intro η hη1
      have := eqall_C j (by omega) a e H hall ψ hψ η (hodd_of ψ η hη1)
      rw [← this]
      exact Finset.sum_congr rfl (fun t' _ => by simp only [hc]; ring)
  exact pointwise_form (3 ^ j) a c (visC a) hu (-ψ (-1)) hpt t ht


/-! ### arithmetic -/

theorem eq_of_both (j : ℕ) (x y : ℕ) (hx : x < 5 * 3 ^ j) (hy : y < 5 * 3 ^ j)
    (h3 : x ≡ y [MOD 3 ^ j]) (h5 : x ≡ y [MOD 5]) : x = y := by
  have hc : Nat.Coprime 5 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  have := (Nat.modEq_and_modEq_iff_modEq_mul hc).1 ⟨h5, h3⟩
  exact Nat.ModEq.eq_of_lt_of_lt this hx hy

theorem not_both_dvd (j : ℕ) (x : ℕ) (hpos : 0 < x) (hlt : x < 5 * 3 ^ j) (h3 : 3 ^ j ∣ x) (h5 : 5 ∣ x) :
    False := by
  have hc : Nat.Coprime 5 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h5 h3
  have := Nat.le_of_dvd hpos this
  omega

theorem natcast_neg_iff (N : ℕ) (x y : ℕ) :
    (x : ZMod N) = -(y : ZMod N) ↔ N ∣ x + y := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add]
  constructor
  · intro h; rw [h]; ring
  · intro h; linear_combination h

theorem not_self_neg (j : ℕ) (hj : 1 ≤ j) (x : ℕ) (hx3 : Nat.Coprime 3 x) :
    (x : ZMod (3 ^ j)) ≠ -(x : ZMod (3 ^ j)) := by
  intro h
  rw [natcast_neg_iff] at h
  have h3 : 3 ∣ x + x := (dvd_pow_self 3 (by omega)).trans h
  have : 3 ∣ 2 * x := by rw [two_mul]; exact h3
  have h3x : 3 ∣ x := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h | h
    · omega
    · exact h
  have := Nat.eq_one_of_dvd_coprimes (a := 3) (b := x) (by simpa using hx3) (dvd_refl 3) h3x
  omega

theorem entry_lt (j : ℕ) (a : Fin 3 → ℕ) (hpos : ∀ t, 0 < a t) (hsum : a 0 + a 1 + a 2 = 5 * 3 ^ j)
    (t : Fin 3) : a t < 5 * 3 ^ j := by
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  fin_cases t <;> simp <;> omega

theorem pair_lt (j : ℕ) (a : Fin 3 → ℕ) (hpos : ∀ t, 0 < a t) (hsum : a 0 + a 1 + a 2 = 5 * 3 ^ j)
    (t t' : Fin 3) (hne : t ≠ t') : a t + a t' < 5 * 3 ^ j := by
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  fin_cases t <;> fin_cases t' <;> simp at hne ⊢ <;> omega


theorem C_top (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (hpos : ∀ t, 0 < a t)
    (hsum : a 0 + a 1 + a 2 = 5 * 3 ^ j) (H : HC j a e) :
    ∀ t ∈ visC a, ∑ t' ∈ visC a, (if a t' = a t then e t' else 0) = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  intro t ht
  have hvis : ∀ t' ∈ visC a, ¬ 5 ∣ a t' ∧ Nat.Coprime 3 (a t') := fun t' h => (Finset.mem_filter.1 h).2
  set πf : Fin 3 → ZMod (5 ^ 1) := fun t' =>
    if (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) then (a t' : ZMod (5 ^ 1)) else -(a t' : ZMod (5 ^ 1)) with hπf
  set xf : Fin 3 → ℂ := fun t' =>
    if (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) then e t'
    else if (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j)) then -e t' else 0 with hxf
  have hunit5 : ∀ t' ∈ visC a, IsUnit (a t' : ZMod (5 ^ 1)) := by
    intro t' ht'
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (hvis t' ht').1).symm
  have hπ : ∀ t' ∈ visC a, IsUnit (πf t') := by
    intro t' ht'
    simp only [hπf]
    split_ifs
    · exact hunit5 t' ht'
    · exact (hunit5 t' ht').neg
  have hh : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∑ t' ∈ visC a, xf t' * ψ (πf t') = 0 := by
    intro ψ hψ
    have hr := C_rel j hj a e H ψ hψ t ht
    refine Eq.trans ?_ hr
    refine Finset.sum_congr rfl (fun t' ht' => ?_)
    have hex : ¬ ((a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) ∧ (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))) := by
      rintro ⟨h1, h2⟩
      exact not_self_neg j (by omega) (a t) (hvis t ht).2 (h1.symm.trans h2)
    by_cases p3 : (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j))
    · have hm3 : ¬ (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j)) := fun h => hex ⟨p3, h⟩
      simp only [hxf, hπf, if_pos p3, if_neg hm3]
      ring
    · by_cases m3 : (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))
      · simp only [hxf, hπf, if_neg p3, if_pos m3]
        have : -(a t' : ZMod (5 ^ 1)) = (-1) * (a t' : ZMod (5 ^ 1)) := by ring
        rw [this, map_mul]
        ring
      · simp only [hxf, hπf, if_neg p3, if_neg m3]
        ring
  have hfv := five_vanish (visC a) πf hπ xf hh t ht
  refine Eq.trans (Finset.sum_congr rfl (fun t' ht' => ?_)) hfv
  have hπt : πf t = (a t : ZMod (5 ^ 1)) := by simp [hπf]
  by_cases p3 : (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j))
  · have hπt' : πf t' = (a t' : ZMod (5 ^ 1)) := by simp [hπf, p3]
    have hxt' : xf t' = e t' := by simp [hxf, p3]
    rw [hπt', hπt, hxt']
    by_cases heq : a t' = a t
    · rw [if_pos heq, if_pos (by rw [heq])]
    · rw [if_neg heq, if_neg]
      intro h5
      apply heq
      refine eq_of_both j _ _ (entry_lt j a hpos hsum t') (entry_lt j a hpos hsum t) ?_ ?_
      · exact (ZMod.natCast_eq_natCast_iff _ _ _).1 p3
      · exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h5
  · have hπt' : πf t' = -(a t' : ZMod (5 ^ 1)) := by simp [hπf, p3]
    have hne : a t' ≠ a t := fun h => p3 (by rw [h])
    rw [if_neg hne, hπt']
    by_cases m3 : (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))
    · have hxt' : xf t' = -e t' := by simp only [hxf, if_neg p3, if_pos m3]
      rw [hxt', hπt, if_neg]
      intro h5
      have h5' : (a t : ZMod (5 ^ 1)) = -(a t' : ZMod (5 ^ 1)) := h5.symm
      rw [natcast_neg_iff] at h5' m3
      have htt : t ≠ t' := by
        rintro rfl; exact p3 rfl
      have h3 : 3 ^ j ∣ a t + a t' := by
        have := m3; rwa [add_comm] at this
      exact not_both_dvd j (a t + a t') (by have := hpos t; omega) (pair_lt j a hpos hsum t t' htt) h3
        (by simpa using h5')
    · have hxt' : xf t' = 0 := by simp only [hxf, if_neg p3, if_neg m3]
      rw [hxt']
      simp


theorem class_zero_C (I : Finset (Fin 3)) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ)
    (hcl : ∀ t ∈ I, ∑ t' ∈ I, (if a t' = a t then e t' else 0) = 0)
    (w : Fin 3 → ℂ) (hw : ∀ t t', a t = a t' → w t = w t') : ∑ t ∈ I, e t * w t = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem a hx)]
  refine Finset.sum_eq_zero (fun v hv => ?_)
  obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv
  rw [Finset.sum_congr rfl (fun t ht => by rw [hw t t0 (Finset.mem_filter.1 ht).2]), ← Finset.sum_mul]
  have := hcl t0 ht0
  rw [Finset.sum_filter]
  rw [this, zero_mul]

theorem three_dvd_unique (j : ℕ) (a : Fin 3 → ℕ) (hsum : a 0 + a 1 + a 2 = 5 * 3 ^ j) (hj : 1 ≤ j)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (t t1 : Fin 3) (h : 3 ∣ a t) (h1 : 3 ∣ a t1) :
    t1 = t := by
  by_contra hne
  have h3j : 3 ∣ 5 * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 5
  have hall : 3 ∣ a 0 ∧ 3 ∣ a 1 ∧ 3 ∣ a 2 := by
    fin_cases t <;> fin_cases t1 <;> simp at hne h h1 ⊢ <;> omega
  have : 3 ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) := Nat.dvd_gcd hall.1 (Nat.dvd_gcd hall.2.1 hall.2.2)
  rw [hgcd] at this
  omega

theorem C_left (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (hpos : ∀ t, 0 < a t)
    (hsum : a 0 + a 1 + a 2 = 5 * 3 ^ j) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (H : HC j a e) (t : Fin 3) (h5 : ¬ 5 ∣ a t) (hc3 : ¬ Nat.Coprime 3 (a t)) : e t = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h3t : 3 ∣ a t := by
    by_contra hh; exact hc3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hh)
  obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 1 le_rfl (-1) (Or.inr rfl)
  obtain ⟨hψp, hψs⟩ := Erdos634.GA2LCore.mem_PrimPar.1 hψ
  have hodd : ψ (-1) * (1 : DirichletCharacter ℂ (2 ^ 0)) (-1) * (1 : DirichletCharacter ℂ (3 ^ j)) (-1) = -1 := by
    rw [hψs, one_mod_one, MulChar.one_apply (isUnit_one.neg)]; norm_num
  have h := H ψ hψp 1 1 hodd
  set B : ℕ → ℂ := fun x => bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) (1 : DirichletCharacter ℂ (3 ^ j)))) x with hB
  have hB5 : ∀ x, 5 ∣ x → B x = 0 := fun x hx =>
    bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 0 j) hψp _ x hx
  have hBne : B (a t) ≠ 0 :=
    bracket_triv_ne_zero2 1 0 j ψ hψp (Erdos634.GA2NF1.psi_two_ne_one 1 le_rfl ψ hψp)
      (Erdos634.GA2NF1.psi_three_ne_one 1 le_rfl ψ hψp) (a t) h5
  have huniq : ∀ t1, ¬ 5 ∣ a t1 → ¬ Nat.Coprime 3 (a t1) → t1 = t := by
    intro t1 _ hc1
    have : 3 ∣ a t1 := by
      by_contra hh; exact hc1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hh)
    exact three_dvd_unique j a hsum (by omega) hgcd t t1 h3t this
  -- split the sum
  have hsplit : ∑ t' : Fin 3, e t' * B (a t') =
      ∑ t' ∈ visC a, e t' * B (a t') + e t * B (a t) := by
    have hs : ∑ t' : Fin 3, e t' * B (a t') =
        ∑ t' : Fin 3, ((if t' ∈ visC a then e t' * B (a t') else 0) + (if t' = t then e t * B (a t) else 0)) := by
      refine Finset.sum_congr rfl (fun t' _ => ?_)
      by_cases h5' : 5 ∣ a t'
      · have : t' ∉ visC a := fun hv => (Finset.mem_filter.1 hv).2.1 h5'
        have hne : t' ≠ t := fun he => h5 (he ▸ h5')
        rw [hB5 _ h5', if_neg this, if_neg hne]; ring
      · by_cases hc' : Nat.Coprime 3 (a t')
        · have hv : t' ∈ visC a := Finset.mem_filter.2 ⟨Finset.mem_univ _, h5', hc'⟩
          have hne : t' ≠ t := fun he => hc3 (he ▸ hc')
          rw [if_pos hv, if_neg hne]; ring
        · have hv : t' ∉ visC a := fun hv => hc' (Finset.mem_filter.1 hv).2.2
          have he := huniq t' h5' hc'
          rw [if_neg hv, if_pos he, he]; ring
    rw [hs, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_ite_eq' Finset.univ t]
    simp
  have hvis0 : ∑ t' ∈ visC a, e t' * B (a t') = 0 :=
    class_zero_C (visC a) a e (C_top j hj a e hpos hsum H) (fun t' => B (a t')) (fun x y hxy => by simp [hxy])
  have hfull : ∑ t' : Fin 3, e t' * B (a t') = 0 := h
  rw [hsplit, hvis0, zero_add] at hfull
  exact (mul_eq_zero.1 hfull).resolve_right hBne


/-- **Theorem C (labelled form, i = 0, r = 1, j >= 2).**  n = 5 * 3^j, any primitive 3-tile a, weights e, and the
full odd-character system psi (1 x eta3): every class sum over the entries prime to 5 vanishes. -/
theorem theoremC_classes (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (hpos : ∀ t, 0 < a t)
    (hsum : a 0 + a 1 + a 2 = 5 * 3 ^ j) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (H : HC j a e) :
    ∀ t, ¬ 5 ∣ a t →
      ∑ t' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a t), e t' = 0 := by
  intro t h5
  by_cases hc3 : Nat.Coprime 3 (a t)
  · have htV : t ∈ visC a := Finset.mem_filter.2 ⟨Finset.mem_univ _, h5, hc3⟩
    have := C_top j hj a e hpos hsum H t htV
    rw [← this]
    unfold visC
    simp only [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun t' _ => ?_)
    by_cases heq : a t' = a t
    · by_cases h5' : 5 ∣ a t'
      · exact absurd (heq ▸ h5') h5
      · simp [heq, h5, hc3]
    · simp [heq]
  · have h0 := C_left j hj a e hpos hsum hgcd H t h5 hc3
    have h3t : 3 ∣ a t := by
      by_contra hh; exact hc3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hh)
    rw [Finset.sum_eq_single t]
    · exact h0
    · intro t' ht' hne
      exfalso
      have h3' : 3 ∣ a t' := by rw [(Finset.mem_filter.1 ht').2]; exact h3t
      exact hne (three_dvd_unique j a hsum (by omega) hgcd t t' h3t h3')
    · intro hh
      exfalso
      exact hh (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h5⟩, rfl⟩)

end Erdos634.GA2PD

#print axioms Erdos634.GA2PD.bracket_C_visible
#print axioms Erdos634.GA2PD.eqprim_C
#print axioms Erdos634.GA2PD.eqall_C
#print axioms Erdos634.GA2PD.C_rel
#print axioms Erdos634.GA2PD.C_top
#print axioms Erdos634.GA2PD.C_left
#print axioms Erdos634.GA2PD.theoremC_classes
