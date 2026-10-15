/-
**Theorem A, labelled form**: Lemma P at p = 5 for n = 2^(k+3) 3^j 5^r (j, r >= 1), i = k+3 >= 3.

Entries aP, aQ odd, aS even (positive, sum n, gcd 1), coefficients eP, eQ, eS in C.  Hypothesis `H`: the full odd-character system
  sum_t e_t [a_t/n]_chi = 0   for every chi = psi (eta2 x eta3), psi primitive mod 5^r, eta2 mod 2^(k+3), eta3 mod 3^j ARBITRARY, chi odd
(odd chi whose 5-part has conductor exactly 5^r; every eta mod M is such a pair by CRT).
Conclusion `theoremA_lab`: every column in I = {entries prime to 5} has zero class sum:
  (5 !| aP -> eP + [aP = aQ] eQ = 0) /\ (5 !| aQ -> eQ + [aQ = aP] eP = 0) /\ (5 !| aS -> eS = 0).
Proof (case split): top characters select odd columns by 3-level (`top_one`, `top_same` = A1/A2); both odd columns at the
same level j with eP eQ != 0 give shape A or B (`GA2NR2.top_chain_R` = A3), killed by `GA2NK.kill_A` / `kill_B` (A4/A5);
then the even column dies at eta = 1 (`even_kill`, F4).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NR2
import Erdos634.Draft.GA2NK

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NT

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2MTop Erdos634.GA2NB Erdos634.GA2NB2 Erdos634.GA2NR1 Erdos634.GA2NR2 Erdos634.GA2NF1 Erdos634.GA2NK
open Erdos634.GA2LCore

/-- the 3-part of d_a : 3^j / gcd(3^j, a). -/
def D3 (j a : ℕ) : ℕ := 3 ^ j / Nat.gcd (3 ^ j) a

theorem D3_dvd (j a : ℕ) : D3 j a ∣ 3 ^ j := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

theorem D3_eq_of_coprime (j a : ℕ) (h : ¬ 3 ∣ a) : D3 j a = 3 ^ j := by
  unfold D3
  have : Nat.Coprime (3 ^ j) a := Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h)
  rw [this, Nat.div_one]

theorem D3_lt_of_dvd (j : ℕ) (hj : 1 ≤ j) (a : ℕ) (ha : 0 < a) (h3 : 3 ∣ a) : D3 j a < 3 ^ j := by
  unfold D3
  have hg : 3 ∣ Nat.gcd (3 ^ j) a := Nat.dvd_gcd (dvd_pow_self 3 (by omega)) h3
  have hgpos : 0 < Nat.gcd (3 ^ j) a := Nat.gcd_pos_of_pos_right _ ha
  have : 1 < Nat.gcd (3 ^ j) a := by
    have := Nat.le_of_dvd hgpos hg
    omega
  exact Nat.div_lt_self (by positivity) this

theorem D3_pos (j a : ℕ) : 0 < D3 j a := by
  unfold D3
  exact Nat.div_pos (Nat.le_of_dvd (by positivity) (Nat.gcd_dvd_left _ _)) (Nat.gcd_pos_of_pos_left _ (by positivity))

/-! ## A1 / A2: one odd column selected by the top characters -/

theorem top_one (r k j : ℕ) (hr : 1 ≤ r) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : Odd aX) (hX5 : ¬ 5 ∣ aX) (hYo : Odd aY) (hS : 2 ∣ aS)
    (hY : 5 ∣ aY ∨ eY = 0 ∨ ¬ D3 j aX ∣ D3 j aY)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eX * bracket (chi ψ (chi η2 η3)) aX + eY * bracket (chi ψ (chi η2 η3)) aY +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    eX = 0 := by
  obtain ⟨ψ, η2, η3, hψ, hη2, hη3, hodd⟩ := exists_top r k j (D3 j aX) hr (D3_dvd j aX)
  have hc2 : η2.conductor = 2 ^ (k + 3) := hη2
  have h := H ψ hψ η2 η3 hodd
  rw [bracket_even_R r hr k j ψ hψ η2 hη2 η3 aS hS, mul_zero, add_zero] at h
  have hX : bracket (chi ψ (chi η2 η3)) aX ≠ 0 :=
    bracket_ne_zero_of_eq r k j ψ hψ η2 η3 aX hX5 (by rw [hc2, hη3, dm_odd k j aX hXo]; rfl)
  have hYz : eY * bracket (chi ψ (chi η2 η3)) aY = 0 := by
    rcases hY with h5 | h0 | hnd
    · rw [bracket_p_dvd hr (not5_dvd k j) hψ (chi η2 η3) aY h5, mul_zero]
    · rw [h0, zero_mul]
    · by_cases h5 : 5 ∣ aY
      · rw [bracket_p_dvd hr (not5_dvd k j) hψ (chi η2 η3) aY h5, mul_zero]
      · rw [bracket_eq_zero_of_not_dvd r k j ψ hψ η2 η3 aY h5, mul_zero]
        intro hd
        apply hnd
        rw [hc2, hη3, dm_odd k j aY hYo] at hd
        exact (Nat.mul_dvd_mul_iff_left (by positivity)).1 hd
  rw [hYz, add_zero] at h
  exact (mul_eq_zero.1 h).resolve_right hX

theorem top_same (r k j : ℕ) (hr : 1 ≤ r) (aX aS : ℕ) (eX eY eS : ℂ)
    (hXo : Odd aX) (hX5 : ¬ 5 ∣ aX) (hS : 2 ∣ aS)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eX * bracket (chi ψ (chi η2 η3)) aX + eY * bracket (chi ψ (chi η2 η3)) aX +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    eX + eY = 0 := by
  obtain ⟨ψ, η2, η3, hψ, hη2, hη3, hodd⟩ := exists_top r k j (D3 j aX) hr (D3_dvd j aX)
  have hc2 : η2.conductor = 2 ^ (k + 3) := hη2
  have h := H ψ hψ η2 η3 hodd
  rw [bracket_even_R r hr k j ψ hψ η2 hη2 η3 aS hS, mul_zero, add_zero] at h
  have hX : bracket (chi ψ (chi η2 η3)) aX ≠ 0 :=
    bracket_ne_zero_of_eq r k j ψ hψ η2 η3 aX hX5 (by rw [hc2, hη3, dm_odd k j aX hXo]; rfl)
  have : (eX + eY) * bracket (chi ψ (chi η2 η3)) aX = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_right hX

/-! ## A1, x even: the even column -/

theorem even_kill (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hS5 : ¬ 5 ∣ aS)
    (hOK : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ = 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    eS = 0 := by
  obtain ⟨ψ, hψ⟩ := nonempty5 r hr (-1) (Or.inr rfl)
  obtain ⟨hψp, hψs⟩ := mem_PrimPar.1 hψ
  have h := H ψ hψp 1 1 (by simp [MulChar.one_apply (isUnit_one.neg), hψs])
  rw [hOK ψ hψp 1 1, zero_add] at h
  have hne := bracket_triv_ne_zero r k j hj ψ hψp (psi_two_ne_one r hr ψ hψp) (psi_three_ne_one r hr ψ hψp)
    aS hS5
  exact (mul_eq_zero.1 h).resolve_right hne

/-- The odd part vanishes in every character once the class sums of the odd columns are zero. -/
theorem odd_ok (r k j : ℕ) (hr : 1 ≤ r) (aP aQ : ℕ) (eP eQ : ℂ)
    (C1P : ¬ 5 ∣ aP → eP + (if aP = aQ then eQ else 0) = 0)
    (C1Q : ¬ 5 ∣ aQ → eQ + (if aQ = aP then eP else 0) = 0) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ = 0 := by
  intro ψ hψ η2 η3
  by_cases hP5 : 5 ∣ aP
  · rw [bracket_p_dvd hr (not5_dvd k j) hψ (chi η2 η3) aP hP5, mul_zero, zero_add]
    by_cases hQ5 : 5 ∣ aQ
    · rw [bracket_p_dvd hr (not5_dvd k j) hψ (chi η2 η3) aQ hQ5, mul_zero]
    · have := C1Q hQ5
      have hne : aQ ≠ aP := fun h => hQ5 (h ▸ hP5)
      rw [if_neg hne, add_zero] at this
      rw [this, zero_mul]
  · have hP := C1P hP5
    by_cases hQ5 : 5 ∣ aQ
    · have hne : aP ≠ aQ := fun h => hP5 (h ▸ hQ5)
      rw [if_neg hne, add_zero] at hP
      rw [hP, zero_mul, bracket_p_dvd hr (not5_dvd k j) hψ (chi η2 η3) aQ hQ5, mul_zero, add_zero]
    · by_cases heq : aP = aQ
      · rw [if_pos heq] at hP
        subst heq
        have : (eP + eQ) * bracket (chi ψ (chi η2 η3)) aP = 0 := by rw [hP, zero_mul]
        linear_combination this
      · have hQ := C1Q hQ5
        rw [if_neg heq, add_zero] at hP
        rw [if_neg (fun h => heq h.symm), add_zero] at hQ
        rw [hP, hQ, zero_mul, zero_mul, add_zero]

/-! ## A3 + A4 + A5: both odd columns at level j, distinct, both coefficients nonzero: contradiction -/

theorem a3_kill (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hS : 2 ∣ aS) (hS0 : 0 < aS) (hP0 : 0 < aP) (hQ0 : 0 < aQ)
    (hsum : aP + aQ + aS = 2 ^ (k + 3) * (3 ^ j * 5 ^ r)) (hne : aP ≠ aQ)
    (hePne : eP ≠ 0) (heQne : eQ ≠ 0)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    False := by
  have hshape := top_chain_R r k j hr hj aP aQ aS eP eQ eS hPo hQo hP0 hQ0 hP3 hQ3 hP5 hQ5 hS
    (by omega) hne hePne (fun ψ hψ η2 hη2 η3 _ hodd => H ψ hψ η2 η3 hodd)
  rcases hshape with ⟨heq, hA | hA⟩ | ⟨heq, hB⟩
  · -- shape A, aP = aQ + h : low = Q
    rw [heq] at H
    have := kill_A r k j hr hj aQ aP aS eP eS hQo hQ3 hQ5 hS0 (by omega) hA
      (fun ψ hψ η2 η3 hodd => by have := H ψ hψ η2 η3 hodd; linear_combination this)
    exact hePne this
  · -- shape A, aQ = aP + h : low = P
    rw [heq] at H
    have := kill_A r k j hr hj aP aQ aS eP eS hPo hP3 hP5 hS0 hsum hA
      (fun ψ hψ η2 η3 hodd => H ψ hψ η2 η3 hodd)
    exact hePne this
  · -- shape B
    rw [heq] at H
    exact hePne (kill_B r k j hr hj aP aQ aS eP eS hPo hQo hP3 hQ3 hP5 hQ5 hsum hB H)

/-! ## the case split -/

theorem step_odd (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hSe : 2 ∣ aS) (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 2 ^ (k + 3) * (3 ^ j * 5 ^ r))
    (hF2 : ¬ (3 ∣ aP ∧ 3 ∣ aQ))
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    (¬ 5 ∣ aP → eP + (if aP = aQ then eQ else 0) = 0) ∧
    (¬ 5 ∣ aQ → eQ + (if aQ = aP then eP else 0) = 0) := by
  have HQ : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eQ * bracket (chi ψ (chi η2 η3)) aQ + eP * bracket (chi ψ (chi η2 η3)) aP +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0 :=
    fun ψ hψ η2 η3 hodd => by have := H ψ hψ η2 η3 hodd; linear_combination this
  -- the key trichotomy for two columns in I
  have both : ¬ 5 ∣ aP → ¬ 5 ∣ aQ → (aP = aQ → eP + eQ = 0) ∧ (aP ≠ aQ → eP = 0 ∧ eQ = 0) := by
    intro hP5 hQ5
    refine ⟨fun heq => ?_, fun hne => ?_⟩
    · subst heq
      exact top_same r k j hr aP aS eP eQ eS hPo hP5 hSe H
    · by_cases h3P : 3 ∣ aP
      · have h3Q : ¬ 3 ∣ aQ := fun h => hF2 ⟨h3P, h⟩
        have hlt : ¬ D3 j aQ ∣ D3 j aP := by
          intro hd
          have := Nat.le_of_dvd (D3_pos j aP) hd
          rw [D3_eq_of_coprime j aQ h3Q] at this
          have := D3_lt_of_dvd j hj aP hP0 h3P
          omega
        have eQ0 := top_one r k j hr aQ aP aS eQ eP eS hQo hQ5 hPo hSe (Or.inr (Or.inr hlt)) HQ
        have eP0 := top_one r k j hr aP aQ aS eP eQ eS hPo hP5 hQo hSe (Or.inr (Or.inl eQ0)) H
        exact ⟨eP0, eQ0⟩
      · by_cases h3Q : 3 ∣ aQ
        · have hlt : ¬ D3 j aP ∣ D3 j aQ := by
            intro hd
            have := Nat.le_of_dvd (D3_pos j aQ) hd
            rw [D3_eq_of_coprime j aP h3P] at this
            have := D3_lt_of_dvd j hj aQ hQ0 h3Q
            omega
          have eP0 := top_one r k j hr aP aQ aS eP eQ eS hPo hP5 hQo hSe (Or.inr (Or.inr hlt)) H
          have eQ0 := top_one r k j hr aQ aP aS eQ eP eS hQo hQ5 hPo hSe (Or.inr (Or.inl eP0)) HQ
          exact ⟨eP0, eQ0⟩
        · by_cases heQ : eQ = 0
          · have eP0 := top_one r k j hr aP aQ aS eP eQ eS hPo hP5 hQo hSe (Or.inr (Or.inl heQ)) H
            exact ⟨eP0, heQ⟩
          · by_cases heP : eP = 0
            · have eQ0 := top_one r k j hr aQ aP aS eQ eP eS hQo hQ5 hPo hSe (Or.inr (Or.inl heP)) HQ
              exact ⟨heP, eQ0⟩
            · exact (a3_kill r k j hr hj aP aQ aS eP eQ eS hPo hQo h3P h3Q hP5 hQ5 hSe hS0 hP0 hQ0 hsum hne
                heP heQ H).elim
  refine ⟨fun hP5 => ?_, fun hQ5 => ?_⟩
  · by_cases hQ5 : 5 ∣ aQ
    · have hne : aP ≠ aQ := fun h => hP5 (h ▸ hQ5)
      rw [if_neg hne, add_zero]
      exact top_one r k j hr aP aQ aS eP eQ eS hPo hP5 hQo hSe (Or.inl hQ5) H
    · by_cases heq : aP = aQ
      · rw [if_pos heq]; exact (both hP5 hQ5).1 heq
      · rw [if_neg heq, add_zero]; exact ((both hP5 hQ5).2 heq).1
  · by_cases hP5 : 5 ∣ aP
    · have hne : aQ ≠ aP := fun h => hQ5 (h ▸ hP5)
      rw [if_neg hne, add_zero]
      exact top_one r k j hr aQ aP aS eQ eP eS hQo hQ5 hPo hSe (Or.inl hP5) HQ
    · by_cases heq : aQ = aP
      · rw [if_pos heq]; rw [add_comm]; exact (both hP5 hQ5).1 heq.symm
      · rw [if_neg heq, add_zero]; exact ((both hP5 hQ5).2 (fun h => heq h.symm)).2

/-- **Theorem A (labelled form).** -/
theorem theoremA_lab (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hSe : 2 ∣ aS) (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 2 ^ (k + 3) * (3 ^ j * 5 ^ r))
    (hgcd : Nat.gcd (Nat.gcd aP aQ) aS = 1)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    (¬ 5 ∣ aP → eP + (if aP = aQ then eQ else 0) = 0) ∧
    (¬ 5 ∣ aQ → eQ + (if aQ = aP then eP else 0) = 0) ∧ (¬ 5 ∣ aS → eS = 0) := by
  have h3n : 3 ∣ 2 ^ (k + 3) * (3 ^ j * 5 ^ r) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _) _
  have hF2 : ¬ (3 ∣ aP ∧ 3 ∣ aQ) := by
    rintro ⟨h1, h2⟩
    have h3S : 3 ∣ aS := by omega
    have : 3 ∣ Nat.gcd (Nat.gcd aP aQ) aS := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3S
    rw [hgcd] at this
    omega
  obtain ⟨C1P, C1Q⟩ := step_odd r k j hr hj aP aQ aS eP eQ eS hPo hQo hSe hP0 hQ0 hS0 hsum hF2 H
  refine ⟨C1P, C1Q, fun hS5 => ?_⟩
  exact even_kill r k j hr hj aP aQ aS eP eQ eS hS5 (odd_ok r k j hr aP aQ eP eQ C1P C1Q)
    (fun ψ hψ η2 η3 hodd => H ψ hψ η2 η3 hodd)

end Erdos634.GA2NT

#print axioms Erdos634.GA2NT.top_one
#print axioms Erdos634.GA2NT.top_same
#print axioms Erdos634.GA2NT.even_kill
#print axioms Erdos634.GA2NT.a3_kill
#print axioms Erdos634.GA2NT.step_odd
#print axioms Erdos634.GA2NT.theoremA_lab
