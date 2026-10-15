/-
Theorem K-a in labelled form (i = 2, n = 4 * 5^r * 3^j, r >= 2, j >= 1): the class sums of the weights vanish on every
column prime to 5, from the odd-character equations at (psi primitive mod 5^r) x (eta2 mod 4) x (eta3 mod 3^j).
  `stepK0`  : X visible (prime to 30), Y invisible to the primitive eta3 (5 | Y or 3 | Y)  =>  eX = 0   (single column)
  `stepK1`  : X visible, Y arbitrary odd  =>  eX = 0 or (aX = aY and eX + eY = 0)   [top step `GA2SE.top_two` + bottom `GA2SD`]
  `stepK2`  : X odd, 3 | X (5 !| X), Y killed  =>  eX = 0                           [eta3 of conductor 3^j / gcd]
  `stepK3`  : the even entry                                                          [trivial characters]
  `theoremKa_lab`.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SE

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SF

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PF Erdos634.GA2PG
open Erdos634.GA2SC Erdos634.GA2SD Erdos634.GA2SE

theorem stepK0 (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hSe : aS % 2 = 0)
    (H : H3K r j aX aY aS eX eY eS) (hvX : ¬ 5 ∣ aX ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aX)
    (hY : 5 ∣ aY ∨ ¬ Nat.Coprime (2 ^ 2 * 3 ^ j) aY) : eX = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨χ4, hχ4, hχ4o⟩ := exists_chi4
  obtain ⟨ψ, η3, hψ, hη3c, hodd⟩ := exists_L1char_r r (by omega) j (3 ^ j) dvd_rfl χ4 hχ4o
  have hη3 : η3.IsPrimitive := hη3c
  have hbot := H ψ hψ χ4 η3 hodd
  rw [bracket_even_zero_r r j (by omega) ψ hψ χ4 hχ4 η3 aS hSe, mul_zero, add_zero] at hbot
  have hBY : bracket (chi ψ (chi χ4 η3)) aY = 0 := by
    rcases hY with h5 | hnc
    · exact bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 2 j) hψ _ aY h5
    · by_cases h5 : 5 ∣ aY
      · exact bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 2 j) hψ _ aY h5
      · rw [bracket_top_prim r 2 j ψ hψ χ4 hχ4 η3 hη3 aY h5, if_neg hnc]
  rw [hBY, mul_zero, add_zero] at hbot
  rw [bracket_top_prim r 2 j ψ hψ χ4 hχ4 η3 hη3 aX hvX.1, if_pos hvX.2] at hbot
  have hX3 : ¬ 3 ∣ aX := not3_of_cop j hj aX hvX.2
  have h1 : ψ (aX : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ (unit5r r aX hvX.1)
  have h2 : χ4 (aX : ZMod (2 ^ 2)) ≠ 0 := chi4_ne_zero χ4 hχ4o aX hXo
  have h3 : η3 (aX : ZMod (3 ^ j)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hX3).symm
  have : eX * (ψ (aX : ZMod (5 ^ r)) * (χ4 (aX : ZMod (2 ^ 2)) * η3 (aX : ZMod (3 ^ j)))) = 0 := hbot
  exact (mul_eq_zero.1 this).resolve_right (mul_ne_zero h1 (mul_ne_zero h2 h3))

theorem stepK1 (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hYo : aY % 2 = 1) (hSe : aS % 2 = 0)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hS0 : 0 < aS)
    (hsum : aX + aY + aS = 4 * (5 ^ r * 3 ^ j))
    (H : H3K r j aX aY aS eX eY eS) (hvX : ¬ 5 ∣ aX ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aX)
    (hY3 : 5 ∣ aY ∨ ¬ 3 ∣ aY) :
    eX = 0 ∨ (aX = aY ∧ eX + eY = 0) := by
  obtain ⟨χ4, hχ4, hχ4o⟩ := exists_chi4
  have hm0 := m0_odd_r r j
  have hX3 : ¬ 3 ∣ aX := not3_of_cop j hj aX hvX.2
  have hχX : χ4 (aX : ZMod (2 ^ 2)) ≠ 0 := chi4_ne_zero χ4 hχ4o aX hXo
  have EQ := top_two r j hr hj aX aY aS eX eY eS hSe hXo hYo hvX.1 hX3 hY3 H χ4 hχ4 hχ4o
  have h3N : 3 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have h5N : 5 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
  by_cases h5Y : 5 ∣ aY
  · rw [if_pos h5Y, add_zero] at EQ
    left
    exact (mul_eq_zero.1 EQ).resolve_right hχX
  · rw [if_neg h5Y] at EQ
    have hY3' : ¬ 3 ∣ aY := hY3.resolve_left h5Y
    by_cases hmatch : ((aY : ZMod (5 ^ r * 3 ^ j)) = (aX : ZMod (5 ^ r * 3 ^ j)) ∨
        (aY : ZMod (5 ^ r * 3 ^ j)) = -(aX : ZMod (5 ^ r * 3 ^ j)))
    · rw [if_pos hmatch] at EQ
      have hvY : ¬ 5 ∣ aY ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aY := ⟨h5Y, unit_cop j aY hYo hY3'⟩
      have hχY : χ4 (aY : ZMod (2 ^ 2)) ≠ 0 := chi4_ne_zero χ4 hχ4o aY hYo
      have hcvX := chi4_val χ4 hχ4o aX hXo
      have hcvY := chi4_val χ4 hχ4o aY hYo
      rcases hmatch with hm | hm
      · have hm' : aY ≡ aX [MOD 5 ^ r * 3 ^ j] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hm
        have hsh := shape_plus (5 ^ r * 3 ^ j) aY aX hm0 hYo hXo hY0 hX0 (by omega) (by omega) hm'
        rcases hsh with h | h | h
        · right
          refine ⟨h.symm, ?_⟩
          rw [h] at EQ
          have : (eX + eY) * χ4 (aX : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
          exact (mul_eq_zero.1 this).resolve_right hχX
        · left
          have hneq : eX = eY := by
            have hf : χ4 (aY : ZMod (2 ^ 2)) = - χ4 (aX : ZMod (2 ^ 2)) := by
              rw [hcvX, hcvY]
              have : aY % 4 = if aX % 4 = 1 then 3 else 1 := by split_ifs <;> omega
              split_ifs <;> first | rfl | omega | norm_num
            rw [hf] at EQ
            have : (eX - eY) * χ4 (aX : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
            have := (mul_eq_zero.1 this).resolve_right hχX
            linear_combination this
          exact bottomA_r r hr j hj aX aY aS ((5 ^ r * 3 ^ j - aX) / 2) eX eY eS (by omega) (by omega)
            (by omega) hvX.1 hX3 hXo hneq H
        · left
          have hneq : eY = eX := by
            have hf : χ4 (aX : ZMod (2 ^ 2)) = - χ4 (aY : ZMod (2 ^ 2)) := by
              rw [hcvX, hcvY]
              split_ifs <;> first | rfl | omega | norm_num
            rw [hf] at EQ
            have : (eY - eX) * χ4 (aY : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
            have := (mul_eq_zero.1 this).resolve_right hχY
            linear_combination this
          have := bottomA_r r hr j hj aY aX aS ((5 ^ r * 3 ^ j - aY) / 2) eY eX eS (by omega) (by omega)
            (by omega) hvY.1 hY3' hYo hneq (H3K_swap H)
          rw [← hneq]; exact this
      · left
        have hm' : 5 ^ r * 3 ^ j ∣ aX + aY := by
          have := (natcast_neg_iff (5 ^ r * 3 ^ j) aY aX).1 hm
          rwa [add_comm] at this
        have hsh := shape_minus (5 ^ r * 3 ^ j) aX aY hm0 hXo hYo hX0 hY0 (by omega) hm'
        have hcv : χ4 (aY : ZMod (2 ^ 2)) = χ4 (aX : ZMod (2 ^ 2)) := by
          rw [hcvX, hcvY]
          split_ifs <;> first | rfl | omega | norm_num
        rw [hcv] at EQ
        have h1 : (eX + eY) * χ4 (aX : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
        have h2 := (mul_eq_zero.1 h1).resolve_right hχX
        have h3 := bottomB_r r hr j hj aX aY aS eX eY eS hsh (by omega) hvX.1 hX3 hXo H
        linear_combination (1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h3
    · rw [if_neg hmatch, add_zero] at EQ
      left
      exact (mul_eq_zero.1 EQ).resolve_right hχX

theorem stepK1' (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hYo : aY % 2 = 1) (hSe : aS % 2 = 0)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hS0 : 0 < aS)
    (hsum : aX + aY + aS = 4 * (5 ^ r * 3 ^ j))
    (H : H3K r j aX aY aS eX eY eS) (hvX : ¬ 5 ∣ aX ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aX) :
    eX = 0 ∨ (aX = aY ∧ eX + eY = 0) := by
  by_cases hY : 5 ∣ aY ∨ ¬ 3 ∣ aY
  · exact stepK1 r j hr hj aX aY aS eX eY eS hXo hYo hSe hX0 hY0 hS0 hsum H hvX hY
  · left
    push Not at hY
    refine stepK0 r j hr hj aX aY aS eX eY eS hXo hSe H hvX (Or.inr ?_)
    intro hc
    exact not3_of_cop j hj aY hc hY.2

end Erdos634.GA2SF

#print axioms Erdos634.GA2SF.stepK0
#print axioms Erdos634.GA2SF.stepK1
