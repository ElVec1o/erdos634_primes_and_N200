/-
GA2U, atom E: Lemma T, case B (the 3-divisible entry T is odd; the other two are one odd Q and one even S = 2b).
  `topB` : j >= 2, H1 1 j aT aQ (2 b) eT eQ eS with 3 | aT, 5 !| aT, 3 !| aQ, 3 !| b:
           (5 | aQ or eQ = 0) and (5 | 2 b or eS = 0).
  Route: psi = an odd primitive character mod 5 (psi(2)^2 = -1), eta primitive EVEN mod 3^j (T invisible: `bracket_i1_three`);
  tokens aQ, aQ/2, b mod 3^j with weights w, -w psi(2)^-1, v, and `GA2UD.three_atoms`.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2UD
import Erdos634.Draft.GA2UA
import Erdos634.Draft.GA2SP
import Erdos634.Draft.GA2PJ

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UE

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.GA2SP (H1 H1_swap unit_cop1)
open Erdos634.GA2SL (unit3)
open Erdos634.GA2SD (unit5r)
open Erdos634.GA2PA (not5_dvd')

theorem inv2_cast (j : ℕ) : (2 : ZMod (3 ^ j)) * ((((3 ^ j + 1) / 2 : ℕ)) : ZMod (3 ^ j)) = 1 := by
  have hodd : (3 ^ j) % 2 = 1 := by
    have : Odd (3 ^ j) := Odd.pow (by decide)
    exact Nat.odd_iff.1 this
  have h : 2 * ((3 ^ j + 1) / 2) = 3 ^ j + 1 := by omega
  have h2 : ((2 * ((3 ^ j + 1) / 2) : ℕ) : ZMod (3 ^ j)) = ((3 ^ j + 1 : ℕ) : ZMod (3 ^ j)) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one] at h2
  simpa using h2

theorem topB (j : ℕ) (hj : 2 ≤ j) (aT aQ b : ℕ) (eT eQ eS : ℂ)
    (hT3 : 3 ∣ aT) (hT5 : ¬ 5 ∣ aT) (hQo : aQ % 2 = 1) (hQ3 : ¬ 3 ∣ aQ) (hb3 : ¬ 3 ∣ b)
    (H : H1 1 j aT aQ (2 * b) eT eQ eS) : (5 ∣ aQ ∨ eQ = 0) ∧ (5 ∣ 2 * b ∨ eS = 0) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ 1) := ⟨by norm_num⟩
  obtain ⟨ψ, hψp, hψo⟩ := Erdos634.GA2UA.exists_psi_odd
  have hs := Erdos634.GA2UA.psi_odd_sq ψ hψo
  have hs2 : ψ (2 : ZMod (5 ^ 1)) ≠ 0 := by
    intro h0; rw [h0] at hs; norm_num at hs
  set s := ψ (2 : ZMod (5 ^ 1)) with hsdef
  -- the basic equation for every primitive even eta
  have hbasic : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive → η (-1) = 1 →
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aQ +
        eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (2 * b) = 0 := by
    intro η hη he
    have hodd : ψ (-1) * η (-1) = -1 := by rw [hψo, he]; norm_num
    have hb := H ψ hψp η hodd
    rw [Erdos634.GA2PJ.bracket_i1_three 1 j (by omega) ψ hψp η hη aT hT5 hT3, mul_zero, zero_add] at hb
    exact hb
  -- weights
  set h2 : ℕ := (3 ^ j + 1) / 2 with hh2
  have hh2u : IsUnit (h2 : ZMod (3 ^ j)) := by
    have := inv2_cast j
    exact (isUnit_iff_exists_inv).2 ⟨2, by rw [mul_comm]; exact this⟩
  set wQ : ℂ := if 5 ∣ aQ then 0 else eQ * ψ (aQ : ZMod (5 ^ 1)) with hwQ
  set wS : ℂ := if 5 ∣ 2 * b then 0 else eS * ψ (b : ZMod (5 ^ 1)) with hwS
  set a : Fin 3 → ℕ := ![aQ, aQ * h2, b] with ha
  set c : Fin 3 → ℂ := ![wQ, -wQ * s⁻¹, wS] with hc
  have hu : ∀ t, IsUnit (a t : ZMod (3 ^ j)) := by
    intro t
    fin_cases t
    · exact unit3 j aQ hQ3
    · simp only [ha]
      show IsUnit ((aQ * h2 : ℕ) : ZMod (3 ^ j))
      rw [Nat.cast_mul]
      exact (unit3 j aQ hQ3).mul hh2u
    · exact unit3 j b hb3
  have h10 : (a 1 : ZMod (3 ^ j)) ≠ a 0 ∧ (a 1 : ZMod (3 ^ j)) ≠ -(a 0 : ZMod (3 ^ j)) := by
    have hQu := unit3 j aQ hQ3
    have e1 : (a 1 : ZMod (3 ^ j)) = (aQ : ZMod (3 ^ j)) * (h2 : ZMod (3 ^ j)) := by
      simp only [ha]; show ((aQ * h2 : ℕ) : ZMod (3 ^ j)) = _; rw [Nat.cast_mul]
    have e0 : (a 0 : ZMod (3 ^ j)) = (aQ : ZMod (3 ^ j)) := rfl
    have h2c := inv2_cast j
    rw [← hh2] at h2c
    constructor
    · intro h
      rw [e1, e0] at h
      have : (h2 : ZMod (3 ^ j)) = 1 := by
        have := hQu.mul_left_cancel (a := (aQ : ZMod (3 ^ j))) (b := (h2 : ZMod (3 ^ j))) (c := 1)
          (by rw [mul_one]; exact h)
        exact this
      rw [this, mul_one] at h2c
      exact Erdos634.GA2UB.two_ne_one3 j hj h2c
    · intro h
      rw [e1, e0] at h
      have : (h2 : ZMod (3 ^ j)) = -1 := by
        have := hQu.mul_left_cancel (a := (aQ : ZMod (3 ^ j))) (b := (h2 : ZMod (3 ^ j))) (c := -1)
          (by rw [mul_neg, mul_one]; exact h)
        exact this
      rw [this, mul_neg_one] at h2c
      exact Erdos634.GA2UB.two_ne_neg_one3 j hj (by linear_combination -h2c)
  have hBQ : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aQ =
        wQ * η (aQ : ZMod (3 ^ j)) * (1 - s⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹) := by
    intro η hη
    by_cases h5 : 5 ∣ aQ
    · rw [hwQ, if_pos h5, Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 1 j) hψp _ aQ h5]
      ring
    · rw [hwQ, if_neg h5, Erdos634.GA2PJ.bracket_i1_odd 1 j (by omega) ψ hψp η hη aQ h5
        (unit_cop1 j aQ hQo hQ3)]
      ring
  have hBS : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (2 * b) = wS * η (b : ZMod (3 ^ j)) := by
    intro η hη
    by_cases h5 : 5 ∣ 2 * b
    · rw [hwS, if_pos h5, Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 1 j) hψp _ (2 * b) h5]
      ring
    · rw [hwS, if_neg h5, Erdos634.GA2PJ.bracket_i1_even 1 j (by omega) ψ hψp η hη b h5 hb3]
      ring
  have horth : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive → η (-1) = 1 →
      ∑ t, c t * η (a t : ZMod (3 ^ j)) = 0 := by
    intro η hη he
    have hb := hbasic η hη he
    rw [hBQ η hη, hBS η hη] at hb
    have hηh2 : η (h2 : ZMod (3 ^ j)) = (η (2 : ZMod (3 ^ j)))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul]
      have := inv2_cast j
      rw [← hh2] at this
      rw [this, map_one]
    rw [Fin.sum_univ_three]
    have e1 : (a 1 : ZMod (3 ^ j)) = (aQ : ZMod (3 ^ j)) * (h2 : ZMod (3 ^ j)) := by
      simp only [ha]; show ((aQ * h2 : ℕ) : ZMod (3 ^ j)) = _; rw [Nat.cast_mul]
    have e0 : (a 0 : ZMod (3 ^ j)) = (aQ : ZMod (3 ^ j)) := rfl
    have e2 : (a 2 : ZMod (3 ^ j)) = (b : ZMod (3 ^ j)) := rfl
    have c0 : c 0 = wQ := rfl
    have c1 : c 1 = -wQ * s⁻¹ := rfl
    have c2 : c 2 = wS := rfl
    rw [e0, e1, e2, c0, c1, c2, map_mul, hηh2]
    linear_combination hb
  have hκ1 : -s⁻¹ ≠ 1 := by
    intro h
    have : s = -1 := by
      field_simp at h
      linear_combination -h
    rw [this] at hs; norm_num at hs
  have hκ0 : -s⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hs2)
  obtain ⟨z0, -, z2⟩ := Erdos634.GA2UD.three_atoms j hj a c hu h10 horth (-s⁻¹) hκ0 hκ1
    (by show -wQ * s⁻¹ = -s⁻¹ * wQ; ring)
  have z0' : wQ = 0 := z0
  have z2' : wS = 0 := z2
  refine ⟨?_, ?_⟩
  · by_cases h5 : 5 ∣ aQ
    · exact Or.inl h5
    · right
      rw [hwQ, if_neg h5] at z0'
      exact (mul_eq_zero.1 z0').resolve_right (Erdos634.GA2LCore.nz ψ _ (unit5r 1 aQ h5))
  · by_cases h5 : 5 ∣ 2 * b
    · exact Or.inl h5
    · right
      rw [hwS, if_neg h5] at z2'
      have hb5 : ¬ 5 ∣ b := fun h => h5 (Dvd.dvd.mul_left h 2)
      exact (mul_eq_zero.1 z2').resolve_right (Erdos634.GA2LCore.nz ψ _ (unit5r 1 b hb5))

end Erdos634.GA2UE

#print axioms Erdos634.GA2UE.topB
