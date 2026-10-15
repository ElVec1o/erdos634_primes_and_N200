/-
GA2S, atom P: Prop K-c (i = 1) with an entry T divisible by 3, not by 5 (r >= 2): the case T ODD (T = P or T = Q), any j >= 1.

For a PRIMITIVE eta3 mod 3^j the odd entry T (3 | T) is invisible (`GA2PJ.bracket_i1_three`); the two remaining entries give
tokens  b([2v] - kappa [v]) + c [-u-v]  (kappa = eta3(2)^-1, 2u = T, 2v = Q, -u-v = S/2 mod 5^r) with a = 0, so the 5-adic pattern
step (`GA2SO.five_pattern` with a = 0, `concl_a0`) forces b = c = 0, i.e. eQ = 0 and eS = 0 (for those not divisible by 5).
  `H1`, `H1_swap`, `exists_half`, `half_unit'`, `odd_expr`, `neg_half_unit`, `unit_cop1` : tools
  `kcP_zero` : T = P  =>  (5 | Q or eQ = 0) and (5 | S or eS = 0).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SO
import Erdos634.Draft.GA2SL
import Erdos634.Draft.GA2PJ

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SP

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PG
open Erdos634.GA2SD Erdos634.GA2SJ Erdos634.GA2SK Erdos634.GA2SO
open Erdos634.GA2SL (unit3)

def H1 (r j : ℕ) (aP aQ aS : ℕ) (eP eQ eS : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
    ψ (-1) * η (-1) = -1 →
    eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aP +
    eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aQ +
    eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aS = 0

theorem H1_swap {r j : ℕ} {aP aQ aS : ℕ} {eP eQ eS : ℂ} (H : H1 r j aP aQ aS eP eQ eS) :
    H1 r j aQ aP aS eQ eP eS := by
  intro ψ hψ η hodd
  have := H ψ hψ η hodd
  linear_combination this

theorem unit_cop1 (j : ℕ) (x : ℕ) (hx2 : x % 2 = 1) (hx3 : ¬ 3 ∣ x) : Nat.Coprime (2 ^ 1 * 3 ^ j) x := by
  apply Nat.Coprime.mul_left
  · apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  · exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hx3)

theorem exists_half (r : ℕ) (x : ZMod (5 ^ r)) : ∃ u : ZMod (5 ^ r), 2 * u = x := by
  obtain ⟨w, hw⟩ := (half_unit r).exists_right_inv
  exact ⟨w * x, by rw [← mul_assoc, hw, one_mul]⟩

theorem half_unit' (r : ℕ) {x u : ZMod (5 ^ r)} (hx : IsUnit x) (hu : 2 * u = x) : IsUnit u := by
  rw [← hu] at hx
  exact isUnit_of_mul_isUnit_right hx

theorem odd_expr (r : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) {u : ZMod (5 ^ r)} {a : ℕ}
    (hua : 2 * u = (a : ZMod (5 ^ r))) (κ : ℂ) :
    ψ (a : ZMod (5 ^ r)) * (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * κ) = ψ (2 * u) - κ * ψ u := by
  have h2 : ψ (2 : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ (half_unit r)
  have hmul : ψ (2 : ZMod (5 ^ r)) * ψ u = ψ (a : ZMod (5 ^ r)) := by rw [← map_mul, hua]
  rw [hua]
  have : ψ u = (ψ (2 : ZMod (5 ^ r)))⁻¹ * ψ (a : ZMod (5 ^ r)) := by
    field_simp; linear_combination hmul
  rw [this]; ring

theorem neg_half_unit (r : ℕ) {x : ZMod (5 ^ r)} (hx : IsUnit x) : ∃ u : ZMod (5 ^ r), IsUnit u ∧ 2 * u = -x := by
  obtain ⟨u, hu⟩ := exists_half r (-x)
  exact ⟨u, half_unit' r hx.neg hu, hu⟩

theorem kcP_zero (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aP aQ bS : ℕ) (eP eQ eS : ℂ)
    (hQo : aQ % 2 = 1)
    (hsum : aP + aQ + 2 * bS = 2 * (5 ^ r * 3 ^ j))
    (hP3 : 3 ∣ aP) (hP5 : ¬ 5 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hS3 : ¬ 3 ∣ bS)
    (H : H1 r j aP aQ (2 * bS) eP eQ eS) : (5 ∣ aQ ∨ eQ = 0) ∧ (5 ∣ 2 * bS ∨ eS = 0) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h5N : 5 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
  obtain ⟨η, hη⟩ := exists_prim3 j hj
  have hηη : η (-1) * η (-1) = 1 := by
    rcases DirichletCharacter.even_or_odd η with h | h <;> rw [h] <;> norm_num
  have hε : (-η (-1)) = 1 ∨ (-η (-1)) = -1 := by
    rcases DirichletCharacter.even_or_odd η with h | h <;> rw [h] <;> simp
  have hκ : (η (2 : ZMod (3 ^ j)))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (3 ^ j)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  have hbasic : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = -η (-1) →
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aQ +
        eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (2 * bS) = 0 := by
    intro ψ hψ h1
    have hodd : ψ (-1) * η (-1) = -1 := by rw [h1]; linear_combination -hηη
    have hb := H ψ hψ η hodd
    rw [Erdos634.GA2PJ.bracket_i1_three r j hj ψ hψ η hη aP hP5 hP3, mul_zero, zero_add] at hb
    exact hb
  have hPu : IsUnit (aP : ZMod (5 ^ r)) := unit5r r aP hP5
  obtain ⟨u, hu2⟩ := exists_half r (aP : ZMod (5 ^ r))
  have huu : IsUnit u := half_unit' r hPu hu2
  have hηQ : η (aQ : ZMod (3 ^ j)) ≠ 0 := Erdos634.GA2LCore.nz η _ (unit3 j aQ hQ3)
  have hηS : η (bS : ZMod (3 ^ j)) ≠ 0 := Erdos634.GA2LCore.nz η _ (unit3 j bS hS3)
  by_cases hQ5 : 5 ∣ aQ
  · refine ⟨Or.inl hQ5, Or.inr ?_⟩
    by_cases hS5 : 5 ∣ 2 * bS
    · exact absurd (by omega : 5 ∣ aP) hP5
    · have hbSu : IsUnit (bS : ZMod (5 ^ r)) := unit5r r bS (by omega)
      obtain ⟨w, hwu, hw2⟩ := neg_half_unit r hbSu
      have hww : -w - w = (bS : ZMod (5 ^ r)) := by linear_combination (-1 : ZMod (5 ^ r)) * hw2
      have key := five_pattern r hr (u := w) (v := w) hwu hwu (κ := (η (2 : ZMod (3 ^ j)))⁻¹)
        (ε := -η (-1)) (a := 0) (b := 0) (c := eS * η (bS : ZMod (3 ^ j))) hκ hε
        (Or.inr (by rw [hww]; exact hbSu)) (Or.inl rfl)
        (by
          intro ψ hψ h1
          have hb := hbasic ψ hψ h1
          rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 1 j) hψ _ aQ hQ5, mul_zero, zero_add,
            Erdos634.GA2PJ.bracket_i1_even r j hj ψ hψ η hη bS hS5 hS3] at hb
          rw [hww]
          linear_combination hb)
      have hc0 := (concl_a0 key).2
      have : eS = 0 := (mul_eq_zero.1 hc0).resolve_right hηS
      exact this
  · by_cases hS5 : 5 ∣ 2 * bS
    · refine ⟨Or.inr ?_, Or.inl hS5⟩
      obtain ⟨v, hv2⟩ := exists_half r (aQ : ZMod (5 ^ r))
      have hvu : IsUnit v := half_unit' r (unit5r r aQ hQ5) hv2
      have key := five_pattern r hr (u := u) (v := v) huu hvu (κ := (η (2 : ZMod (3 ^ j)))⁻¹)
        (ε := -η (-1)) (a := 0) (b := eQ * η (aQ : ZMod (3 ^ j))) (c := 0) hκ hε
        (Or.inl rfl) (Or.inr (Or.inr rfl))
        (by
          intro ψ hψ h1
          have hb := hbasic ψ hψ h1
          rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 1 j) hψ _ (2 * bS) hS5, mul_zero, add_zero,
            Erdos634.GA2PJ.bracket_i1_odd r j hj ψ hψ η hη aQ hQ5 (unit_cop1 j aQ hQo hQ3)] at hb
          have := odd_expr r ψ hv2 ((η (2 : ZMod (3 ^ j)))⁻¹)
          linear_combination hb - (eQ * η (aQ : ZMod (3 ^ j))) * this)
      have hb0 := (concl_a0 key).1
      exact (mul_eq_zero.1 hb0).resolve_right hηQ
    · obtain ⟨v, hv2⟩ := exists_half r (aQ : ZMod (5 ^ r))
      have hvu : IsUnit v := half_unit' r (unit5r r aQ hQ5) hv2
      have hbSu : IsUnit (bS : ZMod (5 ^ r)) := unit5r r bS (by omega)
      have hsumZ : (aP : ZMod (5 ^ r)) + aQ + 2 * bS = 0 := by
        have : ((aP + aQ + 2 * bS : ℕ) : ZMod (5 ^ r)) = 0 := by
          rw [hsum]
          exact zmod5r_of_dvd r _ (by
            have : 5 ^ r ∣ 5 ^ r * 3 ^ j := dvd_mul_right _ _
            exact Dvd.dvd.mul_left this 2)
        push_cast at this
        exact this
      have huv : -u - v = (bS : ZMod (5 ^ r)) := by
        have h2 : (2 : ZMod (5 ^ r)) * (-u - v - bS) = 0 := by
          linear_combination (-1 : ZMod (5 ^ r)) * hsumZ - hu2 - hv2
        have h2u := half_unit r
        have := (h2u.mul_right_eq_zero).1 h2
        linear_combination this
      have key := five_pattern r hr (u := u) (v := v) huu hvu (κ := (η (2 : ZMod (3 ^ j)))⁻¹)
        (ε := -η (-1)) (a := 0) (b := eQ * η (aQ : ZMod (3 ^ j))) (c := eS * η (bS : ZMod (3 ^ j))) hκ hε
        (Or.inr (by rw [huv]; exact hbSu)) (Or.inl rfl)
        (by
          intro ψ hψ h1
          have hb := hbasic ψ hψ h1
          rw [Erdos634.GA2PJ.bracket_i1_even r j hj ψ hψ η hη bS hS5 hS3,
            Erdos634.GA2PJ.bracket_i1_odd r j hj ψ hψ η hη aQ hQ5 (unit_cop1 j aQ hQo hQ3)] at hb
          have := odd_expr r ψ hv2 ((η (2 : ZMod (3 ^ j)))⁻¹)
          rw [huv]
          linear_combination hb - (eQ * η (aQ : ZMod (3 ^ j))) * this)
      obtain ⟨hb0, hc0⟩ := concl_a0 key
      exact ⟨Or.inr ((mul_eq_zero.1 hb0).resolve_right hηQ), Or.inr ((mul_eq_zero.1 hc0).resolve_right hηS)⟩

end Erdos634.GA2SP

#print axioms Erdos634.GA2SP.kcP_zero
