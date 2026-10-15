/-
GA2S, atom S: Prop K-c (i = 1), entry T divisible by 3 not by 5, r >= 2: the hidden-entry kills and the labelled theorem `kc_lab`.
  `kcT_even` : T = S even:   eS = 0 once P, Q are Good.
  `kcT_odd`  : T = P odd:    eP = 0 once eQ, eS vanish (or Q, S divisible by 5).
  `kc_lab`   : (P, Q odd, S even; hypothesis hT: T = P or T = Q or (T = S and j >= 2)):  the class sums vanish on every column prime to 5.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SR

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SS

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PG
open Erdos634.GA2SD Erdos634.GA2SJ Erdos634.GA2SK Erdos634.GA2SO Erdos634.GA2SP Erdos634.GA2SQ Erdos634.GA2SR
open Erdos634.GA2SL (unit3)

theorem kcT_even (r j : ℕ) (hr : 2 ≤ r) (aP aQ b : ℕ) (eP eQ eS : ℂ) (hS5 : ¬ 5 ∣ 2 * b)
    (hX : Good aP aQ eP eQ) (hY : Good aQ aP eQ eP) (H : H1 r j aP aQ (2 * b) eP eQ eS) : eS = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hD : 3 ^ j / Nat.gcd (3 ^ j) b ∣ 3 ^ j := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨ψ, η3, hψ, hη3, hodd⟩ := exists_L1char0 r (by omega) j _ hD
  have hbot := H ψ hψ η3 hodd
  set B : ℕ → ℂ := fun x => bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) x with hB
  have hB5 : ∀ x, 5 ∣ x → B x = 0 := fun x hx =>
    bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 1 j) hψ _ x hx
  have hBne : B (2 * b) ≠ 0 := by
    refine bracket_ne_zero_of_eq2 r 1 j ψ hψ (1 : DirichletCharacter ℂ (2 ^ 1)) η3 (2 * b) hS5 ?_
    have hc1 : (1 : DirichletCharacter ℂ (2 ^ 1)).conductor = 1 := DirichletCharacter.conductor_one
    rw [hc1, hη3, one_mul, dm_even1]
  have hz := pair_zero B hB5 aP aQ eP eQ hX hY
  have : eP * B aP + eQ * B aQ + eS * B (2 * b) = 0 := hbot
  rw [hz, zero_add] at this
  exact (mul_eq_zero.1 this).resolve_right hBne

theorem kcT_odd (r j : ℕ) (hr : 2 ≤ r) (aP aQ aS : ℕ) (eP eQ eS : ℂ) (hPo : aP % 2 = 1) (hP5 : ¬ 5 ∣ aP)
    (hQ : 5 ∣ aQ ∨ eQ = 0) (hS : 5 ∣ aS ∨ eS = 0) (H : H1 r j aP aQ aS eP eQ eS) : eP = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hD : 3 ^ j / Nat.gcd (3 ^ j) aP ∣ 3 ^ j := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨ψ, η3, hψ, hη3, hodd⟩ := exists_L1char0 r (by omega) j _ hD
  have hκ : (η3 (2 : ZMod (3 ^ j)))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (3 ^ j)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  have h2ne : ψ (2 : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ (half_unit r)
  -- the general kill, given a good psi'
  have kill : ∀ ψ' : DirichletCharacter ℂ (5 ^ r), ψ'.IsPrimitive → ψ' (-1) * η3 (-1) = -1 →
      (ψ' (2 : ZMod (5 ^ r)))⁻¹ * (η3 (2 : ZMod (3 ^ j)))⁻¹ ≠ 1 → eP = 0 := by
    intro ψ' hψ' hodd' hfac
    have hbot := H ψ' hψ' η3 hodd'
    have hQ0 : eQ * bracket (chi ψ' (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) aQ = 0 := by
      rcases hQ with h | h
      · rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 1 j) hψ' _ aQ h, mul_zero]
      · rw [h, zero_mul]
    have hS0 : eS * bracket (chi ψ' (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η3)) aS = 0 := by
      rcases hS with h | h
      · rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 1 j) hψ' _ aS h, mul_zero]
      · rw [h, zero_mul]
    rw [hQ0, hS0, add_zero, add_zero] at hbot
    exact (mul_eq_zero.1 hbot).resolve_right
      (bracket_ne_zero_odd r j ψ' hψ' η3 aP hη3 hP5 hPo hfac)
  by_cases hf : (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η3 (2 : ZMod (3 ^ j)))⁻¹ = 1
  · -- use psi^-1
    refine kill ψ⁻¹ (Erdos634.GA2SA.inv_prim r ψ hψ) ?_ ?_
    · have h1 : ψ⁻¹ (-1) = ψ (-1) := by
        rw [MulChar.inv_apply_eq_inv']
        rcases DirichletCharacter.even_or_odd ψ with h | h <;> rw [h] <;> norm_num
      rw [h1]; exact hodd
    · intro h
      rw [MulChar.inv_apply_eq_inv', inv_inv] at h
      have hsq : ψ (2 : ZMod (5 ^ r)) ^ 2 = 1 := by
        have e1 : (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η3 (2 : ZMod (3 ^ j)))⁻¹ =
            ψ (2 : ZMod (5 ^ r)) * (η3 (2 : ZMod (3 ^ j)))⁻¹ := by rw [hf, h]
        have e2 : ((ψ (2 : ZMod (5 ^ r)))⁻¹ - ψ (2 : ZMod (5 ^ r))) * (η3 (2 : ZMod (3 ^ j)))⁻¹ = 0 := by
          linear_combination e1
        have e3 := (mul_eq_zero.1 e2).resolve_right hκ
        field_simp at e3
        linear_combination -e3
      exact Erdos634.GA2SA.psi_two_sq_ne_one r hr ψ hψ hsq
  · exact kill ψ hψ hodd hf

theorem kc_lab (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : aP % 2 = 1) (hQo : aQ % 2 = 1) (hSe : aS % 2 = 0)
    (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 2 * (5 ^ r * 3 ^ j))
    (hgcd : Nat.gcd (Nat.gcd aP aQ) aS = 1)
    (hT : (3 ∣ aP ∧ ¬ 5 ∣ aP) ∨ (3 ∣ aQ ∧ ¬ 5 ∣ aQ) ∨ (3 ∣ aS ∧ ¬ 5 ∣ aS ∧ 2 ≤ j))
    (H : H1 r j aP aQ aS eP eQ eS) :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aP = x then eP else 0) + (if aQ = x then eQ else 0) + (if aS = x then eS else 0) = 0 := by
  have h3N : 3 ∣ 2 * (5 ^ r * 3 ^ j) := Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _) 2
  have h5N : 5 ∣ 2 * (5 ^ r * 3 ^ j) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _) 2
  have no3 : ∀ x y : ℕ, x ∈ ({aP, aQ, aS} : Finset ℕ) → y ∈ ({aP, aQ, aS} : Finset ℕ) → True := fun _ _ _ _ => trivial
  have hno3PQ : ¬ (3 ∣ aP ∧ 3 ∣ aQ) := by
    rintro ⟨h1, h2⟩
    have h3 : 3 ∣ aS := by omega
    have := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [hgcd] at this
    omega
  have hno3PS : ¬ (3 ∣ aP ∧ 3 ∣ aS) := by
    rintro ⟨h1, h2⟩
    have h3 : 3 ∣ aQ := by omega
    have := Nat.dvd_gcd (Nat.dvd_gcd h1 h3) h2
    rw [hgcd] at this
    omega
  have hno3QS : ¬ (3 ∣ aQ ∧ 3 ∣ aS) := by
    rintro ⟨h1, h2⟩
    have h3 : 3 ∣ aP := by omega
    have := Nat.dvd_gcd (Nat.dvd_gcd h3 h1) h2
    rw [hgcd] at this
    omega
  obtain ⟨bS, hbS⟩ : ∃ bS, aS = 2 * bS := ⟨aS / 2, by omega⟩
  have key : ∀ x : ℕ, ¬ 5 ∣ x →
      (5 ∣ aP ∨ eP = 0 ∨ (aP = aQ ∧ eP + eQ = 0)) → (5 ∣ aQ ∨ eQ = 0 ∨ (aQ = aP ∧ eQ + eP = 0)) →
      (5 ∣ aS ∨ eS = 0) →
      (if aP = x then eP else 0) + (if aQ = x then eQ else 0) + (if aS = x then eS else 0) = 0 := by
    intro x hx GP GQ GS
    have hSP : aS ≠ aP := by intro h; omega
    have hSQ : aS ≠ aQ := by intro h; omega
    by_cases hSx : aS = x
    · have hS5 : ¬ 5 ∣ aS := by rw [hSx]; exact hx
      have heS : eS = 0 := GS.resolve_left hS5
      rw [if_neg (fun h => hSP (by rw [hSx, h])), if_neg (fun h => hSQ (by rw [hSx, h])), if_pos hSx, heS]
      ring
    · rw [if_neg hSx, add_zero]
      by_cases hPx : aP = x
      · have hP5 : ¬ 5 ∣ aP := by rw [hPx]; exact hx
        by_cases hQx : aQ = x
        · have hQ5 : ¬ 5 ∣ aQ := by rw [hQx]; exact hx
          rw [if_pos hPx, if_pos hQx]
          rcases GP with h | h | ⟨_, h⟩
          · exact absurd h hP5
          · rcases GQ with h' | h' | ⟨_, h'⟩
            · exact absurd h' hQ5
            · rw [h, h']; ring
            · linear_combination h'
          · exact h
        · rw [if_pos hPx, if_neg hQx, add_zero]
          rcases GP with h | h | ⟨h, _⟩
          · exact absurd h hP5
          · exact h
          · exfalso; apply hQx; rw [← h]; exact hPx
      · rw [if_neg hPx, zero_add]
        by_cases hQx : aQ = x
        · have hQ5 : ¬ 5 ∣ aQ := by rw [hQx]; exact hx
          rw [if_pos hQx]
          rcases GQ with h | h | ⟨h, _⟩
          · exact absurd h hQ5
          · exact h
          · exfalso; apply hPx; rw [← h]; exact hQx
        · rw [if_neg hQx]
  intro x hx
  rcases hT with ⟨hP3, hP5⟩ | ⟨hQ3, hQ5⟩ | ⟨hS3, hS5, hj2⟩
  · -- T = P
    have hQ3 : ¬ 3 ∣ aQ := fun h => hno3PQ ⟨hP3, h⟩
    have hS3 : ¬ 3 ∣ bS := by
      intro h
      exact hno3PS ⟨hP3, by rw [hbS]; exact Dvd.dvd.mul_left h 2⟩
    have hz := kcP_zero r j hr hj aP aQ bS eP eQ eS hQo (by omega) hP3 hP5 hQ3 hS3 (by rw [← hbS]; exact H)
    have heP := kcT_odd r j hr aP aQ aS eP eQ eS hPo hP5 hz.1 (by rw [hbS]; exact hz.2) H
    refine key x hx (Or.inr (Or.inl heP)) (by rcases hz.1 with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) ?_
    rw [hbS]; exact hz.2
  · -- T = Q
    have hP3 : ¬ 3 ∣ aP := fun h => hno3PQ ⟨h, hQ3⟩
    have hS3 : ¬ 3 ∣ bS := by
      intro h
      exact hno3QS ⟨hQ3, by rw [hbS]; exact Dvd.dvd.mul_left h 2⟩
    have H' := H1_swap H
    have hz := kcP_zero r j hr hj aQ aP bS eQ eP eS hPo (by omega) hQ3 hQ5 hP3 hS3 (by rw [← hbS]; exact H')
    have heQ := kcT_odd r j hr aQ aP aS eQ eP eS hQo hQ5 hz.1 (by rw [hbS]; exact hz.2) H'
    refine key x hx (by rcases hz.1 with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) (Or.inr (Or.inl heQ)) ?_
    rw [hbS]; exact hz.2
  · -- T = S, j >= 2
    have hP3 : ¬ 3 ∣ aP := fun h => hno3PS ⟨h, hS3⟩
    have hQ3 : ¬ 3 ∣ aQ := fun h => hno3QS ⟨h, hS3⟩
    have GP : 5 ∣ aP ∨ eP = 0 ∨ (aP = aQ ∧ eP + eQ = 0) := by
      by_cases h5 : 5 ∣ aP
      · exact Or.inl h5
      · exact Or.inr (kcS_top r j hr hj2 aP aQ aS eP eQ eS hPo hQo hP0 hQ0 hS0 hsum hP3 hQ3 hS3 hS5 h5 H)
    have GQ : 5 ∣ aQ ∨ eQ = 0 ∨ (aQ = aP ∧ eQ + eP = 0) := by
      by_cases h5 : 5 ∣ aQ
      · exact Or.inl h5
      · exact Or.inr (kcS_top r j hr hj2 aQ aP aS eQ eP eS hQo hPo hQ0 hP0 hS0 (by omega) hQ3 hP3 hS3 hS5 h5
          (H1_swap H))
    have hgP : Good aP aQ eP eQ := by
      rcases GP with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hgQ : Good aQ aP eQ eP := by
      rcases GQ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have heS : eS = 0 := by
      have := kcT_even r j hr aP aQ bS eP eQ eS (by rw [← hbS]; exact hS5) hgP hgQ (by rw [← hbS]; exact H)
      exact this
    exact key x hx GP GQ (Or.inr heS)

end Erdos634.GA2SS

#print axioms Erdos634.GA2SS.kcT_even
#print axioms Erdos634.GA2SS.kcT_odd
#print axioms Erdos634.GA2SS.kc_lab
