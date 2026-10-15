/-
GA2U, atom G: Lemma T, case A assembled: the 3-divisible entry is the EVEN one S; P, Q odd, prime to 3.
  `topA` : j >= 2, H1 1 j aP aQ aS eP eQ eS, 3 | aS, 5 !| aS:   Good aP aQ eP eQ  and  Good aQ aP eQ eP.
  Route: psi = psi_1, psi_1^-1 (odd primitive mod 5), eta primitive EVEN mod 3^j  =>  (two tokens, Lemma N at 3, `GA2UF.two_tok`)
  aQ = +-aP mod 3^j and e_P psi(aP) + e_Q psi(aQ) = 0;  `GA2UA.five_tri` for psi_1 and its inverse; arithmetic (aS divisible by 3,
  aS > 0) kills aQ = aP mod 3^j and the two "+- mod 5 and mod 3^j" combinations except (aQ = aP mod 5, aQ = -aP mod 3^j),
  which the EVEN psi_2 (Legendre) and ONE odd primitive eta with eta(2) != -1 kills.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2UF

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UG

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.GA2SP (H1 H1_swap unit_cop1)
open Erdos634.GA2SL (unit3)
open Erdos634.GA2SD (unit5r)
open Erdos634.GA2PG (Good)

theorem arith_three (j : ℕ) (hj : 1 ≤ j) (aP aQ aS : ℕ) (hP3 : ¬ 3 ∣ aP) (hS3 : 3 ∣ aS)
    (hsum : aP + aQ + aS = 2 * (5 ^ 1 * 3 ^ j)) (h : (aQ : ZMod (3 ^ j)) = (aP : ZMod (3 ^ j))) : False := by
  have h1 : aQ ≡ aP [MOD 3 ^ j] := (ZMod.natCast_eq_natCast_iff aQ aP (3 ^ j)).1 h
  have h2 : aQ ≡ aP [MOD 3] := Nat.ModEq.of_dvd (dvd_pow_self 3 (by omega)) h1
  have h3N : 3 ∣ 2 * (5 ^ 1 * 3 ^ j) := Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _) 2
  unfold Nat.ModEq at h2
  omega

theorem arith_minus (j : ℕ) (aP aQ aS : ℕ) (hPo : aP % 2 = 1) (hQo : aQ % 2 = 1) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 2 * (5 ^ 1 * 3 ^ j)) (h3 : 3 ^ j ∣ aP + aQ) (h5 : 5 ∣ aP + aQ) : False := by
  have hc : Nat.Coprime 5 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  have hN : 5 * 3 ^ j ∣ aP + aQ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h5 h3
  have hNodd : (5 * 3 ^ j) % 2 = 1 := by
    have : _root_.Odd (5 * 3 ^ j) := Odd.mul (by decide) (Odd.pow (by decide))
    exact Nat.odd_iff.1 this
  have hNpos : 0 < 5 * 3 ^ j := by positivity
  obtain ⟨k, hk⟩ := hN
  simp only [pow_one] at hsum
  generalize 5 * 3 ^ j = N at *
  have hk2 : k < 2 := by
    by_contra hh
    push Not at hh
    nlinarith
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; omega
    · exact h0
  interval_cases k
  omega

theorem cc_zero {a : ℕ} {e z : ℂ} (hz : z ≠ 0) (h : (if 5 ∣ a then (0 : ℂ) else e * z) = 0) : 5 ∣ a ∨ e = 0 := by
  by_cases h5 : 5 ∣ a
  · exact Or.inl h5
  · right
    rw [if_neg h5] at h
    exact (mul_eq_zero.1 h).resolve_right hz

theorem topA (j : ℕ) (hj : 2 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : aP % 2 = 1) (hQo : aQ % 2 = 1) (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hS3 : 3 ∣ aS) (hS5 : ¬ 5 ∣ aS)
    (hS0 : 0 < aS) (hsum : aP + aQ + aS = 2 * (5 ^ 1 * 3 ^ j))
    (H : H1 1 j aP aQ aS eP eQ eS) : Good aP aQ eP eQ ∧ Good aQ aP eQ eP := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ 1) := ⟨by norm_num⟩
  have hPu := unit3 j aP hP3
  have hQu := unit3 j aQ hQ3
  have hP5u : ∀ h : ¬ 5 ∣ aP, IsUnit (aP : ZMod (5 ^ 1)) := fun h => unit5r 1 aP h
  have hQ5u : ∀ h : ¬ 5 ∣ aQ, IsUnit (aQ : ZMod (5 ^ 1)) := fun h => unit5r 1 aQ h
  -- the dichotomy for an odd primitive psi
  have hD : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ψ (-1) = -1 →
      (((if 5 ∣ aP then 0 else eP * ψ (aP : ZMod (5 ^ 1))) = 0 ∧ (if 5 ∣ aQ then 0 else eQ * ψ (aQ : ZMod (5 ^ 1))) = 0) ∨
        (((aQ : ZMod (3 ^ j)) = (aP : ZMod (3 ^ j)) ∨ (aQ : ZMod (3 ^ j)) = -(aP : ZMod (3 ^ j))) ∧
          (if 5 ∣ aP then 0 else eP * ψ (aP : ZMod (5 ^ 1))) + (if 5 ∣ aQ then 0 else eQ * ψ (aQ : ZMod (5 ^ 1))) = 0)) := by
    intro ψ hψ hψo
    refine Erdos634.GA2UF.two_tok j hj aP aQ _ _ hPu hQu ?_
    intro η hη he
    have hodd : ψ (-1) * η (-1) = -1 := by rw [hψo, he]; norm_num
    have h1 := Erdos634.GA2UF.topA_eqn j (by omega) aP aQ aS eP eQ eS hPo hQo hP3 hQ3 hS3 hS5 H ψ hψ η hη hodd
    exact (mul_eq_zero.1 h1).resolve_right (Erdos634.GA2UF.F_ne_odd j (by omega) ψ hψo η)
  obtain ⟨ψ, hψp, hψo⟩ := Erdos634.GA2UA.exists_psi_odd
  have hψip : (ψ⁻¹).IsPrimitive := Erdos634.GA2SA.inv_prim 1 ψ hψp
  have hψio : ψ⁻¹ (-1) = -1 := Erdos634.GA2SA.inv_neg_one 1 ψ hψo
  have D1 := hD ψ hψp hψo
  have D2 := hD ψ⁻¹ hψip hψio
  by_cases hW : (aQ : ZMod (3 ^ j)) = (aP : ZMod (3 ^ j)) ∨ (aQ : ZMod (3 ^ j)) = -(aP : ZMod (3 ^ j))
  swap
  · -- no coincidence: both weights vanish
    have hz : (if 5 ∣ aP then (0 : ℂ) else eP * ψ (aP : ZMod (5 ^ 1))) = 0 ∧
        (if 5 ∣ aQ then (0 : ℂ) else eQ * ψ (aQ : ZMod (5 ^ 1))) = 0 := by
      rcases D1 with h | h
      · exact h
      · exact absurd h.1 hW
    refine ⟨?_, ?_⟩
    · by_cases h5 : 5 ∣ aP
      · exact Or.inl h5
      · exact Or.inr (Or.inl ((cc_zero (Erdos634.GA2LCore.nz ψ _ (hP5u h5)) hz.1).resolve_left h5))
    · by_cases h5 : 5 ∣ aQ
      · exact Or.inl h5
      · exact Or.inr (Or.inl ((cc_zero (Erdos634.GA2LCore.nz ψ _ (hQ5u h5)) hz.2).resolve_left h5))
  · -- coincidence mod 3^j
    have E1 : (if 5 ∣ aP then (0 : ℂ) else eP * ψ (aP : ZMod (5 ^ 1))) +
        (if 5 ∣ aQ then (0 : ℂ) else eQ * ψ (aQ : ZMod (5 ^ 1))) = 0 := by
      rcases D1 with h | h
      · rw [h.1, h.2]; ring
      · exact h.2
    have E2 : (if 5 ∣ aP then (0 : ℂ) else eP * ψ⁻¹ (aP : ZMod (5 ^ 1))) +
        (if 5 ∣ aQ then (0 : ℂ) else eQ * ψ⁻¹ (aQ : ZMod (5 ^ 1))) = 0 := by
      rcases D2 with h | h
      · rw [h.1, h.2]; ring
      · exact h.2
    by_cases hP5 : 5 ∣ aP
    · rw [if_pos hP5, zero_add] at E1
      refine ⟨Or.inl hP5, Or.inr (Or.inl ?_)⟩
      by_cases hQ5 : 5 ∣ aQ
      · exact absurd hQ5 (fun h => by omega)
      · exact (cc_zero (Erdos634.GA2LCore.nz ψ _ (hQ5u hQ5)) E1).resolve_left hQ5
    by_cases hQ5 : 5 ∣ aQ
    · rw [if_pos hQ5, add_zero] at E1
      exact ⟨Or.inr (Or.inl ((cc_zero (Erdos634.GA2LCore.nz ψ _ (hP5u hP5)) E1).resolve_left hP5)), Or.inl hQ5⟩
    rw [if_neg hP5, if_neg hQ5] at E1 E2
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv'] at E2
    have hxP : ∀ y : ZMod (5 ^ 1), (aP : ZMod (5 ^ 1)) = y → ((aP : ℕ) : ZMod (5 ^ 1)) = y := fun y h => h
    rcases Erdos634.GA2UA.five_tri ψ hψo _ _ (hP5u hP5) (hQ5u hQ5) eP eQ E1 E2 with
      ⟨h1, h2⟩ | ⟨hxy, hsum'⟩ | ⟨hxy, hee⟩
    · exact ⟨Or.inr (Or.inl h1), Or.inr (Or.inl h2)⟩
    · rcases hW with hW1 | hW2
      · exact (arith_three j (by omega) aP aQ aS hP3 hS3 hsum hW1).elim
      · -- the Legendre step
        obtain ⟨ψ2, hψ2p, hψ2e⟩ := Erdos634.GA2UA.exists_psi_even
        have hψ2two := Erdos634.GA2UA.psi_even_two ψ2 hψ2p hψ2e
        obtain ⟨η0, hη0p, hη0o⟩ := Erdos634.GA2UB.exists_odd_prim j (by omega)
        have hη02 := Erdos634.GA2UB.prim_two_ne_neg_one j hj η0 hη0p
        have hodd2 : ψ2 (-1) * η0 (-1) = -1 := by rw [hψ2e, hη0o]; norm_num
        have h1 := Erdos634.GA2UF.topA_eqn j (by omega) aP aQ aS eP eQ eS hPo hQo hP3 hQ3 hS3 hS5 H ψ2 hψ2p η0 hη0p
          hodd2
        have hF : 1 - (ψ2 (2 : ZMod (5 ^ 1)))⁻¹ * (η0 (2 : ZMod (3 ^ j)))⁻¹ ≠ 0 := by
          rw [hψ2two]
          intro h0
          apply hη02
          have h' : (η0 (2 : ZMod (3 ^ j)))⁻¹ = -1 := by
            have : (-1 : ℂ)⁻¹ = -1 := by norm_num
            rw [this] at h0
            linear_combination h0
          calc η0 (2 : ZMod (3 ^ j)) = ((η0 (2 : ZMod (3 ^ j)))⁻¹)⁻¹ := (inv_inv _).symm
            _ = (-1 : ℂ)⁻¹ := by rw [h']
            _ = -1 := by norm_num
        have h1' := (mul_eq_zero.1 h1).resolve_right hF
        rw [if_neg hP5, if_neg hQ5, hxy, hW2] at h1'
        have hneg : η0 (-(aP : ZMod (3 ^ j))) = - η0 (aP : ZMod (3 ^ j)) := by
          rw [show -(aP : ZMod (3 ^ j)) = (-1) * (aP : ZMod (3 ^ j)) by ring, map_mul, hη0o]; ring
        rw [hneg] at h1'
        have hne : ψ2 (aP : ZMod (5 ^ 1)) * η0 (aP : ZMod (3 ^ j)) ≠ 0 :=
          mul_ne_zero (Erdos634.GA2LCore.nz ψ2 _ (hP5u hP5)) (Erdos634.GA2LCore.nz η0 _ hPu)
        have h3 : (eP - eQ) * (ψ2 (aP : ZMod (5 ^ 1)) * η0 (aP : ZMod (3 ^ j))) = 0 := by
          linear_combination h1'
        have hee : eP = eQ := by
          have := (mul_eq_zero.1 h3).resolve_right hne
          linear_combination this
        have hePz : eP = 0 := by linear_combination (1 / 2 : ℂ) * (hsum' + hee)
        have heQz : eQ = 0 := by linear_combination (1 / 2 : ℂ) * (hsum' - hee)
        exact ⟨Or.inr (Or.inl hePz), Or.inr (Or.inl heQz)⟩
    · rcases hW with hW1 | hW2
      · exact (arith_three j (by omega) aP aQ aS hP3 hS3 hsum hW1).elim
      · refine (arith_minus j aP aQ aS hPo hQo hS0 hsum ?_ ?_).elim
        · have : ((aP + aQ : ℕ) : ZMod (3 ^ j)) = 0 := by
            push_cast; linear_combination hW2
          exact (ZMod.natCast_eq_zero_iff _ _).1 this
        · have : ((aP + aQ : ℕ) : ZMod (5 ^ 1)) = 0 := by
            push_cast; linear_combination hxy
          have := (ZMod.natCast_eq_zero_iff _ _).1 this
          simpa using this

end Erdos634.GA2UG

#print axioms Erdos634.GA2UG.arith_three
#print axioms Erdos634.GA2UG.arith_minus
#print axioms Erdos634.GA2UG.topA
