/-
GA2S, atom Q: Prop K-c (i = 1), T = S the EVEN entry divisible by 3 (not by 5), r >= 2, j >= 2.

For primitive eta3 mod 3^j the entry S is invisible; P, Q (3 !| P, Q) give tokens a([2u]-kappa[u]) + b([2v]-kappa[v]) (c = 0), and the 5-adic
pattern step (`GA2SO.five_pattern`) gives per eta:  (a = b = 0) or (v = u, b = -a) or (v = -u, b = -eps a).  The 3-adic constancy over
primitive characters (`GA2SJ.const_prim3` via `GA2SK.const_ratio3`, j >= 2) turns this into  aP = aQ, eP + eQ = 0  or  eP = 0.
  `kcS_top` : eP = 0 or (aP = aQ and eP + eQ = 0).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SP
import Erdos634.Draft.GA2SE

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SQ

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PG
open Erdos634.GA2SD Erdos634.GA2SJ Erdos634.GA2SK Erdos634.GA2SO Erdos634.GA2SP
open Erdos634.GA2SL (unit3)
open Erdos634.GA2SE (m0_odd_r)

theorem kcS_top (r j : ℕ) (hr : 2 ≤ r) (hj : 2 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : aP % 2 = 1) (hQo : aQ % 2 = 1) (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 2 * (5 ^ r * 3 ^ j))
    (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hS3 : 3 ∣ aS) (hS5 : ¬ 5 ∣ aS) (hP5 : ¬ 5 ∣ aP)
    (H : H1 r j aP aQ aS eP eQ eS) :
    eP = 0 ∨ (aP = aQ ∧ eP + eQ = 0) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h5N : 5 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
  have hm0 := m0_odd_r r j
  haveI : Fact (1 < 5 ^ r) := ⟨by
    calc 1 < 5 ^ 1 := by norm_num
      _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)⟩
  obtain ⟨η0, h0⟩ := exists_prim3 j (by omega)
  have hη0P : η0 (aP : ZMod (3 ^ j)) ≠ 0 := Erdos634.GA2LCore.nz η0 _ (unit3 j aP hP3)
  have hPu : IsUnit (aP : ZMod (5 ^ r)) := unit5r r aP hP5
  obtain ⟨u, hu2⟩ := exists_half r (aP : ZMod (5 ^ r))
  have huu : IsUnit u := half_unit' r hPu hu2
  -- for every primitive eta: the data
  have hε : ∀ η : DirichletCharacter ℂ (3 ^ j), (-η (-1)) = 1 ∨ (-η (-1)) = -1 := by
    intro η
    rcases DirichletCharacter.even_or_odd η with h | h <;> rw [h] <;> simp
  have hκ : ∀ η : DirichletCharacter ℂ (3 ^ j), (η (2 : ZMod (3 ^ j)))⁻¹ ≠ 0 := by
    intro η
    apply inv_ne_zero
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (3 ^ j)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  have hbasic : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
      ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = -η (-1) →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aP +
        eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aQ = 0 := by
    intro η hη ψ hψ h1
    have hηη : η (-1) * η (-1) = 1 := by
      rcases DirichletCharacter.even_or_odd η with h | h <;> rw [h] <;> norm_num
    have hodd : ψ (-1) * η (-1) = -1 := by rw [h1]; linear_combination -hηη
    have hb := H ψ hψ η hodd
    rw [Erdos634.GA2PJ.bracket_i1_three r j (by omega) ψ hψ η hη aS hS5 hS3, mul_zero, add_zero] at hb
    exact hb
  by_cases hQ5 : 5 ∣ aQ
  · -- Q absent: P alone
    left
    have key := five_pattern r hr (u := u) (v := u) huu huu (κ := (η0 (2 : ZMod (3 ^ j)))⁻¹)
      (ε := -η0 (-1)) (a := eP * η0 (aP : ZMod (3 ^ j))) (b := 0) (c := 0) (hκ η0) (hε η0)
      (Or.inl rfl) (Or.inr (Or.inl rfl))
      (by
        intro ψ hψ h1
        have hb := hbasic η0 h0 ψ hψ h1
        rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 1 j) hψ _ aQ hQ5, mul_zero, add_zero,
          Erdos634.GA2PJ.bracket_i1_odd r j (by omega) ψ hψ η0 h0 aP hP5 (unit_cop1 j aP hPo hP3)] at hb
        have := odd_expr r ψ hu2 ((η0 (2 : ZMod (3 ^ j)))⁻¹)
        linear_combination hb - (eP * η0 (aP : ZMod (3 ^ j))) * this)
    have := concl_bc0 (hε η0) key
    exact (mul_eq_zero.1 this).resolve_right hη0P
  · obtain ⟨v, hv2⟩ := exists_half r (aQ : ZMod (5 ^ r))
    have hvu : IsUnit v := half_unit' r (unit5r r aQ hQ5) hv2
    have hη0Q : η0 (aQ : ZMod (3 ^ j)) ≠ 0 := Erdos634.GA2LCore.nz η0 _ (unit3 j aQ hQ3)
    have hC : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
        Erdos634.GA2QP.Concl u v (-η (-1)) (eP * η (aP : ZMod (3 ^ j))) (eQ * η (aQ : ZMod (3 ^ j))) 0 := by
      intro η hη
      refine five_pattern r hr huu hvu (hκ η) (hε η) (Or.inl rfl) (Or.inr (Or.inr rfl)) ?_
      intro ψ hψ h1
      have hb := hbasic η hη ψ hψ h1
      rw [Erdos634.GA2PJ.bracket_i1_odd r j (by omega) ψ hψ η hη aP hP5 (unit_cop1 j aP hPo hP3),
        Erdos634.GA2PJ.bracket_i1_odd r j (by omega) ψ hψ η hη aQ hQ5 (unit_cop1 j aQ hQo hQ3)] at hb
      have h1' := odd_expr r ψ hu2 ((η (2 : ZMod (3 ^ j)))⁻¹)
      have h2' := odd_expr r ψ hv2 ((η (2 : ZMod (3 ^ j)))⁻¹)
      linear_combination hb - (eP * η (aP : ZMod (3 ^ j))) * h1' - (eQ * η (aQ : ZMod (3 ^ j))) * h2'
    have h2u : (2 : ZMod (5 ^ r)) ≠ 0 := (half_unit r).ne_zero
    have hnn : ¬ (u = -u) := by
      intro h
      have : (2 : ZMod (5 ^ r)) * u = 0 := by linear_combination h
      exact huu.ne_zero ((half_unit r).mul_right_eq_zero.1 this)
    by_cases hvu1 : v = u
    · -- v = u
      have hEq : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
          eQ * η (aQ : ZMod (3 ^ j)) = -(eP * η (aP : ZMod (3 ^ j))) := by
        intro η hη
        rcases hC η hη with ⟨h1, h2, _⟩ | ⟨_, h2, _⟩ | ⟨h1, _, _⟩
        · rw [h1, h2]; ring
        · exact h2
        · exact absurd (hvu1.symm.trans h1) hnn
      by_cases heQ : eQ = 0
      · left
        have := hEq η0 h0
        rw [heQ, zero_mul] at this
        have h3 : eP * η0 (aP : ZMod (3 ^ j)) = 0 := by linear_combination this
        exact (mul_eq_zero.1 h3).resolve_right hη0P
      · have hc : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
            η ((unit3 j aQ hQ3).unit : ZMod (3 ^ j)) = (-eP / eQ) * η ((unit3 j aP hP3).unit : ZMod (3 ^ j)) := by
          intro η hη
          have := hEq η hη
          rw [IsUnit.unit_spec, IsUnit.unit_spec]
          field_simp
          linear_combination this
        have hvu3 := const_ratio3 j hj _ _ _ hc
        have hv3 : (aQ : ZMod (3 ^ j)) = (aP : ZMod (3 ^ j)) := by
          have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) hvu3
          simpa using this
        have m3 : aQ ≡ aP [MOD 3 ^ j] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hv3
        have h5 : (aQ : ZMod (5 ^ r)) = (aP : ZMod (5 ^ r)) := by rw [← hu2, ← hv2, hvu1]
        have m5 : aQ ≡ aP [MOD 5 ^ r] := (ZMod.natCast_eq_natCast_iff _ _ _).1 h5
        have mm : aQ ≡ aP [MOD 5 ^ r * 3 ^ j] :=
          (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow _ _ (by norm_num))).1 ⟨m5, m3⟩
        have hsh := Erdos634.GA2PE.shape_plus (5 ^ r * 3 ^ j) aQ aP hm0 hQo hPo hQ0 hP0
          (by omega) (by omega) mm
        have hPQ : aP = aQ := by omega
        right
        refine ⟨hPQ, ?_⟩
        have := hEq η0 h0
        rw [← hPQ] at this
        have : (eP + eQ) * η0 (aP : ZMod (3 ^ j)) = 0 := by linear_combination this
        exact (mul_eq_zero.1 this).resolve_right hη0P
    · by_cases hvu2 : v = -u
      · -- v = -u
        have hEq : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
            eQ * η (aQ : ZMod (3 ^ j)) = η (-1) * (eP * η (aP : ZMod (3 ^ j))) := by
          intro η hη
          rcases hC η hη with ⟨h1, h2, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
          · rw [h1, h2]; ring
          · exact absurd h1 hvu1
          · linear_combination h3
        by_cases heQ : eQ = 0
        · left
          have := hEq η0 h0
          rw [heQ, zero_mul] at this
          have hηm : η0 (-1) ≠ 0 := by
            rcases DirichletCharacter.even_or_odd η0 with h | h <;> rw [h] <;> norm_num
          have h3 : η0 (-1) * (eP * η0 (aP : ZMod (3 ^ j))) = 0 := by linear_combination -this
          have h4 := (mul_eq_zero.1 h3).resolve_left hηm
          exact (mul_eq_zero.1 h4).resolve_right hη0P
        · exfalso
          have hc : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
              η (-(unit3 j aQ hQ3).unit : (ZMod (3 ^ j))ˣ) = (eP / eQ) * η ((unit3 j aP hP3).unit : ZMod (3 ^ j)) := by
            intro η hη
            have := hEq η hη
            rw [Units.val_neg, IsUnit.unit_spec, IsUnit.unit_spec]
            have hn : (-(aQ : ZMod (3 ^ j))) = (-1) * (aQ : ZMod (3 ^ j)) := by ring
            have hηη : η (-1) * η (-1) = 1 := by
              rcases DirichletCharacter.even_or_odd η with h | h <;> rw [h] <;> norm_num
            rw [hn, map_mul, div_mul_eq_mul_div, eq_div_iff heQ]
            linear_combination η (-1) * this + eP * η (aP : ZMod (3 ^ j)) * hηη
          have hvu3 := const_ratio3 j hj _ _ _ hc
          have hv3 : -(aQ : ZMod (3 ^ j)) = (aP : ZMod (3 ^ j)) := by
            have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) hvu3
            simpa using this
          have m3 : 3 ^ j ∣ aP + aQ := by
            have : (aP : ZMod (3 ^ j)) = -(aQ : ZMod (3 ^ j)) := hv3.symm
            exact (natcast_neg_iff (3 ^ j) aP aQ).1 this
          have m5 : 5 ^ r ∣ aP + aQ := by
            have h5 : (aQ : ZMod (5 ^ r)) = -(aP : ZMod (5 ^ r)) := by
              rw [← hu2, ← hv2, hvu2]; ring
            have := (natcast_neg_iff (5 ^ r) aQ aP).1 h5
            rwa [add_comm] at this
          have mm : 5 ^ r * 3 ^ j ∣ aP + aQ :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num)) m5 m3
          have h2 : 2 ∣ aP + aQ := by omega
          have hcop2 : Nat.Coprime 2 (5 ^ r * 3 ^ j) :=
            Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num)) (Nat.Coprime.pow_right _ (by norm_num))
          have mm2 : 2 * (5 ^ r * 3 ^ j) ∣ aP + aQ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 h2 mm
          have := Nat.le_of_dvd (by omega) mm2
          omega
      · left
        rcases hC η0 h0 with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _⟩
        · exact (mul_eq_zero.1 h1).resolve_right hη0P
        · exact absurd h1 hvu1
        · exact absurd h1 hvu2

end Erdos634.GA2SQ

#print axioms Erdos634.GA2SQ.kcS_top
