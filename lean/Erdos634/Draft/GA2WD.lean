/-
GA2W, part D: `KcJ1Lab` (Prop K-c, T = S the even entry divisible by 3 at j = 1, n = 6 * 5^r, r >= 2) -- GA2V_NOTES section 4.
  Route: Leg first (S invisible; the two odd entries give the pair pattern `GA2SO.five_pattern`, kappa = -1, eps = 1, c = 0);
  the surviving configuration (P = Q mod 5^r) goes to the trivial character mod 3, where Lemma N (+-support version,
  `GA2WA.lemmaN_lin`) on the five tokens {6u, 3u, 2u, u, -2u} (|+-support| = 8 < 10) gives eP + eQ = 0.
  `kc_eta1`, `kc_good`, `kc_S`, `kcJ1_lab`.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2WC

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2WD

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.GA2SP (H1 H1_swap half_unit' exists_half odd_expr unit_cop1)
open Erdos634.GA2PG (Good pair_zero)
open Erdos634.GA2SD (unit5r zmod5r_of_dvd)
open Erdos634.GA2SL (unit3)
open Erdos634.GA2SO (five_pattern concl_bc0 half_unit)
open Erdos634.GA2WB
open Erdos634.GA2WA (lemmaN_lin)

/-- the trivial-character stage in the surviving configuration (P = Q mod 5^r): eP + eQ = 0. -/
theorem kc_eta1 (r : ℕ) (hr : 2 ≤ r) (aP aQ s : ℕ) (eP eQ eS : ℂ)
    (hsum : aP + aQ + 6 * s = 2 * (5 ^ r * 3 ^ 1)) (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hP2 : aP % 2 = 1) (hQ2 : aQ % 2 = 1) (hS5 : ¬ 5 ∣ 6 * s)
    (hPQ : (aQ : ZMod (5 ^ r)) = (aP : ZMod (5 ^ r)))
    (H : H1 r 1 aP aQ (6 * s) eP eQ eS) : eP + eQ = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h6u : IsUnit (6 : ZMod (5 ^ r)) := by
    have := unit5r r 6 (by omega)
    simpa using this
  have h2u : IsUnit (2 : ZMod (5 ^ r)) := half_unit r
  have h3u : IsUnit (3 : ZMod (5 ^ r)) := by
    have := unit5r r 3 (by omega)
    simpa using this
  obtain ⟨w, hw⟩ := h6u.exists_right_inv
  set u : ZMod (5 ^ r) := w * (aP : ZMod (5 ^ r)) with hu
  have hu6 : 6 * u = (aP : ZMod (5 ^ r)) := by rw [hu, ← mul_assoc, hw, one_mul]
  have huu : IsUnit u := by
    have : IsUnit (aP : ZMod (5 ^ r)) := unit5r r aP hP5
    rw [← hu6] at this
    exact isUnit_of_mul_isUnit_right this
  have hsumZ : (aP : ZMod (5 ^ r)) + aQ + (6 * s : ℕ) = 0 := by
    have : ((aP + aQ + 6 * s : ℕ) : ZMod (5 ^ r)) = 0 := by
      rw [hsum]; exact zmod5r_of_dvd r _ (Dvd.dvd.mul_left (dvd_mul_right _ _) 2)
    push_cast at this ⊢
    exact this
  have hs : (s : ZMod (5 ^ r)) = -2 * u := by
    have h1 : (6 : ZMod (5 ^ r)) * ((s : ZMod (5 ^ r)) + 2 * u) = 0 := by
      push_cast at hsumZ
      linear_combination hsumZ + 2 * hu6 - hPQ
    have h3 := (IsUnit.mul_right_eq_zero h6u).1 h1
    linear_combination h3
  have hbase : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = -1 →
      (eP + eQ) * ψ (aP : ZMod (5 ^ r)) + (-(eP + eQ)) * (ψ 3 * ψ u) + (-(eP + eQ)) * (ψ 2 * ψ u)
        + (eP + eQ) * ψ u + (2 * eS) * ψ (s : ZMod (5 ^ r)) = 0 := by
    intro ψ hψ h1
    have hodd : ψ (-1) * (1 : DirichletCharacter ℂ (3 ^ 1)) (-1) = -1 := by
      rw [h1, MulChar.one_apply (isUnit_one.neg)]; norm_num
    have hb := H ψ hψ 1 hodd
    rw [br_c_unit r ψ hψ aP hP5 hP3 hP2, br_c_unit r ψ hψ aQ hQ5 hQ3 hQ2, br_c_six r ψ hψ s hS5, hPQ] at hb
    have h2ne : ψ (2 : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ h2u
    have h3ne : ψ (3 : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ h3u
    have hPψ : ψ (aP : ZMod (5 ^ r)) = ψ 2 * ψ 3 * ψ u := by
      rw [← hu6, show (6 : ZMod (5 ^ r)) * u = 2 * 3 * u by norm_num, map_mul, map_mul]
    rw [hPψ] at hb ⊢
    have hid : ψ 2 * ψ 3 * ψ u * ((1 - (ψ 2)⁻¹) * (1 - (ψ 3)⁻¹)) =
        ψ 2 * ψ 3 * ψ u - ψ 3 * ψ u - ψ 2 * ψ u + ψ u := by
      field_simp
      ring
    linear_combination hb - (eP + eQ) * hid
  set P : Finset ℤ := {6, -6, 3, -3, 2, -2, 1, -1} with hP
  have key := lemmaN_lin r hr huu (![6, 3, 2, 1, -2] : Fin 5 → ℤ)
    (![eP + eQ, -(eP + eQ), -(eP + eQ), eP + eQ, 2 * eS] : Fin 5 → ℂ)
    (ε := -1) (Or.inr rfl) P
    (by intro i; fin_cases i <;> simp [hP])
    (by simp [hP])
    (by intro n hn; simp only [hP, Finset.mem_insert, Finset.mem_singleton] at hn; omega)
    (by intro n hn; simp only [hP, Finset.mem_insert, Finset.mem_singleton] at hn; omega)
    (by
      intro ψ hψ h1
      have e6 : ((6 : ℤ) : ZMod (5 ^ r)) * u = (aP : ZMod (5 ^ r)) := by push_cast; exact hu6
      have e3 : ((3 : ℤ) : ZMod (5 ^ r)) * u = 3 * u := by push_cast; ring
      have e2 : ((2 : ℤ) : ZMod (5 ^ r)) * u = 2 * u := by push_cast; ring
      have e1 : ((1 : ℤ) : ZMod (5 ^ r)) * u = u := by push_cast; ring
      have es : ((-2 : ℤ) : ZMod (5 ^ r)) * u = (s : ZMod (5 ^ r)) := by push_cast; rw [hs]
      simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, e6, e3, e2, e1, es]
      rw [map_mul ψ 3 u, map_mul ψ 2 u]
      have := hbase ψ hψ h1
      linear_combination this)
    6 (by simp [hP])
  simp [Fin.sum_univ_five] at key
  exact key

theorem kc_good (r : ℕ) (hr : 2 ≤ r) (aP aQ s : ℕ) (eP eQ eS : ℂ)
    (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < 6 * s)
    (hsum : aP + aQ + 6 * s = 2 * (5 ^ r * 3 ^ 1)) (hP2 : aP % 2 = 1) (hQ2 : aQ % 2 = 1)
    (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hS5 : ¬ 5 ∣ 6 * s)
    (H : H1 r 1 aP aQ (6 * s) eP eQ eS) : Good aP aQ eP eQ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hP5 : 5 ∣ aP
  · exact Or.inl hP5
  right
  have h5N : 5 ∣ 5 ^ r * 3 ^ 1 := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
  obtain ⟨η, hη⟩ := Erdos634.GA2SJ.exists_prim3 1 le_rfl
  have hη1 : η (-1) = -1 := eta3_neg_one η hη
  have hηη : η (-1) * η (-1) = 1 := by rw [hη1]; norm_num
  have hε : (-η (-1)) = 1 ∨ (-η (-1)) = -1 := by rw [hη1]; left; norm_num
  have hκ : (η (2 : ZMod (3 ^ 1)))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (3 ^ 1)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  have hηP : η (aP : ZMod (3 ^ 1)) ≠ 0 := Erdos634.GA2LCore.nz η _ (unit3 1 aP hP3)
  have hηQ : η (aQ : ZMod (3 ^ 1)) ≠ 0 := Erdos634.GA2LCore.nz η _ (unit3 1 aQ hQ3)
  have hbasic : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = -η (-1) →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aP +
        eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aQ = 0 := by
    intro ψ hψ h1
    have hodd : ψ (-1) * η (-1) = -1 := by rw [h1]; linear_combination -hηη
    have hb := H ψ hψ η hodd
    rw [Erdos634.GA2PJ.bracket_i1_three r 1 le_rfl ψ hψ η hη (6 * s) hS5 ⟨2 * s, by ring⟩, mul_zero,
      add_zero] at hb
    exact hb
  have hPu : IsUnit (aP : ZMod (5 ^ r)) := unit5r r aP hP5
  obtain ⟨u, hu2⟩ := exists_half r (aP : ZMod (5 ^ r))
  have huu : IsUnit u := half_unit' r hPu hu2
  by_cases hQ5 : 5 ∣ aQ
  · left
    have key := five_pattern r hr (u := u) (v := u) huu huu (κ := (η (2 : ZMod (3 ^ 1)))⁻¹)
      (ε := -η (-1)) (a := eP * η (aP : ZMod (3 ^ 1))) (b := 0) (c := 0) hκ hε
      (Or.inl rfl) (Or.inr (Or.inr rfl))
      (by
        intro ψ hψ h1
        have hb := hbasic ψ hψ h1
        rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := r) (by omega) (Erdos634.GA2PA.not5_dvd' 1 1) hψ _
          aQ hQ5, mul_zero, add_zero,
          Erdos634.GA2PJ.bracket_i1_odd r 1 le_rfl ψ hψ η hη aP hP5 (unit_cop1 1 aP hP2 hP3)] at hb
        have := odd_expr r ψ hu2 ((η (2 : ZMod (3 ^ 1)))⁻¹)
        linear_combination hb - (eP * η (aP : ZMod (3 ^ 1))) * this)
    have hb0 := concl_bc0 hε key
    exact (mul_eq_zero.1 hb0).resolve_right hηP
  · obtain ⟨v, hv2⟩ := exists_half r (aQ : ZMod (5 ^ r))
    have hvu : IsUnit v := half_unit' r (unit5r r aQ hQ5) hv2
    have key := five_pattern r hr (u := u) (v := v) huu hvu (κ := (η (2 : ZMod (3 ^ 1)))⁻¹)
      (ε := -η (-1)) (a := eP * η (aP : ZMod (3 ^ 1))) (b := eQ * η (aQ : ZMod (3 ^ 1))) (c := 0) hκ hε
      (Or.inl rfl) (Or.inr (Or.inr rfl))
      (by
        intro ψ hψ h1
        have hb := hbasic ψ hψ h1
        rw [Erdos634.GA2PJ.bracket_i1_odd r 1 le_rfl ψ hψ η hη aP hP5 (unit_cop1 1 aP hP2 hP3),
          Erdos634.GA2PJ.bracket_i1_odd r 1 le_rfl ψ hψ η hη aQ hQ5 (unit_cop1 1 aQ hQ2 hQ3)] at hb
        have e1 := odd_expr r ψ hu2 ((η (2 : ZMod (3 ^ 1)))⁻¹)
        have e2 := odd_expr r ψ hv2 ((η (2 : ZMod (3 ^ 1)))⁻¹)
        linear_combination hb - (eP * η (aP : ZMod (3 ^ 1))) * e1 - (eQ * η (aQ : ZMod (3 ^ 1))) * e2)
    rcases key with ⟨ha, _, _⟩ | ⟨hvu, hba, _⟩ | ⟨hvu, _, _⟩
    · left
      exact (mul_eq_zero.1 ha).resolve_right hηP
    · -- P = Q mod 5^r
      have hPQ : (aQ : ZMod (5 ^ r)) = (aP : ZMod (5 ^ r)) := by rw [← hv2, ← hu2, hvu]
      have hA : eP + eQ = 0 :=
        kc_eta1 r hr aP aQ s eP eQ eS hsum hP5 hQ5 hP3 hQ3 hP2 hQ2 hS5 hPQ H
      have hEQ : eQ = -eP := by linear_combination hA
      have hdiff : eP * (η (aP : ZMod (3 ^ 1)) - η (aQ : ZMod (3 ^ 1))) = 0 := by
        rw [hEQ] at hba
        linear_combination hba
      by_cases hep : eP = 0
      · exact Or.inl hep
      · right
        have hηeq : η (aP : ZMod (3 ^ 1)) = η (aQ : ZMod (3 ^ 1)) := by
          have := (mul_eq_zero.1 hdiff).resolve_left hep
          linear_combination this
        rcases mod3_cases aP aQ hP3 hQ3 with hm | hm
        · -- aQ = aP mod 3
          have m3 : aQ ≡ aP [MOD 3 ^ 1] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hm
          have m5 : aQ ≡ aP [MOD 5 ^ r] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hPQ
          have m2 : aQ ≡ aP [MOD 2] := by unfold Nat.ModEq; omega
          have mm : aQ ≡ aP [MOD 5 ^ r * 3 ^ 1] :=
            (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow _ _ (by norm_num))).1 ⟨m5, m3⟩
          have mm2 : aQ ≡ aP [MOD 2 * (5 ^ r * 3 ^ 1)] :=
            (Nat.modEq_and_modEq_iff_modEq_mul
              (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
                (Nat.Coprime.pow_right _ (by norm_num)))).1 ⟨m2, mm⟩
          have hlt : aP < 2 * (5 ^ r * 3 ^ 1) := by omega
          have hlt' : aQ < 2 * (5 ^ r * 3 ^ 1) := by omega
          have hQP : aQ = aP := by
            have := mm2
            rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at this
            exact this
          exact ⟨hQP.symm, by rw [hEQ]; ring⟩
        · exfalso
          have hηneg : η (aQ : ZMod (3 ^ 1)) = - η (aP : ZMod (3 ^ 1)) := by
            rw [hm, show -(aP : ZMod (3 ^ 1)) = (-1) * (aP : ZMod (3 ^ 1)) by ring, map_mul, hη1]; ring
          apply hηP
          rw [hηneg] at hηeq
          linear_combination hηeq / 2
    · exfalso
      have hQ : (aQ : ZMod (5 ^ r)) = -(aP : ZMod (5 ^ r)) := by
        rw [← hv2, hvu, ← hu2]; ring
      have h' := (Erdos634.GA2PD.natcast_neg_iff (5 ^ r) aQ aP).1 hQ
      have h5 : 5 ∣ aQ + aP := (dvd_pow_self 5 (by omega)).trans h'
      omega

theorem kc_S (r : ℕ) (hr : 2 ≤ r) (aP aQ s : ℕ) (eP eQ eS : ℂ) (hS5 : ¬ 5 ∣ 6 * s)
    (H : H1 r 1 aP aQ (6 * s) eP eQ eS) (GP : Good aP aQ eP eQ) (GQ : Good aQ aP eQ eP) : eS = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, hψo⟩ := exists_odd_psi r (by omega)
  have hodd : ψ (-1) * (1 : DirichletCharacter ℂ (3 ^ 1)) (-1) = -1 := by
    rw [hψo, MulChar.one_apply (isUnit_one.neg)]; norm_num
  have hbk := H ψ hψ 1 hodd
  set B : ℕ → ℂ := fun x => bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1))
    (1 : DirichletCharacter ℂ (3 ^ 1)))) x with hB
  have hB5 : ∀ x, 5 ∣ x → B x = 0 := fun x hx =>
    Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := r) (by omega) (Erdos634.GA2PA.not5_dvd' 1 1) hψ _ x hx
  have hz := pair_zero B hB5 aP aQ eP eQ GP GQ
  have hBne : B (6 * s) ≠ 0 := by
    show bracket _ (6 * s) ≠ 0
    rw [br_c_six r ψ hψ s hS5]
    exact mul_ne_zero two_ne_zero (Erdos634.GA2LCore.nz ψ _ (unit5r r s (by omega)))
  have : eP * B aP + eQ * B aQ + eS * B (6 * s) = 0 := hbk
  rw [hz, zero_add] at this
  exact (mul_eq_zero.1 this).resolve_right hBne

theorem kcJ1_lab : Erdos634.GA2SY.KcJ1Lab := by
  intro r aP aQ aS eP eQ eS hr hP2 hQ2 hS2 hP0 hQ0 hS0 hsum hgcd hS3 hS5 H
  have h3N : 3 ∣ 2 * (5 ^ r * 3 ^ 1) := Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _) 2
  have hP3 : ¬ 3 ∣ aP := by
    intro h
    have hQ' : 3 ∣ aQ := by omega
    have := Nat.dvd_gcd (Nat.dvd_gcd h hQ') hS3
    rw [hgcd] at this
    omega
  have hQ3 : ¬ 3 ∣ aQ := by
    intro h
    have hP' : 3 ∣ aP := by omega
    exact hP3 hP'
  have h6 : 6 ∣ aS := by omega
  obtain ⟨s, rfl⟩ := h6
  have GP : Good aP aQ eP eQ := kc_good r hr aP aQ s eP eQ eS hP0 hQ0 hS0 hsum hP2 hQ2 hP3 hQ3 hS5 H
  have GQ : Good aQ aP eQ eP :=
    kc_good r hr aQ aP s eQ eP eS hQ0 hP0 hS0 (by omega) hQ2 hP2 hQ3 hP3 hS5 (H1_swap H)
  have heS := kc_S r hr aP aQ s eP eQ eS hS5 H GP GQ
  intro x hx
  have hTX : 6 * s ≠ aP := by omega
  have hTY : 6 * s ≠ aQ := by omega
  by_cases hTx : 6 * s = x
  · rw [if_neg (fun h => hTX (by rw [hTx, h])), if_neg (fun h => hTY (by rw [hTx, h])), if_pos hTx, heS]
    ring
  · rw [if_neg hTx, add_zero]
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

end Erdos634.GA2WD

#print axioms Erdos634.GA2WD.kc_eta1
#print axioms Erdos634.GA2WD.kc_good
#print axioms Erdos634.GA2WD.kc_S
#print axioms Erdos634.GA2WD.kcJ1_lab
