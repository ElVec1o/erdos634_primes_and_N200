/-
`KbJ1Lab` (Prop K-b, entry T = 3t at j = 1, n = 3 * 5^r, r >= 2).
  Route: quadratic character Leg mod 3 FIRST (it does not see T; the two visible tokens are a 5-adic pair step `five_eval2`),
  then the trivial character mod 3 for the single surviving configuration (X = Y mod 5^r, Leg X = -Leg Y), where
  Lemma N (+-support version, `GA2WA.lemmaN_lin`) on the three tokens {3u, u, -2u} kills the weight; the hidden entry is
  killed by `GA2SM.kb_T` (valid at j = 1).
  `kbE`, `kb_eta1`, `kb_good`, `kbJ1_lab`.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2WB
import Erdos634.Draft.GA2SY

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2WC

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.GA2SL (H0 H0_swap unit3)
open Erdos634.GA2PG (Good pair_zero)
open Erdos634.GA2SD (unit5r zmod5r_of_dvd)
open Erdos634.GA2SK (five_eval2 bracket_hidden0)
open Erdos634.GA2WB
open Erdos634.GA2WA (lemmaN_lin)

/-- the Leg-stage equation (copy of the `E` of `GA2SL.kb_top`, for j >= 1) -/
theorem kbE (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aT : ℕ) (eX eY eT : ℂ)
    (hX3 : ¬ 3 ∣ aX) (hY3 : ¬ 3 ∣ aY) (hT3 : 3 ∣ aT) (hT5 : ¬ 5 ∣ aT) (hX5 : ¬ 5 ∣ aX)
    (H : H0 r j aX aY aT eX eY eT) (η : DirichletCharacter ℂ (3 ^ j)) (hη : η.IsPrimitive) :
    eX * η (aX : ZMod (3 ^ j)) + (if 5 ∣ aY then 0 else eY * η (aY : ZMod (3 ^ j)) *
      ((if (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r)) then 1 else 0) +
        (-η (-1)) * (if (aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) then 1 else 0))) = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hX3' : Nat.Coprime 3 aX := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hX3
  have hY3' : Nat.Coprime 3 aY := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hY3
  have hε : (-η (-1)) = 1 ∨ (-η (-1)) = -1 := by
    rcases DirichletCharacter.even_or_odd η with h | h <;> rw [h] <;> simp
  have := five_eval2 r hr aX aY (eX * η (aX : ZMod (3 ^ j))) (eY * η (aY : ZMod (3 ^ j))) (-η (-1)) hε hX5 (by
    intro ψ hψ h1
    have hηη : η (-1) * η (-1) = 1 := by
      rcases DirichletCharacter.even_or_odd η with h | h <;> rw [h] <;> norm_num
    have hodd : ψ (-1) * η (-1) = -1 := by rw [h1]; linear_combination -hηη
    have hb := H ψ hψ η hodd
    obtain ⟨κ, hκ, hκb⟩ := Erdos634.GA2QK1.bracket_K0 r j (by omega) (by omega) ψ hψ η
    rw [bracket_hidden0 r j (by omega) (by omega) ψ hψ η hη aT hT5 hT3, mul_zero, add_zero,
      hκb aX hX5 hX3'] at hb
    have hmain : κ * (eX * η (aX : ZMod (3 ^ j)) * ψ (aX : ZMod (5 ^ r)) +
        (if 5 ∣ aY then 0 else eY * η (aY : ZMod (3 ^ j)) * ψ (aY : ZMod (5 ^ r)))) = 0 := by
      by_cases h5 : 5 ∣ aY
      · rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := r) (by omega) (Erdos634.GA2PA.not5_dvd' 0 j) hψ _ aY h5,
          mul_zero, add_zero] at hb
        rw [if_pos h5]; linear_combination hb
      · rw [hκb aY h5 hY3'] at hb
        rw [if_neg h5]; linear_combination hb
    exact (mul_eq_zero.1 hmain).resolve_left hκ)
  refine Eq.trans ?_ this
  split_ifs <;> ring

/-- the trivial-character stage in the surviving configuration (X = Y mod 5^r, eY = eX): Lemma N on {3u, u, -2u}. -/
theorem kb_eta1 (r : ℕ) (hr : 2 ≤ r) (aX aY t : ℕ) (eX eY eT : ℂ)
    (hsum : aX + aY + 3 * t = 5 ^ r * 3 ^ 1) (hX5 : ¬ 5 ∣ aX) (hY5 : ¬ 5 ∣ aY)
    (hY3 : ¬ 3 ∣ aY) (hX3 : ¬ 3 ∣ aX) (hT5 : ¬ 5 ∣ 3 * t)
    (hXY : (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r))) (hE : eY = eX)
    (H : H0 r 1 aX aY (3 * t) eX eY eT) : eX = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3u : IsUnit (3 : ZMod (5 ^ r)) := by
    have := unit5r r 3 (by omega)
    simpa using this
  obtain ⟨w, hw⟩ := h3u.exists_right_inv
  set u : ZMod (5 ^ r) := w * (aX : ZMod (5 ^ r)) with hu
  have hu3 : 3 * u = (aX : ZMod (5 ^ r)) := by rw [hu, ← mul_assoc, hw, one_mul]
  have huu : IsUnit u := by
    have : IsUnit (aX : ZMod (5 ^ r)) := unit5r r aX hX5
    rw [← hu3] at this
    exact isUnit_of_mul_isUnit_right this
  have hsumZ : (aX : ZMod (5 ^ r)) + aY + (3 * t : ℕ) = 0 := by
    have : ((aX + aY + 3 * t : ℕ) : ZMod (5 ^ r)) = 0 := by
      rw [hsum]; exact zmod5r_of_dvd r _ (dvd_mul_right _ _)
    push_cast at this ⊢
    exact this
  have hts : (t : ZMod (5 ^ r)) = -2 * u := by
    have h1 : (3 : ZMod (5 ^ r)) * ((t : ZMod (5 ^ r)) + 2 * u) = 0 := by
      push_cast at hsumZ
      linear_combination hsumZ + 2 * hu3 - hXY
    have h3 := (IsUnit.mul_right_eq_zero h3u).1 h1
    linear_combination h3
  have hbase : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = -1 →
      (2 * eX) * ψ (aX : ZMod (5 ^ r)) + (-2 * eX) * ψ u + (2 * eT) * ψ (t : ZMod (5 ^ r)) = 0 := by
    intro ψ hψ h1
    have hodd : ψ (-1) * (1 : DirichletCharacter ℂ (3 ^ 1)) (-1) = -1 := by
      rw [h1, MulChar.one_apply (isUnit_one.neg)]; norm_num
    have hb := H ψ hψ 1 hodd
    rw [br_b_unit r ψ hψ aX hX5 hX3, br_b_unit r ψ hψ aY hY5 hY3, br_b_three r ψ hψ t hT5, hXY, hE] at hb
    have h3ne : ψ (3 : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ h3u
    have hψu : ψ u = (ψ (3 : ZMod (5 ^ r)))⁻¹ * ψ (aX : ZMod (5 ^ r)) := by
      have : ψ (aX : ZMod (5 ^ r)) = ψ 3 * ψ u := by rw [← map_mul, hu3]
      rw [this]; field_simp
    rw [hψu]
    linear_combination hb
  set P : Finset ℤ := {3, -3, 1, -1, -2, 2} with hP
  have key := lemmaN_lin r hr huu (![3, 1, -2] : Fin 3 → ℤ) (![2 * eX, -2 * eX, 2 * eT] : Fin 3 → ℂ)
    (ε := -1) (Or.inr rfl) P
    (by intro i; fin_cases i <;> simp [hP])
    (by simp [hP])
    (by intro n hn; simp only [hP, Finset.mem_insert, Finset.mem_singleton] at hn; omega)
    (by intro n hn; simp only [hP, Finset.mem_insert, Finset.mem_singleton] at hn; omega)
    (by
      intro ψ hψ h1
      have e3 : ((3 : ℤ) : ZMod (5 ^ r)) * u = (aX : ZMod (5 ^ r)) := by push_cast; exact hu3
      have e1 : ((1 : ℤ) : ZMod (5 ^ r)) * u = u := by push_cast; ring
      have e2 : ((-2 : ℤ) : ZMod (5 ^ r)) * u = (t : ZMod (5 ^ r)) := by push_cast; rw [hts]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, e3, e1, e2]
      have := hbase ψ hψ h1
      linear_combination this)
    3 (by simp [hP])
  simp [Fin.sum_univ_three] at key
  exact key

theorem kb_good (r : ℕ) (hr : 2 ≤ r) (aX aY aT : ℕ) (eX eY eT : ℂ)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hT0 : 0 < aT) (hsum : aX + aY + aT = 5 ^ r * 3 ^ 1)
    (hX3 : ¬ 3 ∣ aX) (hY3 : ¬ 3 ∣ aY) (hT3 : 3 ∣ aT) (hT5 : ¬ 5 ∣ aT)
    (H : H0 r 1 aX aY aT eX eY eT) : Good aX aY eX eY := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hX5 : 5 ∣ aX
  · exact Or.inl hX5
  · right
    have h5N : 5 ∣ 5 ^ r * 3 ^ 1 := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
    obtain ⟨η, hη⟩ := Erdos634.GA2SJ.exists_prim3 1 le_rfl
    have hη1 : η (-1) = -1 := eta3_neg_one η hη
    have E := kbE r 1 hr le_rfl aX aY aT eX eY eT hX3 hY3 hT3 hT5 hX5 H η hη
    rw [hη1, neg_neg] at E
    have hηX : η (aX : ZMod (3 ^ 1)) ≠ 0 := Erdos634.GA2LCore.nz η _ (unit3 1 aX hX3)
    by_cases hY5 : 5 ∣ aY
    · left
      rw [if_pos hY5, add_zero] at E
      exact (mul_eq_zero.1 E).resolve_right hηX
    · rw [if_neg hY5] at E
      have hneg : ¬ ((aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r))) := by
        intro h
        have h' := (Erdos634.GA2PD.natcast_neg_iff (5 ^ r) aY aX).1 h
        have h5 : 5 ∣ aY + aX := (dvd_pow_self 5 (by omega)).trans h'
        omega
      by_cases h1 : (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r))
      · rw [if_pos h1, if_neg hneg] at E
        have E' : eX * η (aX : ZMod (3 ^ 1)) + eY * η (aY : ZMod (3 ^ 1)) = 0 := by linear_combination E
        rcases mod3_cases aX aY hX3 hY3 with hm | hm
        · have hηeq : η (aY : ZMod (3 ^ 1)) = η (aX : ZMod (3 ^ 1)) := by rw [hm]
          have hsm : (eX + eY) * η (aX : ZMod (3 ^ 1)) = 0 := by linear_combination E' - eY * hηeq
          have hsum0 : eX + eY = 0 := (mul_eq_zero.1 hsm).resolve_right hηX
          have m3 : aY ≡ aX [MOD 3 ^ 1] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hm
          have m5 : aY ≡ aX [MOD 5 ^ r] := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
          have mm : aY ≡ aX [MOD 5 ^ r * 3 ^ 1] :=
            (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow _ _ (by norm_num))).1 ⟨m5, m3⟩
          have hlt : aX < 5 ^ r * 3 ^ 1 := by omega
          have hlt' : aY < 5 ^ r * 3 ^ 1 := by omega
          have hYX : aY = aX := by
            have := mm
            rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at this
            exact this
          exact Or.inr ⟨hYX.symm, hsum0⟩
        · have hηneg : η (aY : ZMod (3 ^ 1)) = - η (aX : ZMod (3 ^ 1)) := by
            rw [hm, show -(aX : ZMod (3 ^ 1)) = (-1) * (aX : ZMod (3 ^ 1)) by ring, map_mul, hη1]; ring
          have hsm : (eX - eY) * η (aX : ZMod (3 ^ 1)) = 0 := by linear_combination E' - eY * hηneg
          have hEY : eY = eX := by
            have := (mul_eq_zero.1 hsm).resolve_right hηX
            linear_combination -this
          left
          obtain ⟨t, ht⟩ := hT3
          subst ht
          exact kb_eta1 r hr aX aY t eX eY eT hsum hX5 hY5 hY3 hX3 hT5 h1 hEY H
      · rw [if_neg h1, if_neg hneg] at E
        left
        have : eX * η (aX : ZMod (3 ^ 1)) = 0 := by linear_combination E
        exact (mul_eq_zero.1 this).resolve_right hηX

theorem kbJ1_lab : Erdos634.GA2SY.KbJ1Lab := by
  intro r aX aY aT eX eY eT hr hX0 hY0 hT0 hsum hX3 hY3 hT3 hT5 H
  have GP : Good aX aY eX eY := kb_good r hr aX aY aT eX eY eT hX0 hY0 hT0 hsum hX3 hY3 hT3 hT5 H
  have GQ : Good aY aX eY eX :=
    kb_good r hr aY aX aT eY eX eT hY0 hX0 hT0 (by omega) hY3 hX3 hT3 hT5 (H0_swap H)
  have heT := Erdos634.GA2SM.kb_T r 1 hr aX aY aT eX eY eT hT5 GP GQ H
  intro x hx
  have hTX : aT ≠ aX := by intro h; apply hX3; rw [← h]; exact hT3
  have hTY : aT ≠ aY := by intro h; apply hY3; rw [← h]; exact hT3
  by_cases hTx : aT = x
  · rw [if_neg (fun h => hTX (by rw [hTx, h])), if_neg (fun h => hTY (by rw [hTx, h])), if_pos hTx, heT]
    ring
  · rw [if_neg hTx, add_zero]
    by_cases hPx : aX = x
    · have hP5 : ¬ 5 ∣ aX := by rw [hPx]; exact hx
      by_cases hQx : aY = x
      · have hQ5 : ¬ 5 ∣ aY := by rw [hQx]; exact hx
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
      by_cases hQx : aY = x
      · have hQ5 : ¬ 5 ∣ aY := by rw [hQx]; exact hx
        rw [if_pos hQx]
        rcases GQ with h | h | ⟨h, _⟩
        · exact absurd h hQ5
        · exact h
        · exfalso; apply hPx; rw [← h]; exact hQx
      · rw [if_neg hQx]

end Erdos634.GA2WC

#print axioms Erdos634.GA2WC.kbE
#print axioms Erdos634.GA2WC.kb_eta1
#print axioms Erdos634.GA2WC.kb_good
#print axioms Erdos634.GA2WC.kbJ1_lab
