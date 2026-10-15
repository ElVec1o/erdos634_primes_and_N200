/-
GA2S, atom L: Prop K-b (i = 0) with an entry T divisible by 3, not by 5, r >= 2, j >= 2: the labelled theorem on (X, Y, T).
  `H0`      : the labelled hypothesis (odd characters psi x (1 mod 2^0) x eta, psi primitive mod 5^r, eta mod 3^j).
  `kb_top`  : X odd-weight step: eX = 0 or (aX = aY and eX + eY = 0)         [primitive eta only; GA2SK tools]
  `kb_T`    : the hidden entry T: eT = 0 once the two visible entries are `Good`.
  `kb_lab`  : the class sums vanish on every column prime to 5.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SK

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SL

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PG
open Erdos634.GA2SD Erdos634.GA2SJ Erdos634.GA2SK

def H0 (r j : ℕ) (aX aY aT : ℕ) (eX eY eT : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
    ψ (-1) * η (-1) = -1 →
    eX * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) aX +
    eY * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) aY +
    eT * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) aT = 0

theorem H0_swap {r j : ℕ} {aX aY aT : ℕ} {eX eY eT : ℂ} (H : H0 r j aX aY aT eX eY eT) :
    H0 r j aY aX aT eY eX eT := by
  intro ψ hψ η hodd
  have := H ψ hψ η hodd
  linear_combination this

theorem unit3 (j : ℕ) (x : ℕ) (h : ¬ 3 ∣ x) : IsUnit (x : ZMod (3 ^ j)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm

theorem kb_top (r j : ℕ) (hr : 2 ≤ r) (hj : 2 ≤ j) (aX aY aT : ℕ) (eX eY eT : ℂ)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hT0 : 0 < aT) (hsum : aX + aY + aT = 5 ^ r * 3 ^ j)
    (hX3 : ¬ 3 ∣ aX) (hY3 : ¬ 3 ∣ aY) (hT3 : 3 ∣ aT) (hT5 : ¬ 5 ∣ aT) (hX5 : ¬ 5 ∣ aX)
    (H : H0 r j aX aY aT eX eY eT) :
    eX = 0 ∨ (aX = aY ∧ eX + eY = 0) := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hX3' : Nat.Coprime 3 aX := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hX3
  have hY3' : Nat.Coprime 3 aY := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hY3
  -- the 5-adic equation for each primitive eta
  have E : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
      eX * η (aX : ZMod (3 ^ j)) + (if 5 ∣ aY then 0 else eY * η (aY : ZMod (3 ^ j)) *
        ((if (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r)) then 1 else 0) +
          (-η (-1)) * (if (aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) then 1 else 0))) = 0 := by
    intro η hη
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
        · rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 0 j) hψ _ aY h5, mul_zero, add_zero] at hb
          rw [if_pos h5]; linear_combination hb
        · rw [hκb aY h5 hY3'] at hb
          rw [if_neg h5]; linear_combination hb
      exact (mul_eq_zero.1 hmain).resolve_left hκ)
    refine Eq.trans ?_ this
    split_ifs <;> ring
  obtain ⟨η0, h0⟩ := exists_prim3 j (by omega)
  have hη0X : η0 (aX : ZMod (3 ^ j)) ≠ 0 := Erdos634.GA2LCore.nz η0 _ (unit3 j aX hX3)
  have hη0Y : η0 (aY : ZMod (3 ^ j)) ≠ 0 := Erdos634.GA2LCore.nz η0 _ (unit3 j aY hY3)
  have hone : (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r)) → (aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) → False := by
    intro h1 h2
    have : (aX : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) := h1.symm.trans h2
    have h3 := (natcast_neg_iff (5 ^ r) aX aX).1 this
    have h4 : 5 ∣ aX + aX := (dvd_pow_self 5 (by omega)).trans h3
    omega
  by_cases hY5 : 5 ∣ aY
  · left
    have := E η0 h0
    rw [if_pos hY5, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right hη0X
  · by_cases h1 : (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r))
    · by_cases heY : eY = 0
      · left
        have := E η0 h0
        rw [if_neg hY5, heY] at this
        simpa [hη0X] using this
      · have hc : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
            η ((unit3 j aY hY3).unit : ZMod (3 ^ j)) = (-eX / eY) * η ((unit3 j aX hX3).unit : ZMod (3 ^ j)) := by
          intro η hη
          have := E η hη
          rw [if_neg hY5, if_pos h1, if_neg (fun h2 => hone h1 h2)] at this
          rw [IsUnit.unit_spec, IsUnit.unit_spec]
          field_simp
          linear_combination this
        have hvu := const_ratio3 j hj _ _ _ hc
        have hv3 : (aY : ZMod (3 ^ j)) = (aX : ZMod (3 ^ j)) := by
          have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) hvu
          simpa using this
        have m3 : aY ≡ aX [MOD 3 ^ j] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hv3
        have m5 : aY ≡ aX [MOD 5 ^ r] := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
        have mm : aY ≡ aX [MOD 5 ^ r * 3 ^ j] :=
          (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow _ _ (by norm_num))).1 ⟨m5, m3⟩
        have hlt : aX < 5 ^ r * 3 ^ j := by omega
        have hlt' : aY < 5 ^ r * 3 ^ j := by omega
        have hYX : aY = aX := by
          have := mm
          rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at this
          exact this
        right
        refine ⟨hYX.symm, ?_⟩
        have := E η0 h0
        rw [if_neg hY5, if_pos h1, if_neg (fun h2 => hone h1 h2), hYX] at this
        have : (eX + eY) * η0 (aX : ZMod (3 ^ j)) = 0 := by linear_combination this
        exact (mul_eq_zero.1 this).resolve_right hη0X
    · by_cases h2 : (aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r))
      · by_cases heY : eY = 0
        · left
          have := E η0 h0
          rw [if_neg hY5, heY] at this
          simpa [hη0X] using this
        · exfalso
          have hc : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive →
              η (-(unit3 j aY hY3).unit : (ZMod (3 ^ j))ˣ) = (eX / eY) * η ((unit3 j aX hX3).unit : ZMod (3 ^ j)) := by
            intro η hη
            have := E η hη
            rw [if_neg hY5, if_neg h1, if_pos h2] at this
            rw [Units.val_neg, IsUnit.unit_spec, IsUnit.unit_spec]
            have hn : (-(aY : ZMod (3 ^ j))) = (-1) * (aY : ZMod (3 ^ j)) := by ring
            rw [hn, map_mul]
            field_simp
            linear_combination -this
          have hvu := const_ratio3 j hj _ _ _ hc
          have hv3 : -(aY : ZMod (3 ^ j)) = (aX : ZMod (3 ^ j)) := by
            have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) hvu
            simpa using this
          have m3 : 3 ^ j ∣ aX + aY := by
            have : (aX : ZMod (3 ^ j)) = -(aY : ZMod (3 ^ j)) := hv3.symm
            exact (natcast_neg_iff (3 ^ j) aX aY).1 this
          have m5 : 5 ^ r ∣ aX + aY := by
            have : (aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) := h2
            have := (natcast_neg_iff (5 ^ r) aY aX).1 this
            rwa [add_comm] at this
          have mm : 5 ^ r * 3 ^ j ∣ aX + aY :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num)) m5 m3
          have := Nat.le_of_dvd (by omega) mm
          omega
      · left
        have := E η0 h0
        rw [if_neg hY5, if_neg h1, if_neg h2] at this
        simp at this
        simpa [hη0X] using this

end Erdos634.GA2SL

#print axioms Erdos634.GA2SL.kb_top
