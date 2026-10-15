/-
GA2S, atom D: the BOTTOM step at 5^r (r >= 2) killing shapes A and B of Prop K-a (copies of GA2PG.eqA / bottomA / bottomB with 5 -> 5^r).
  `bottomA_r` : a_Y = a_X + 2 m0, e_X = e_Y  =>  e_X = 0     (m0 = 5^r 3^j; uses psi and psi^-1 and psi(2)^2 != 1, which needs r >= 2)
  `bottomB_r` : a_X + a_Y = 2 m0 = a_S       =>  e_X = e_Y
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SC

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SD

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PF Erdos634.GA2PG Erdos634.GA2SC

theorem zmod5r_of_dvd (r : ℕ) (x : ℕ) (h : 5 ^ r ∣ x) : (x : ZMod (5 ^ r)) = 0 :=
  (ZMod.natCast_eq_zero_iff x (5 ^ r)).2 h

theorem unit5r (r : ℕ) (x : ℕ) (h : ¬ 5 ∣ x) : IsUnit (x : ZMod (5 ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h).symm

theorem one_neg_one_K (r j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψo : ψ (-1) = -1) :
    ψ (-1) * (1 : DirichletCharacter ℂ (2 ^ 2)) (-1) * (1 : DirichletCharacter ℂ (3 ^ j)) (-1) = -1 := by
  rw [hψo, MulChar.one_apply (isUnit_one.neg), MulChar.one_apply (isUnit_one.neg)]; norm_num

theorem eqA_r (r : ℕ) (hr : 2 ≤ r) (j : ℕ) (hj : 1 ≤ j) (aX aY aS b : ℕ) (eX eY eS : ℂ)
    (hY : aY = aX + 2 * (5 ^ r * 3 ^ j)) (hb : aX + 2 * b = 5 ^ r * 3 ^ j) (hZ : aS = 4 * b)
    (hX5 : ¬ 5 ∣ aX) (hX3 : ¬ 3 ∣ aX) (hXo : aX % 2 = 1) (hE : eX = eY)
    (H : H3K r j aX aY aS eX eY eS)
    (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) (hψo : ψ (-1) = -1) :
    eX * (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹) = eS * (ψ (2 : ZMod (5 ^ r)))⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3N : 3 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have h5N : 5 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
  have hM5 : ((5 ^ r * 3 ^ j : ℕ) : ZMod (5 ^ r)) = 0 := zmod5r_of_dvd r _ (dvd_mul_right _ _)
  generalize hN : 5 ^ r * 3 ^ j = N at *
  have hY5 : ¬ 5 ∣ aY := by omega
  have hY3 : ¬ 3 ∣ aY := by omega
  have hYo : aY % 2 = 1 := by omega
  have hb3 : ¬ 3 ∣ b := by omega
  have hS5 : ¬ 5 ∣ 4 * b := by omega
  subst hZ
  have hbot := H ψ hψ 1 1 (one_neg_one_K r j ψ hψo)
  rw [bracket_triv_odd_r r j hj ψ hψ aX hX5 (unit_cop j aX hXo hX3),
    bracket_triv_odd_r r j hj ψ hψ aY hY5 (unit_cop j aY hYo hY3),
    bracket_triv_four_r r j hj ψ hψ b hS5 hb3] at hbot
  have hcast : (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r)) := by
    rw [hY]; push_cast
    push_cast at hM5
    rw [hM5]; ring
  have hb2 : (2 : ZMod (5 ^ r)) * (b : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) := by
    have : ((aX + 2 * b : ℕ) : ZMod (5 ^ r)) = 0 := by rw [hb]; exact hM5
    push_cast at this
    linear_combination this
  have hψb : ψ (2 : ZMod (5 ^ r)) * ψ (b : ZMod (5 ^ r)) = - ψ (aX : ZMod (5 ^ r)) := by
    rw [← map_mul, hb2]
    have : -(aX : ZMod (5 ^ r)) = (-1) * (aX : ZMod (5 ^ r)) := by ring
    rw [this, map_mul, hψo]; ring
  have h2ne : ψ (2 : ZMod (5 ^ r)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (5 ^ r)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  have hψbv : ψ (b : ZMod (5 ^ r)) = - ψ (aX : ZMod (5 ^ r)) * (ψ (2 : ZMod (5 ^ r)))⁻¹ := by
    field_simp
    linear_combination hψb
  have hXne : ψ (aX : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ (unit5r r aX hX5)
  have h3ne : (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹) ≠ 0 := by
    intro h0
    apply Erdos634.GA2NF1.psi_three_ne_one r (by omega) ψ hψ
    have : (ψ (3 : ZMod (5 ^ r)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    simpa using inv_eq_one.1 this
  rw [hcast, hψbv, ← hE] at hbot
  have key : (2 * ψ (aX : ZMod (5 ^ r)) * (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹)) *
      (eX * (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹) - eS * (ψ (2 : ZMod (5 ^ r)))⁻¹) = 0 := by
    linear_combination hbot
  have := (mul_eq_zero.1 key).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero hXne) h3ne)
  linear_combination this

theorem bottomA_r (r : ℕ) (hr : 2 ≤ r) (j : ℕ) (hj : 1 ≤ j) (aX aY aS b : ℕ) (eX eY eS : ℂ)
    (hY : aY = aX + 2 * (5 ^ r * 3 ^ j)) (hb : aX + 2 * b = 5 ^ r * 3 ^ j) (hZ : aS = 4 * b)
    (hX5 : ¬ 5 ∣ aX) (hX3 : ¬ 3 ∣ aX) (hXo : aX % 2 = 1) (hE : eX = eY)
    (H : H3K r j aX aY aS eX eY eS) : eX = 0 := by
  obtain ⟨ψ, hψ, hψo⟩ := Erdos634.GA2SA.odd_prim_exists r (by omega)
  have h1 := eqA_r r hr j hj aX aY aS b eX eY eS hY hb hZ hX5 hX3 hXo hE H ψ hψ hψo
  have hψ' : (ψ⁻¹).IsPrimitive := Erdos634.GA2SA.inv_prim r ψ hψ
  have hψ'o : ψ⁻¹ (-1) = -1 := Erdos634.GA2SA.inv_neg_one r ψ hψo
  have h2 := eqA_r r hr j hj aX aY aS b eX eY eS hY hb hZ hX5 hX3 hXo hE H ψ⁻¹ hψ' hψ'o
  rw [MulChar.inv_apply_eq_inv', inv_inv] at h2
  have ha0 : ψ (2 : ZMod (5 ^ r)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (5 ^ r)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  set a := ψ (2 : ZMod (5 ^ r)) with ha
  have e : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  have h1' : eX * (a - 1) = eS := by linear_combination a * h1 + (eX + eS) * e
  have hk : eX * (1 - a ^ 2) = 0 := by linear_combination h2 - a * h1'
  have hne : 1 - a ^ 2 ≠ 0 := fun h =>
    Erdos634.GA2SA.psi_two_sq_ne_one r hr ψ hψ (by linear_combination -h)
  exact (mul_eq_zero.1 hk).resolve_right hne

theorem bottomB_r (r : ℕ) (hr : 2 ≤ r) (j : ℕ) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hsXY : aX + aY = 2 * (5 ^ r * 3 ^ j)) (hS : aS = 2 * (5 ^ r * 3 ^ j))
    (hX5 : ¬ 5 ∣ aX) (hX3 : ¬ 3 ∣ aX) (hXo : aX % 2 = 1)
    (H : H3K r j aX aY aS eX eY eS) : eX = eY := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, hψo⟩ := Erdos634.GA2SA.odd_prim_exists r (by omega)
  have h3N : 3 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have h5N : 5 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
  have hM5 : ((5 ^ r * 3 ^ j : ℕ) : ZMod (5 ^ r)) = 0 := zmod5r_of_dvd r _ (dvd_mul_right _ _)
  generalize hN : 5 ^ r * 3 ^ j = N at *
  have hY5 : ¬ 5 ∣ aY := by omega
  have hY3 : ¬ 3 ∣ aY := by omega
  have hYo : aY % 2 = 1 := by omega
  have hS5 : 5 ∣ aS := by omega
  have hbot := H ψ hψ 1 1 (one_neg_one_K r j ψ hψo)
  rw [bracket_triv_odd_r r j hj ψ hψ aX hX5 (unit_cop j aX hXo hX3),
    bracket_triv_odd_r r j hj ψ hψ aY hY5 (unit_cop j aY hYo hY3),
    bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 2 j) hψ _ aS hS5] at hbot
  have hcast : (aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) := by
    have : ((aX + aY : ℕ) : ZMod (5 ^ r)) = 0 := by
      rw [hsXY]; push_cast; push_cast at hM5; rw [hM5]; ring
    push_cast at this
    linear_combination this
  have hψy : ψ (aY : ZMod (5 ^ r)) = - ψ (aX : ZMod (5 ^ r)) := by
    rw [hcast]
    have : -(aX : ZMod (5 ^ r)) = (-1) * (aX : ZMod (5 ^ r)) := by ring
    rw [this, map_mul, hψo]; ring
  have hXne : ψ (aX : ZMod (5 ^ r)) ≠ 0 := Erdos634.GA2LCore.nz ψ _ (unit5r r aX hX5)
  have h2ne : (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹) ≠ 0 := by
    intro h0
    apply Erdos634.GA2NF1.psi_two_ne_one r (by omega) ψ hψ
    have : (ψ (2 : ZMod (5 ^ r)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    simpa using inv_eq_one.1 this
  have h3ne : (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹) ≠ 0 := by
    intro h0
    apply Erdos634.GA2NF1.psi_three_ne_one r (by omega) ψ hψ
    have : (ψ (3 : ZMod (5 ^ r)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    simpa using inv_eq_one.1 this
  rw [hψy] at hbot
  have key : (ψ (aX : ZMod (5 ^ r)) * ((1 - (ψ (2 : ZMod (5 ^ r)))⁻¹) * (1 - (ψ (3 : ZMod (5 ^ r)))⁻¹))) *
      (eX - eY) = 0 := by
    linear_combination hbot
  have := (mul_eq_zero.1 key).resolve_left (mul_ne_zero hXne (mul_ne_zero h2ne h3ne))
  linear_combination this

end Erdos634.GA2SD

#print axioms Erdos634.GA2SD.eqA_r
#print axioms Erdos634.GA2SD.bottomA_r
#print axioms Erdos634.GA2SD.bottomB_r
