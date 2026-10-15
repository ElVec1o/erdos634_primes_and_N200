/-
GA2S, atom E: the TOP step of Prop K-a (i = 2, n = 4 * 5^r * 3^j, r >= 2, j >= 1) by the PRODUCT-GROUP method.

For the odd 2-part chi_4 the equations are on EVEN products psi eta (psi primitive mod 5^r, eta ANY character mod 3^j); the
visible odd entries (prime to 5 and to 3) contribute kappa(psi, eta) psi chi_4 eta (a) with a uniform kappa != 0 (`GA2SC.bracket_Ka`),
so by `GA2SB.odd_of_top` the function F = sum_t c_t [y_t] on (Z/5^r 3^j)^x (c_t = e_t chi_4(a_t)) is ODD.  Evaluating at y_X:
  `top_two`   : eX chi4(aX) + [aY = +-aX mod m0, 5 !| aY] eY chi4(aY) = 0.
  `K_eq1`     : the same in the exact shape of GA2PF.B_eq1 (m0 = 5^r 3^j).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SB
import Erdos634.Draft.GA2SD

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SE

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PF Erdos634.GA2PG
open Erdos634.GA2SC Erdos634.GA2SD
open Erdos634.GA2QK2 (Fv c5 c3)

theorem m0_odd_r (r j : ℕ) : (5 ^ r * 3 ^ j) % 2 = 1 := by
  have : Odd (5 ^ r * 3 ^ j) := Nat.odd_mul.2 ⟨Odd.pow (by decide), Odd.pow (by decide)⟩
  exact Nat.odd_iff.1 this

theorem neg_ne_self_m0 (r j : ℕ) (hr : 1 ≤ r) (x : ℕ) (hx : ¬ 5 ∣ x) :
    ¬ ((x : ZMod (5 ^ r * 3 ^ j)) = -(x : ZMod (5 ^ r * 3 ^ j))) := by
  intro h
  have h2 := (natcast_neg_iff (5 ^ r * 3 ^ j) x x).1 h
  have h3 : 5 ∣ x + x :=
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _).trans h2
  omega

/-- the evaluation of the odd function at `y_X`. -/
theorem top_two (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hSe : aS % 2 = 0) (hXo : aX % 2 = 1) (hYo : aY % 2 = 1)
    (hX5 : ¬ 5 ∣ aX) (hX3 : ¬ 3 ∣ aX) (hY3 : 5 ∣ aY ∨ ¬ 3 ∣ aY)
    (H : H3K r j aX aY aS eX eY eS)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4 : χ4.IsPrimitive) (hχ4o : χ4 (-1) = -1) :
    eX * χ4 (aX : ZMod (2 ^ 2)) +
      (if 5 ∣ aY then 0 else
        if ((aY : ZMod (5 ^ r * 3 ^ j)) = (aX : ZMod (5 ^ r * 3 ^ j)) ∨
            (aY : ZMod (5 ^ r * 3 ^ j)) = -(aX : ZMod (5 ^ r * 3 ^ j)))
        then eY * χ4 (aY : ZMod (2 ^ 2)) else 0) = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ r * 3 ^ j) := ⟨by positivity⟩
  set a2 : Fin 2 → ℕ := ![aX, aY] with ha2
  set e2 : Fin 2 → ℂ := ![eX, eY] with he2
  set y : Fin 2 → ZMod (5 ^ r * 3 ^ j) := fun t => (a2 t : ZMod (5 ^ r * 3 ^ j)) with hy
  set c : Fin 2 → ℂ := fun t => if 5 ∣ a2 t then 0 else e2 t * χ4 (a2 t : ZMod (2 ^ 2)) with hc
  have hno3 : ∀ t, ¬ 5 ∣ a2 t → ¬ 3 ∣ a2 t := by
    intro t ht h3
    fin_cases t
    · exact hX3 h3
    · rcases hY3 with h | h
      · exact ht h
      · exact h h3
  have hunit : ∀ t, c t ≠ 0 → IsUnit (y t) := by
    intro t ht
    have h5 : ¬ 5 ∣ a2 t := by
      intro h; apply ht; simp only [hc, if_pos h]
    have h3 := hno3 t h5
    rw [hy]
    show IsUnit ((a2 t : ℕ) : ZMod (5 ^ r * 3 ^ j))
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5).symm
    · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h3).symm
  have hA : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = 1 →
      ∑ t ∈ (Finset.univ : Finset (Fin 2)), c t * (ψ (c5 r j (y t)) * η (c3 r j (y t))) = 0 := by
    intro ψ hψ η hpe
    have hodd : ψ (-1) * χ4 (-1) * η (-1) = -1 := by rw [hχ4o]; linear_combination -hpe
    obtain ⟨κ, hκ, hb⟩ := bracket_Ka r j hr hj ψ hψ χ4 hχ4 hχ4o η
    have hbot := H ψ hψ χ4 η hodd
    rw [bracket_even_zero_r r j (by omega) ψ hψ χ4 hχ4 η aS hSe, mul_zero, add_zero] at hbot
    have key : ∀ (T : ℕ) (e : ℂ), T % 2 = 1 → (5 ∣ T ∨ ¬ 3 ∣ T) →
        e * bracket (chi ψ (chi χ4 η)) T =
          κ * ((if 5 ∣ T then 0 else e * χ4 (T : ZMod (2 ^ 2))) *
            (ψ (T : ZMod (5 ^ r)) * η (T : ZMod (3 ^ j)))) := by
      intro T e hTo hT3
      by_cases h5 : 5 ∣ T
      · rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 2 j) hψ _ T h5, if_pos h5]; ring
      · rw [if_neg h5, hb T h5 (unit_cop j T hTo (hT3.resolve_left h5))]; ring
    rw [key aX eX hXo (Or.inr hX3), key aY eY hYo hY3] at hbot
    have hsum : κ * (∑ t ∈ (Finset.univ : Finset (Fin 2)), c t *
        (ψ (c5 r j (y t)) * η (c3 r j (y t)))) = 0 := by
      rw [Fin.sum_univ_two, mul_add]
      simp only [hc, hy, ha2, he2, Matrix.cons_val_zero, Matrix.cons_val_one, map_natCast]
      linear_combination hbot
    exact (mul_eq_zero.1 hsum).resolve_left hκ
  set P : Finset (ZMod (5 ^ r * 3 ^ j)) := {y 0, -y 0, y 1, -y 1} with hP
  have hPc : ∀ t ∈ (Finset.univ : Finset (Fin 2)), c t ≠ 0 → y t ∈ P ∧ -(y t) ∈ P := by
    intro t _ _
    fin_cases t <;> simp [hP]
  have hcount : ∀ k : ZMod (5 ^ (r - 1) * 3 ^ j),
      (P.filter (fun g => Erdos634.GA2QK2.cM r j g = k)).card ≤ 4 :=
    fun k => (Finset.card_filter_le _ _).trans Finset.card_le_four
  have hodd := Erdos634.GA2SB.odd_of_top r j hr Finset.univ y c (fun t _ => hunit t) hA P hPc hcount (y 0)
  simp only [Erdos634.GA2QK2.Fv] at hodd
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hodd
  have hneg : ¬ (-(y 0) = y 0) := fun h => neg_ne_self_m0 r j (by omega) aX hX5 h.symm
  have hc0 : c 0 = eX * χ4 (aX : ZMod (2 ^ 2)) := by
    simp only [hc, ha2, he2, Matrix.cons_val_zero, if_neg hX5]
  rw [if_pos rfl, if_neg hneg, zero_add, hc0] at hodd
  by_cases hY5 : 5 ∣ aY
  · have hc1 : c 1 = 0 := by simp only [hc, ha2, Matrix.cons_val_one, Matrix.cons_val_zero, if_pos hY5]
    rw [hc1] at hodd
    simp only [ite_self, add_zero] at hodd
    rw [if_pos hY5]
    simpa using hodd
  · have hc1 : c 1 = eY * χ4 (aY : ZMod (2 ^ 2)) := by
      simp only [hc, ha2, he2, Matrix.cons_val_one, Matrix.cons_val_zero, if_neg hY5]
    rw [hc1] at hodd
    rw [if_neg hY5]
    have hy0 : y 0 = (aX : ZMod (5 ^ r * 3 ^ j)) := rfl
    have hy1 : y 1 = (aY : ZMod (5 ^ r * 3 ^ j)) := rfl
    rw [hy0, hy1] at hodd
    by_cases h1 : (aY : ZMod (5 ^ r * 3 ^ j)) = (aX : ZMod (5 ^ r * 3 ^ j))
    · have h2 : ¬ (-(aX : ZMod (5 ^ r * 3 ^ j)) = (aY : ZMod (5 ^ r * 3 ^ j))) := by
        intro h; apply hneg; rw [hy0]; rw [h1] at h; exact h
      rw [if_pos h1.symm, if_neg h2] at hodd
      rw [if_pos (Or.inl h1)]
      linear_combination hodd
    · by_cases h2 : (aY : ZMod (5 ^ r * 3 ^ j)) = -(aX : ZMod (5 ^ r * 3 ^ j))
      · have h1' : ¬ ((aX : ZMod (5 ^ r * 3 ^ j)) = (aY : ZMod (5 ^ r * 3 ^ j))) := fun h => h1 h.symm
        rw [if_neg h1', if_pos h2.symm] at hodd
        rw [if_pos (Or.inr h2)]
        linear_combination hodd
      · have h1' : ¬ ((aX : ZMod (5 ^ r * 3 ^ j)) = (aY : ZMod (5 ^ r * 3 ^ j))) := fun h => h1 h.symm
        have h2' : ¬ (-(aX : ZMod (5 ^ r * 3 ^ j)) = (aY : ZMod (5 ^ r * 3 ^ j))) := fun h => h2 h.symm
        rw [if_neg h1', if_neg h2'] at hodd
        rw [if_neg (by tauto)]
        linear_combination hodd

end Erdos634.GA2SE

#print axioms Erdos634.GA2SE.top_two
