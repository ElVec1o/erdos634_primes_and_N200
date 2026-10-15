/-
Theorem K-a in labelled form, assembly of the steps (i = 2, n = 4 * 5^r * 3^j, r >= 2, j >= 1).
  `stepK2`  : X odd, 3 | X (5 !| X), Y killed  =>  eX = 0                        [eta3 of conductor 3^j / gcd, GA2PG.stepB2 at 5^r]
  `stepK3`  : the even entry S                                                      [trivial characters, GA2PG.stepB3 at 5^r]
  `goodK`   : every odd entry is `Good` (class sum vanishes / matched pair)
  `theoremKa_lab` : the class sums vanish on every column prime to 5.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SF

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SG

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PF Erdos634.GA2PG
open Erdos634.GA2SC Erdos634.GA2SD Erdos634.GA2SE Erdos634.GA2SF

theorem stepK2 (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hSe : aS % 2 = 0)
    (H : H3K r j aX aY aS eX eY eS) (hX5 : ¬ 5 ∣ aX) (hY : eY = 0 ∨ 5 ∣ aY) : eX = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨χ4, hχ4, hχ4o⟩ := exists_chi4
  have hD : 3 ^ j / Nat.gcd (3 ^ j) aX ∣ 3 ^ j := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨ψ, η3, hψ, hη3, hodd⟩ := exists_L1char_r r (by omega) j _ hD χ4 hχ4o
  have hbot := H ψ hψ χ4 η3 hodd
  have hX : bracket (chi ψ (chi χ4 η3)) aX ≠ 0 := by
    refine bracket_ne_zero_of_eq2 r 2 j ψ hψ χ4 η3 aX hX5 ?_
    rw [dm_odd2 2 j aX (Nat.odd_iff.2 hXo) (by norm_num), hη3]
    have hc4 : χ4.conductor = 2 ^ 2 := hχ4
    rw [hc4]
  have hS := bracket_even_zero_r r j (by omega) ψ hψ χ4 hχ4 η3 aS hSe
  have hYt : eY * bracket (chi ψ (chi χ4 η3)) aY = 0 := by
    rcases hY with h | h
    · rw [h, zero_mul]
    · rw [bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 2 j) hψ _ aY h, mul_zero]
  rw [hS, hYt, mul_zero, add_zero, add_zero] at hbot
  exact (mul_eq_zero.1 hbot).resolve_right hX


theorem stepK3 (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (H : H3K r j aX aY aS eX eY eS) (hS5 : ¬ 5 ∣ aS)
    (hX : Good aX aY eX eY) (hY : Good aY aX eY eX) : eS = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, hψo⟩ := Erdos634.GA2SA.odd_prim_exists r (by omega)
  have hbot := H ψ hψ 1 1 (one_neg_one_K r j ψ hψo)
  set B : ℕ → ℂ := fun x => bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 2)) (1 : DirichletCharacter ℂ (3 ^ j)))) x with hB
  have hB5 : ∀ x, 5 ∣ x → B x = 0 := fun x hx =>
    bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 2 j) hψ _ x hx
  have hBne : B aS ≠ 0 :=
    bracket_triv_ne_zero2 r 2 j ψ hψ (Erdos634.GA2NF1.psi_two_ne_one r (by omega) ψ hψ)
      (Erdos634.GA2NF1.psi_three_ne_one r (by omega) ψ hψ) aS hS5
  have hz := pair_zero B hB5 aX aY eX eY hX hY
  have : eX * B aX + eY * B aY + eS * B aS = 0 := hbot
  rw [hz, zero_add] at this
  exact (mul_eq_zero.1 this).resolve_right hBne


theorem goodK (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hYo : aY % 2 = 1) (hSe : aS % 2 = 0)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hS0 : 0 < aS)
    (hsum : aX + aY + aS = 4 * (5 ^ r * 3 ^ j))
    (hno3 : ¬ (3 ∣ aX ∧ 3 ∣ aY))
    (H : H3K r j aX aY aS eX eY eS) : Good aX aY eX eY := by
  by_cases h5 : 5 ∣ aX
  · exact Or.inl h5
  · by_cases h3 : 3 ∣ aX
    · right; left
      have hY3 : ¬ 3 ∣ aY := fun h => hno3 ⟨h3, h⟩
      refine stepK2 r j hr hj aX aY aS eX eY eS hXo hSe H h5 ?_
      by_cases h5Y : 5 ∣ aY
      · exact Or.inr h5Y
      · left
        have := stepK1' r j hr hj aY aX aS eY eX eS hYo hXo hSe hY0 hX0 hS0 (by omega) (H3K_swap H)
          ⟨h5Y, unit_cop j aY hYo hY3⟩
        rcases this with h | ⟨h, _⟩
        · exact h
        · exfalso; exact hY3 (by rw [h]; exact h3)
    · right
      exact stepK1' r j hr hj aX aY aS eX eY eS hXo hYo hSe hX0 hY0 hS0 hsum H ⟨h5, unit_cop j aX hXo h3⟩

/-- **Theorem K-a (labelled form, i = 2, r >= 2, j >= 1).** n = 4 * 5^r * 3^j; P, Q the odd entries, S the even entry. -/
theorem theoremKa_lab (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : aP % 2 = 1) (hQo : aQ % 2 = 1) (hSe : aS % 2 = 0)
    (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 4 * (5 ^ r * 3 ^ j))
    (hgcd : Nat.gcd (Nat.gcd aP aQ) aS = 1)
    (H : H3K r j aP aQ aS eP eQ eS) :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aP = x then eP else 0) + (if aQ = x then eQ else 0) + (if aS = x then eS else 0) = 0 := by
  have h3N : 3 ∣ 4 * (5 ^ r * 3 ^ j) := Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _) 4
  have hno3 : ¬ (3 ∣ aP ∧ 3 ∣ aQ) := by
    rintro ⟨h1, h2⟩
    have h3 : 3 ∣ aS := by omega
    have := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [hgcd] at this
    omega
  have GP : Good aP aQ eP eQ := goodK r j hr hj aP aQ aS eP eQ eS hPo hQo hSe hP0 hQ0 hS0 hsum hno3 H
  have GQ : Good aQ aP eQ eP := goodK r j hr hj aQ aP aS eQ eP eS hQo hPo hSe hQ0 hP0 hS0 (by omega)
    (fun h => hno3 ⟨h.2, h.1⟩) (H3K_swap H)
  intro x hx
  have hSP : aS ≠ aP := by intro h; omega
  have hSQ : aS ≠ aQ := by intro h; omega
  by_cases hSx : aS = x
  · have hS5 : ¬ 5 ∣ aS := by rw [hSx]; exact hx
    have heS := stepK3 r j hr hj aP aQ aS eP eQ eS H hS5 GP GQ
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

end Erdos634.GA2SG

#print axioms Erdos634.GA2SG.stepK2
#print axioms Erdos634.GA2SG.stepK3
#print axioms Erdos634.GA2SG.goodK
#print axioms Erdos634.GA2SG.theoremKa_lab
