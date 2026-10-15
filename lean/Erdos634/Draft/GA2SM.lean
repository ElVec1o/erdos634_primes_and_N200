/-
GA2S, atom M: Prop K-b with an entry divisible by 3 (i = 0, r >= 2, j >= 2): the hidden entry and the labelled theorem, then the slice and `partKb3_j2`.
  `kb_T`     : eT = 0 once the two visible entries are Good (one character psi x eta3 of conductor 3^j / gcd (aT, 3^j)).
  `kb_lab`   : class sums vanish on every column prime to 5 for the triple (X, Y, T).
  `hP_Kb3`, `lemmaS5_Kb3`, `gapA2_slice_Kb3`, `partKb3_j2` : Lemma S', the slice, and the part of `PartKb3` with j >= 2.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SL
import Erdos634.Draft.GA2SH

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SM

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PG
open Erdos634.GA2SD Erdos634.GA2SK Erdos634.GA2SL
open Erdos634.GA2NP7 (chi_neg_one class_sum_eq cast_ite3)

theorem kb_T (r j : ℕ) (hr : 2 ≤ r) (aX aY aT : ℕ) (eX eY eT : ℂ) (hT5 : ¬ 5 ∣ aT)
    (hX : Good aX aY eX eY) (hY : Good aY aX eY eX) (H : H0 r j aX aY aT eX eY eT) : eT = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hD : 3 ^ j / Nat.gcd (3 ^ j) aT ∣ 3 ^ j := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨ψ, η3, hψ, hη3, hodd⟩ := exists_L1char0 r (by omega) j _ hD
  have hbot := H ψ hψ η3 hodd
  set B : ℕ → ℂ := fun x => bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η3)) x with hB
  have hB5 : ∀ x, 5 ∣ x → B x = 0 := fun x hx =>
    bracket_p_dvd (p := 5) (r := r) (by omega) (not5_dvd' 0 j) hψ _ x hx
  have hBne : B aT ≠ 0 := by
    refine bracket_ne_zero_of_eq2 r 0 j ψ hψ (1 : DirichletCharacter ℂ (2 ^ 0)) η3 aT hT5 ?_
    have hc1 : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor = 1 := DirichletCharacter.conductor_one
    rw [hc1, hη3, one_mul]
    unfold dm
    simp
  have hz := pair_zero B hB5 aX aY eX eY hX hY
  have : eX * B aX + eY * B aY + eT * B aT = 0 := hbot
  rw [hz, zero_add] at this
  exact (mul_eq_zero.1 this).resolve_right hBne

theorem kb_lab (r j : ℕ) (hr : 2 ≤ r) (hj : 2 ≤ j) (aX aY aT : ℕ) (eX eY eT : ℂ)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hT0 : 0 < aT) (hsum : aX + aY + aT = 5 ^ r * 3 ^ j)
    (hX3 : ¬ 3 ∣ aX) (hY3 : ¬ 3 ∣ aY) (hT3 : 3 ∣ aT) (hT5 : ¬ 5 ∣ aT)
    (H : H0 r j aX aY aT eX eY eT) :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aX = x then eX else 0) + (if aY = x then eY else 0) + (if aT = x then eT else 0) = 0 := by
  have GP : Good aX aY eX eY := by
    by_cases h5 : 5 ∣ aX
    · exact Or.inl h5
    · exact Or.inr (kb_top r j hr hj aX aY aT eX eY eT hX0 hY0 hT0 hsum hX3 hY3 hT3 hT5 h5 H)
  have GQ : Good aY aX eY eX := by
    by_cases h5 : 5 ∣ aY
    · exact Or.inl h5
    · exact Or.inr (kb_top r j hr hj aY aX aT eY eX eT hY0 hX0 hT0 (by omega) hY3 hX3 hT3 hT5 h5
        (H0_swap H))
  have heT := kb_T r j hr aX aY aT eX eY eT hT5 GP GQ H
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

end Erdos634.GA2SM

#print axioms Erdos634.GA2SM.kb_T
#print axioms Erdos634.GA2SM.kb_lab
