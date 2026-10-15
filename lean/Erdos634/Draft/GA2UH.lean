/-
GA2U, atom H: killing the 3-divisible entry (trivial eta, psi odd) and the labelled theorem D3Lab (Prop D, r = 1, j >= 2).
  `kill_t`   : once the other two columns are Good, a column prime to 5 has e_t = 0   (eta = 1 mod 3^j, psi odd mod 5:
               `bracket_triv_ne_zero2`; psi(2), psi(3) != 1).
  `d3_lab`   : `GA2SY.D3Lab` -- every hypothesis kept: H1 1 j (primitive psi mod 5, all eta mod 3^j), an entry divisible by 3 and not by 5.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2UG
import Erdos634.Draft.GA2UE
import Erdos634.Draft.GA2SY

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UH

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.GA2SP (H1 H1_swap)
open Erdos634.GA2PG (Good pair_zero)
open Erdos634.GA2PA (not5_dvd')

theorem H1_cyc {r j : ℕ} {a b c : ℕ} {ea eb ec : ℂ} (H : H1 r j a b c ea eb ec) : H1 r j b c a eb ec ea := by
  intro ψ hψ η hodd
  have := H ψ hψ η hodd
  linear_combination this

theorem kill_t (j : ℕ) (hj : 1 ≤ j) (a b c : ℕ) (ea eb ec : ℂ) (H : H1 1 j a b c ea eb ec)
    (ha : Good a b ea eb) (hb : Good b a eb ea) (hc5 : ¬ 5 ∣ c) : ec = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨ψ, hψp, hψo⟩ := Erdos634.GA2UA.exists_psi_odd
  have hodd : ψ (-1) * (1 : DirichletCharacter ℂ (3 ^ j)) (-1) = -1 := by
    rw [hψo, MulChar.one_apply (isUnit_one.neg)]; norm_num
  have hbk := H ψ hψp 1 hodd
  set B : ℕ → ℂ := fun x => bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) (1 : DirichletCharacter ℂ (3 ^ j)))) x
    with hB
  have hB5 : ∀ x, 5 ∣ x → B x = 0 := fun x hx =>
    Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 1 j) hψp _ x hx
  have hz := pair_zero B hB5 a b ea eb ha hb
  have h2 : ψ (2 : ZMod (5 ^ 1)) ≠ 1 := by
    intro h
    have := Erdos634.GA2UA.psi_odd_sq ψ hψo
    rw [h] at this; norm_num at this
  have h3 : ψ (3 : ZMod (5 ^ 1)) ≠ 1 := by
    intro h
    have e : ψ (3 : ZMod (5 ^ 1)) * ψ (2 : ZMod (5 ^ 1)) = 1 := by
      rw [← map_mul]
      rw [Erdos634.GA2UA.five_three_two, map_one]
    rw [h, one_mul] at e
    exact h2 e
  have hne : B c ≠ 0 := Erdos634.GA2PA.bracket_triv_ne_zero2 1 1 j ψ hψp h2 h3 c hc5
  have : ea * B a + eb * B b + ec * B c = 0 := hbk
  rw [hz, zero_add] at this
  exact (mul_eq_zero.1 this).resolve_right hne


theorem d3_lab : Erdos634.GA2SY.D3Lab := by
  intro j aP aQ aS eP eQ eS hj hPo hQo hSe hP0 hQ0 hS0 hsum hgcd hT H
  have h3N : 3 ∣ 2 * (5 ^ 1 * 3 ^ j) := Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _) 2
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
  rcases hT with ⟨hP3, hP5⟩ | ⟨hQ3, hQ5⟩ | ⟨hS3, hS5⟩
  · -- T = P
    have hQ3 : ¬ 3 ∣ aQ := fun h => hno3PQ ⟨hP3, h⟩
    have hS3 : ¬ 3 ∣ bS := by
      intro h
      exact hno3PS ⟨hP3, by rw [hbS]; exact Dvd.dvd.mul_left h 2⟩
    have H' : H1 1 j aP aQ (2 * bS) eP eQ eS := by rw [← hbS]; exact H
    obtain ⟨hz1, hz2⟩ := Erdos634.GA2UE.topB j hj aP aQ bS eP eQ eS hP3 hP5 hQo hQ3 hS3 H'
    have GQS : Good aQ aS eQ eS := by
      rcases hz1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have GSQ : Good aS aQ eS eQ := by
      rw [hbS]
      rcases hz2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have heP := kill_t j (by omega) aQ aS aP eQ eS eP (H1_cyc H) GQS GSQ hP5
    refine key x hx (Or.inr (Or.inl heP)) ?_ ?_
    · rcases hz1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [hbS]; exact hz2
  · -- T = Q
    have hP3 : ¬ 3 ∣ aP := fun h => hno3PQ ⟨h, hQ3⟩
    have hS3 : ¬ 3 ∣ bS := by
      intro h
      exact hno3QS ⟨hQ3, by rw [hbS]; exact Dvd.dvd.mul_left h 2⟩
    have H' : H1 1 j aQ aP (2 * bS) eQ eP eS := by rw [← hbS]; exact H1_swap H
    obtain ⟨hz1, hz2⟩ := Erdos634.GA2UE.topB j hj aQ aP bS eQ eP eS hQ3 hQ5 hPo hP3 hS3 H'
    have GPS : Good aP aS eP eS := by
      rcases hz1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have GSP : Good aS aP eS eP := by
      rw [hbS]
      rcases hz2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have heQ := kill_t j (by omega) aP aS aQ eP eS eQ (H1_cyc (H1_swap H)) GPS GSP hQ5
    refine key x hx ?_ (Or.inr (Or.inl heQ)) ?_
    · rcases hz1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [hbS]; exact hz2
  · -- T = S
    have hP3 : ¬ 3 ∣ aP := fun h => hno3PS ⟨h, hS3⟩
    have hQ3 : ¬ 3 ∣ aQ := fun h => hno3QS ⟨h, hS3⟩
    obtain ⟨GP, GQ⟩ := Erdos634.GA2UG.topA j hj aP aQ aS eP eQ eS hPo hQo hP3 hQ3 hS3 hS5 hS0 hsum H
    have heS := kill_t j (by omega) aP aQ aS eP eQ eS H GP GQ hS5
    exact key x hx GP GQ (Or.inr heS)

end Erdos634.GA2UH

#print axioms Erdos634.GA2UH.kill_t
#print axioms Erdos634.GA2UH.d3_lab
