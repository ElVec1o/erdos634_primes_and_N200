/-
The remaining cases of GapA2 as labelled statements, with the consumer reductions proved.

  `KbJ1Lab` : Prop K-b, entry T = 3t (5 !| t) at j = 1 (n = 3 * 5^r, r >= 2): the labelled statement
              "H0 r 1 aX aY aT e  ==>  class sums vanish"  (hypothesis: only psi PRIMITIVE mod 5^r, eta mod 3).
  `KcJ1Lab` : Prop K-c, T = S the EVEN entry divisible by 3 at j = 1 (n = 6 * 5^r, r >= 2): "H1 r 1 aP aQ aS e ==> class sums vanish".
  `D3Lab`   : Prop D, an entry divisible by 3 (not by 5), r = 1 (n = 10 * 3^j, j >= 2): "H1 1 j aP aQ aS e ==> class sums vanish".
  `partKb3Open_of_lab`, `partKc3Open_of_lab`, `partD3_of_lab` : the consumer chains (Lemma S' via `LemmaSR.lemmaR`, `r0c_core15`).
  `gapA2_of_atoms : GapA2Atoms (= D3Lab /\ KbJ1Lab /\ KcJ1Lab) -> GapA2`.
The three statements are not proved in this module.  Each is a statement about weights satisfying only the PRIMITIVE-psi equations.  Numerical data
(float SVD of the full odd-character matrix with psi primitive, eta ALL, every tile with such an entry, rank = number of
columns prime to 5): KbJ1Lab holds at n = 75, 375, 1875; KcJ1Lab at n = 150, 750, 3750; D3Lab at n = 90, 270, 810; the same fails at n = 30
(r = 1, j = 1: 10 bad tiles).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SX
import Erdos634.Draft.GA2SU

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SY

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2NP7 (chi_neg_one class_sum_eq cast_ite3)
open Erdos634.GA2SL (H0 H0_swap)
open Erdos634.GA2SP (H1 H1_swap)

def KbJ1Lab : Prop :=
  ∀ (r : ℕ) (aX aY aT : ℕ) (eX eY eT : ℂ), 2 ≤ r → 0 < aX → 0 < aY → 0 < aT →
    aX + aY + aT = 5 ^ r * 3 ^ 1 → ¬ 3 ∣ aX → ¬ 3 ∣ aY → 3 ∣ aT → ¬ 5 ∣ aT →
    H0 r 1 aX aY aT eX eY eT →
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aX = x then eX else 0) + (if aY = x then eY else 0) + (if aT = x then eT else 0) = 0

def KcJ1Lab : Prop :=
  ∀ (r : ℕ) (aP aQ aS : ℕ) (eP eQ eS : ℂ), 2 ≤ r → aP % 2 = 1 → aQ % 2 = 1 → aS % 2 = 0 →
    0 < aP → 0 < aQ → 0 < aS → aP + aQ + aS = 2 * (5 ^ r * 3 ^ 1) →
    Nat.gcd (Nat.gcd aP aQ) aS = 1 → 3 ∣ aS → ¬ 5 ∣ aS →
    H1 r 1 aP aQ aS eP eQ eS →
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aP = x then eP else 0) + (if aQ = x then eQ else 0) + (if aS = x then eS else 0) = 0

def D3Lab : Prop :=
  ∀ (j : ℕ) (aP aQ aS : ℕ) (eP eQ eS : ℂ), 2 ≤ j → aP % 2 = 1 → aQ % 2 = 1 → aS % 2 = 0 →
    0 < aP → 0 < aQ → 0 < aS → aP + aQ + aS = 2 * (5 ^ 1 * 3 ^ j) →
    Nat.gcd (Nat.gcd aP aQ) aS = 1 →
    ((3 ∣ aP ∧ ¬ 5 ∣ aP) ∨ (3 ∣ aQ ∧ ¬ 5 ∣ aQ) ∨ (3 ∣ aS ∧ ¬ 5 ∣ aS)) →
    H1 1 j aP aQ aS eP eQ eS →
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aP = x then eP else 0) + (if aQ = x then eQ else 0) + (if aS = x then eS else 0) = 0

theorem hP_KbJ1 (hlab : KbJ1Lab) (r : ℕ) (hr : 2 ≤ r) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 0 * 3 ^ 1))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ r * (2 ^ 0 * 3 ^ 1)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ r * (2 ^ 0 * 3 ^ 1)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 5 ^ r * 3 ^ 1 := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have h3N : 3 ∣ 5 ^ r * 3 ^ 1 := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ 1),
      ψ (-1) * η (-1) = -1 →
      (e 0 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) (a 0) +
      (e 1 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) (a 1) +
      (e 2 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) (a 2) = 0 := by
    intro ψ hψ η hodd
    have hodd' : (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)).Odd := by
      show (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) (-1) = -1
      rw [chi_neg_one, chi_neg_one, Erdos634.GA2PD.one_mod_one, one_mul]; exact hodd
    have := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he _ hodd'
    simpa [Fin.sum_univ_three] using this
  have g1 := hpos 0
  have g2 := hpos 1
  have g3 := hpos 2
  have no3 : ¬ (3 ∣ a 0 ∧ 3 ∣ a 1 ∧ 3 ∣ a 2) := by
    rintro ⟨h0, h1, h2⟩
    have := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h2)
    rw [hgcd] at this
    omega
  intro j' hx
  rw [class_sum_eq a e j' hx]
  obtain ⟨t, ht5, ht3⟩ := hT
  fin_cases t
  · -- T = a 0
    replace ht3 : 3 ∣ a 0 := ht3
    replace ht5 : ¬ 5 ∣ a 0 := ht5
    have hX3 : ¬ 3 ∣ a 1 := fun h => no3 ⟨ht3, h, by omega⟩
    have hY3 : ¬ 3 ∣ a 2 := fun h => no3 ⟨ht3, by omega, h⟩
    have cls := hlab r (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) hr g2 g3 g1 (by omega) hX3 hY3 ht3 ht5
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · replace ht3 : 3 ∣ a 1 := ht3
    replace ht5 : ¬ 5 ∣ a 1 := ht5
    have hX3 : ¬ 3 ∣ a 0 := fun h => no3 ⟨h, ht3, by omega⟩
    have hY3 : ¬ 3 ∣ a 2 := fun h => no3 ⟨by omega, ht3, h⟩
    have cls := hlab r (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) hr g1 g3 g2 (by omega) hX3 hY3 ht3 ht5
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · replace ht3 : 3 ∣ a 2 := ht3
    replace ht5 : ¬ 5 ∣ a 2 := ht5
    have hX3 : ¬ 3 ∣ a 0 := fun h => no3 ⟨h, by omega, ht3⟩
    have hY3 : ¬ 3 ∣ a 1 := fun h => no3 ⟨by omega, h, ht3⟩
    have cls := hlab r (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) hr g1 g2 g3 hs3 hX3 hY3 ht3 ht5
      (fun ψ hψ η hodd => HD ψ hψ η hodd) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

theorem hP_KcJ1 (hlab : KcJ1Lab) (r : ℕ) (hr : 2 ≤ r) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 1 * 3 ^ 1))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t ∧ a t % 2 = 0)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ r * (2 ^ 1 * 3 ^ 1)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ r * (2 ^ 1 * 3 ^ 1)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 2 * (5 ^ r * 3 ^ 1) := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have h1 : (1 : DirichletCharacter ℂ (2 ^ 1)) (-1) = 1 := MulChar.one_apply isUnit_one.neg
  have HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ 1),
      ψ (-1) * η (-1) = -1 →
      (e 0 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (a 0) +
      (e 1 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (a 1) +
      (e 2 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (a 2) = 0 := by
    intro ψ hψ η hodd
    have hodd' : (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)).Odd := by
      show (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (-1) = -1
      rw [chi_neg_one, chi_neg_one, h1, one_mul]; exact hodd
    have := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he _ hodd'
    simpa [Fin.sum_univ_three] using this
  have hnot_all_even : ¬ (a 0 % 2 = 0 ∧ a 1 % 2 = 0 ∧ a 2 % 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    have : 2 ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (by omega) (Nat.dvd_gcd (by omega) (by omega))
    rw [hgcd] at this
    omega
  have g1 := hpos 0
  have g2 := hpos 1
  have g3 := hpos 2
  intro j' hx
  rw [class_sum_eq a e j' hx]
  have gcd_p1 : Nat.gcd (Nat.gcd (a 1) (a 2)) (a 0) = 1 := by rw [Nat.gcd_comm, hgcd]
  have gcd_p2 : Nat.gcd (Nat.gcd (a 0) (a 2)) (a 1) = 1 := by
    rw [Nat.gcd_assoc, Nat.gcd_comm (a 2) (a 1), hgcd]
  have gcd_p0 : Nat.gcd (Nat.gcd (a 0) (a 1)) (a 2) = 1 := by rw [Nat.gcd_assoc, hgcd]
  have hpar : (a 0 % 2 = 1 ∧ a 1 % 2 = 1 ∧ a 2 % 2 = 0) ∨ (a 0 % 2 = 1 ∧ a 1 % 2 = 0 ∧ a 2 % 2 = 1) ∨
      (a 0 % 2 = 0 ∧ a 1 % 2 = 1 ∧ a 2 % 2 = 1) := by omega
  obtain ⟨t, ht5, ht3, hte⟩ := hT
  rcases hpar with ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩
  · have ht : t = 2 := by
      fin_cases t
      · exfalso; have : a 0 % 2 = 0 := hte; omega
      · exfalso; have : a 1 % 2 = 0 := hte; omega
      · rfl
    subst ht
    have cls := hlab r (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) hr h0 h1' h2 g1 g2 g3 hs3 gcd_p0 ht3 ht5
      (fun ψ hψ η hodd => HD ψ hψ η hodd) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have ht : t = 1 := by
      fin_cases t
      · exfalso; have : a 0 % 2 = 0 := hte; omega
      · rfl
      · exfalso; have : a 2 % 2 = 0 := hte; omega
    subst ht
    have cls := hlab r (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) hr h0 h2 h1' g1 g3 g2 (by omega) gcd_p2 ht3 ht5
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have ht : t = 0 := by
      fin_cases t
      · rfl
      · exfalso; have : a 1 % 2 = 0 := hte; omega
      · exfalso; have : a 2 % 2 = 0 := hte; omega
    subst ht
    have cls := hlab r (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) hr h1' h2 h0 g2 g3 g1 (by omega) gcd_p1 ht3 ht5
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

theorem hP_D3 (hlab : D3Lab) (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 1 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ j)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ 1 * (2 ^ 1 * 3 ^ j)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 2 * (5 ^ 1 * 3 ^ j) := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have h1 : (1 : DirichletCharacter ℂ (2 ^ 1)) (-1) = 1 := MulChar.one_apply isUnit_one.neg
  have HD : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      (e 0 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (a 0) +
      (e 1 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (a 1) +
      (e 2 : ℂ) * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (a 2) = 0 := by
    intro ψ hψ η hodd
    have hodd' : (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)).Odd := by
      show (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (-1) = -1
      rw [chi_neg_one, chi_neg_one, h1, one_mul]; exact hodd
    have := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he _ hodd'
    simpa [Fin.sum_univ_three] using this
  have hnot_all_even : ¬ (a 0 % 2 = 0 ∧ a 1 % 2 = 0 ∧ a 2 % 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    have : 2 ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (by omega) (Nat.dvd_gcd (by omega) (by omega))
    rw [hgcd] at this
    omega
  have g1 := hpos 0
  have g2 := hpos 1
  have g3 := hpos 2
  intro j' hx
  rw [class_sum_eq a e j' hx]
  have gcd_p1 : Nat.gcd (Nat.gcd (a 1) (a 2)) (a 0) = 1 := by rw [Nat.gcd_comm, hgcd]
  have gcd_p2 : Nat.gcd (Nat.gcd (a 0) (a 2)) (a 1) = 1 := by
    rw [Nat.gcd_assoc, Nat.gcd_comm (a 2) (a 1), hgcd]
  have gcd_p0 : Nat.gcd (Nat.gcd (a 0) (a 1)) (a 2) = 1 := by rw [Nat.gcd_assoc, hgcd]
  have hpar : (a 0 % 2 = 1 ∧ a 1 % 2 = 1 ∧ a 2 % 2 = 0) ∨ (a 0 % 2 = 1 ∧ a 1 % 2 = 0 ∧ a 2 % 2 = 1) ∨
      (a 0 % 2 = 0 ∧ a 1 % 2 = 1 ∧ a 2 % 2 = 1) := by omega
  obtain ⟨t, ht5, ht3⟩ := hT
  rcases hpar with ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩
  · have hT' : (3 ∣ a 0 ∧ ¬ 5 ∣ a 0) ∨ (3 ∣ a 1 ∧ ¬ 5 ∣ a 1) ∨ (3 ∣ a 2 ∧ ¬ 5 ∣ a 2) := by
      fin_cases t
      · exact Or.inl ⟨ht3, ht5⟩
      · exact Or.inr (Or.inl ⟨ht3, ht5⟩)
      · exact Or.inr (Or.inr ⟨ht3, ht5⟩)
    have cls := hlab j (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) hj h0 h1' h2 g1 g2 g3 hs3 gcd_p0 hT'
      (fun ψ hψ η hodd => HD ψ hψ η hodd) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have hT' : (3 ∣ a 0 ∧ ¬ 5 ∣ a 0) ∨ (3 ∣ a 2 ∧ ¬ 5 ∣ a 2) ∨ (3 ∣ a 1 ∧ ¬ 5 ∣ a 1) := by
      fin_cases t
      · exact Or.inl ⟨ht3, ht5⟩
      · exact Or.inr (Or.inr ⟨ht3, ht5⟩)
      · exact Or.inr (Or.inl ⟨ht3, ht5⟩)
    have cls := hlab j (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) hj h0 h2 h1' g1 g3 g2 (by omega) gcd_p2 hT'
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have hT' : (3 ∣ a 1 ∧ ¬ 5 ∣ a 1) ∨ (3 ∣ a 2 ∧ ¬ 5 ∣ a 2) ∨ (3 ∣ a 0 ∧ ¬ 5 ∣ a 0) := by
      fin_cases t
      · exact Or.inr (Or.inr ⟨ht3, ht5⟩)
      · exact Or.inl ⟨ht3, ht5⟩
      · exact Or.inr (Or.inl ⟨ht3, ht5⟩)
    have cls := hlab j (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) hj h1' h2 h0 g2 g3 g1 (by omega) gcd_p1 hT'
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

theorem lemmaS5_KbJ1 (hlab : KbJ1Lab) (r : ℕ) (hr : 2 ≤ r) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 0 * 3 ^ 1))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t) :
    relSpace (5 ^ r * (2 ^ 0 * 3 ^ 1)) a = trivSpace (5 ^ r * (2 ^ 0 * 3 ^ 1)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_KbJ1 hlab r hr a hpos hsum hgcd hT e he j' hj')

theorem lemmaS5_KcJ1 (hlab : KcJ1Lab) (r : ℕ) (hr : 2 ≤ r) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 1 * 3 ^ 1))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t ∧ a t % 2 = 0) :
    relSpace (5 ^ r * (2 ^ 1 * 3 ^ 1)) a = trivSpace (5 ^ r * (2 ^ 1 * 3 ^ 1)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_KcJ1 hlab r hr a hpos hsum hgcd hT e he j' hj')

theorem lemmaS5_D3 (hlab : D3Lab) (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 1 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t) :
    relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ j)) a = trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_D3 hlab j hj a hpos hsum hgcd hT e he j' hj')

open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

theorem partKb3Open_of_lab (hlab : KbJ1Lab) : Erdos634.GA2SN.PartKb3Open := by
  intro D n a i j k hn hgcd ha e hΦ
  obtain ⟨hi, hk, hj, hne, hT⟩ := hΦ
  subst hi; subst hj
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hn' : n = 5 ^ k * (2 ^ 0 * 3 ^ 1) := by rw [e]; ring
  have hSn : relSpace n a = trivSpace n a := by
    subst hn'
    exact lemmaS5_KbJ1 hlab k hk a hpos hsum hgcd hT
  have h7 : 7 ≤ n := by
    have h25 : 25 ≤ 5 ^ k := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [hn']; nlinarith
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

theorem partKc3Open_of_lab (hlab : KcJ1Lab) : Erdos634.GA2ST.PartKc3Open := by
  intro D n a i j k hn hgcd ha e hΦ
  obtain ⟨hi, hk, hj, hT⟩ := hΦ
  subst hi; subst hj
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hn' : n = 5 ^ k * (2 ^ 1 * 3 ^ 1) := by rw [e]; ring
  have hSn : relSpace n a = trivSpace n a := by
    subst hn'
    exact lemmaS5_KcJ1 hlab k hk a hpos hsum hgcd hT
  have h7 : 7 ≤ n := by
    have h25 : 25 ≤ 5 ^ k := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [hn']; nlinarith
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

theorem partD3_of_lab (hlab : D3Lab) : Erdos634.GA2QG.PartD3 := by
  intro D n a i j k hn hgcd ha e hΦ
  obtain ⟨hi, hk, hj, hne, hT⟩ := hΦ
  subst hi; subst hk
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hn' : n = 5 ^ 1 * (2 ^ 1 * 3 ^ j) := by rw [e]; ring
  have hSn : relSpace n a = trivSpace n a := by
    subst hn'
    exact lemmaS5_D3 hlab j hj a hpos hsum hgcd hT
  have h7 : 7 ≤ n := by
    have h9 : 9 ≤ 3 ^ j := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    rw [hn']; nlinarith
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

/-- the three remaining atoms as ONE hypothesis -/
def GapA2Atoms : Prop := D3Lab ∧ KbJ1Lab ∧ KcJ1Lab

theorem gapA2_of_atoms (R : GapA2Atoms) : Erdos634.CaseA.R0c15.GapA2 :=
  Erdos634.GA2SU.gapA2_of_residual_k (partD3_of_lab R.1) (partKb3Open_of_lab R.2.1) (partKc3Open_of_lab R.2.2)

end Erdos634.GA2SY

#print axioms Erdos634.GA2SY.hP_KbJ1
#print axioms Erdos634.GA2SY.hP_KcJ1
#print axioms Erdos634.GA2SY.hP_D3
#print axioms Erdos634.GA2SY.partKb3Open_of_lab
#print axioms Erdos634.GA2SY.partKc3Open_of_lab
#print axioms Erdos634.GA2SY.partD3_of_lab
#print axioms Erdos634.GA2SY.gapA2_of_atoms
