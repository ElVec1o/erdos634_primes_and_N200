/-
Prop D, part 5: from `relSpace` to the class sums (hP_i1), Lemma S' at n = 5 * (2 * 3^j) for tiles with no entry of I divisible by 3,
and the slice `gapA2_slice_D`.

`gapA2_slice_D` : no CongruentDissection of N = 15 whose model has angles a_k pi / n, gcd(a) = 1, n = 5 * (2 * 3^j) (j >= 2),
  such that every entry of a prime to 5 is prime to 3 (Prop D's hypothesis: "no entry of I divisible by 3").
The tiles with an entry divisible by 3 and not by 5 are not covered.
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QD4
import Erdos634.Draft.GA2PH

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2QD5

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2NP7 (chi_neg_one class_sum_eq cast_ite3)
open Erdos634.GA2QD4

theorem theoremD_lab' (j : ℕ) (hj : 2 ≤ j) (P Q S : ℕ) (eP eQ eS : ℂ)
    (hP2 : P % 2 = 1) (hQ2 : Q % 2 = 1) (hS2 : S % 2 = 0)
    (gP : 0 < P) (gQ : 0 < Q) (gS : 0 < S)
    (hsum : P + Q + S = 2 * (5 ^ 1 * 3 ^ j))
    (h5 : ¬ (5 ∣ P ∧ 5 ∣ Q ∧ 5 ∣ S))
    (h3P : ¬ 5 ∣ P → ¬ 3 ∣ P) (h3Q : ¬ 5 ∣ Q → ¬ 3 ∣ Q) (h3S : ¬ 5 ∣ S → ¬ 3 ∣ S)
    (HD : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) P +
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) Q +
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) S = 0) :
    ∀ x : ℕ, ¬ 5 ∣ x → (if P = x then eP else 0) + (if Q = x then eQ else 0) + (if S = x then eS else 0) = 0 := by
  obtain ⟨b, rfl⟩ : ∃ b, S = 2 * b := ⟨S / 2, by omega⟩
  exact theoremD_lab j hj P Q b eP eQ eS hP2 hQ2 gP gQ gS hsum h5 h3P h3Q h3S HD

theorem hP_i1 (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 1 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t)
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
  have hno5 : ¬ (5 ∣ a 0 ∧ 5 ∣ a 1 ∧ 5 ∣ a 2) := by
    rintro ⟨h0, h1, h2⟩
    have : 5 ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h2)
    rw [hgcd] at this
    omega
  have g1 := hpos 0
  have g2 := hpos 1
  have g3 := hpos 2
  intro j' hx
  rw [class_sum_eq a e j' hx]
  have hpar : (a 0 % 2 = 1 ∧ a 1 % 2 = 1 ∧ a 2 % 2 = 0) ∨ (a 0 % 2 = 1 ∧ a 1 % 2 = 0 ∧ a 2 % 2 = 1) ∨
      (a 0 % 2 = 0 ∧ a 1 % 2 = 1 ∧ a 2 % 2 = 1) := by omega
  rcases hpar with ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩
  · have cls := theoremD_lab' j hj (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) h0 h1' h2 g1 g2 g3 hs3
      (by tauto) (h3 0) (h3 1) (h3 2) HD (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremD_lab' j hj (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) h0 h2 h1' g1 g3 g2 (by omega)
      (by tauto) (h3 0) (h3 2) (h3 1)
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremD_lab' j hj (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) h1' h2 h0 g2 g3 g1 (by omega)
      (by tauto) (h3 1) (h3 2) (h3 0)
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

/-- **Lemma S' at p = 5 for n = 5 * (2 * 3^j), j >= 2, for tiles with no entry of I divisible by 3** (Proposition D). -/
theorem lemmaS5_i1 (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 1 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t) :
    relSpace (5 ^ 1 * (2 ^ 1 * 3 ^ j)) a = trivSpace (5 ^ 1 * (2 ^ 1 * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_i1 j hj a hpos hsum hgcd h3 e he j' hj')

open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

/-- **The i = 1, r = 1, j >= 2 slice of GapA2 for tiles with no entry of I divisible by 3.** -/
theorem gapA2_slice_D (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hform : ∃ j : ℕ, 2 ≤ j ∧ n = 5 * (2 * 3 ^ j))
    (h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t) : False := by
  obtain ⟨j, hj, hnj⟩ := hform
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have h3j : 9 ≤ 3 ^ j := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hSn : relSpace n a = trivSpace n a := by
    have hn' : n = 5 ^ 1 * (2 ^ 1 * 3 ^ j) := by rw [hnj]; norm_num
    subst hn'
    exact lemmaS5_i1 j hj a hpos hsum hgcd h3
  have h7 : 7 ≤ n := by omega
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

end Erdos634.GA2QD5

#print axioms Erdos634.GA2QD5.theoremD_lab'
#print axioms Erdos634.GA2QD5.hP_i1
#print axioms Erdos634.GA2QD5.lemmaS5_i1
#print axioms Erdos634.GA2QD5.gapA2_slice_D
