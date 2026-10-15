/-
GA2S, atom N: Lemma S' / slice / `PartKb3` for j >= 2 (i = 0, k >= 2, an entry divisible by 3 and not by 5).
  `hP_Kb3`, `lemmaS5_Kb3` : relSpace n a = trivSpace n a for n = 5^r * 3^j (r >= 2, j >= 2) and a tile with an entry T, 5 !| T, 3 | T.
  `gapA2_slice_Kb3`       : the corresponding slice of GapA2.
  `PartKb3Open`           : the REMAINING part of PartKb3: j = 1 (n = 3 * 5^k, k >= 3, T = 3t).
  `partKb3_of_open`       : PartKb3Open -> PartKb3.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SM

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SN

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2NP7 (chi_neg_one class_sum_eq cast_ite3)
open Erdos634.GA2SL Erdos634.GA2SM

theorem hP_Kb3 (r j : ℕ) (hr : 2 ≤ r) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 0 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ r * (2 ^ 0 * 3 ^ j)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ r * (2 ^ 0 * 3 ^ j)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 5 ^ r * 3 ^ j := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have h3N : 3 ∣ 5 ^ r * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
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
    have cls := kb_lab r j hr hj (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) g2 g3 g1 (by omega) hX3 hY3 ht3 ht5
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · replace ht3 : 3 ∣ a 1 := ht3
    replace ht5 : ¬ 5 ∣ a 1 := ht5
    have hX3 : ¬ 3 ∣ a 0 := fun h => no3 ⟨h, ht3, by omega⟩
    have hY3 : ¬ 3 ∣ a 2 := fun h => no3 ⟨by omega, ht3, h⟩
    have cls := kb_lab r j hr hj (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) g1 g3 g2 (by omega) hX3 hY3 ht3 ht5
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · replace ht3 : 3 ∣ a 2 := ht3
    replace ht5 : ¬ 5 ∣ a 2 := ht5
    have hX3 : ¬ 3 ∣ a 0 := fun h => no3 ⟨h, by omega, ht3⟩
    have hY3 : ¬ 3 ∣ a 1 := fun h => no3 ⟨by omega, h, ht3⟩
    have cls := kb_lab r j hr hj (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) g1 g2 g3 hs3 hX3 hY3 ht3 ht5
      (fun ψ hψ η hodd => HD ψ hψ η hodd) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

theorem lemmaS5_Kb3 (r j : ℕ) (hr : 2 ≤ r) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 0 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t) :
    relSpace (5 ^ r * (2 ^ 0 * 3 ^ j)) a = trivSpace (5 ^ r * (2 ^ 0 * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_Kb3 r j hr hj a hpos hsum hgcd hT e he j' hj')

open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

theorem gapA2_slice_Kb3 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (r j : ℕ) (hr : 2 ≤ r) (hj : 2 ≤ j) (hnj : n = 5 ^ r * 3 ^ j)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t) : False := by
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hn' : n = 5 ^ r * (2 ^ 0 * 3 ^ j) := by rw [hnj]; norm_num
  have hSn : relSpace n a = trivSpace n a := by
    subst hn'
    exact lemmaS5_Kb3 r j hr hj a hpos hsum hgcd hT
  have h7 : 7 ≤ n := by
    have h25 : 25 ≤ 5 ^ r := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    have h3 : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hnj]
    nlinarith [Nat.mul_le_mul h25 h3]
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

/-- The REMAINING part of `PartKb3`: j = 1 (n = 3 * 5^k, k >= 3), an entry T = 3t with 5 !| t. -/
def PartKb3Open : Prop :=
  Erdos634.GA2QG.GapA2On (fun i j k a => i = 0 ∧ 2 ≤ k ∧ j = 1 ∧ (i, j, k) ≠ (0, 1, 2) ∧
    ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)

theorem partKb3_of_open (h : PartKb3Open) : Erdos634.GA2QG.PartKb3 := by
  intro D n a i j k hn hgcd ha e hΦ
  obtain ⟨hi, hk, hj, hne, hT⟩ := hΦ
  by_cases hj2 : 2 ≤ j
  · subst hi
    exact gapA2_slice_Kb3 D n a hn hgcd ha k j hk hj2 (by rw [e]; ring) hT
  · exact h D n a i j k hn hgcd ha e ⟨hi, hk, by omega, hne, hT⟩

end Erdos634.GA2SN

#print axioms Erdos634.GA2SN.hP_Kb3
#print axioms Erdos634.GA2SN.lemmaS5_Kb3
#print axioms Erdos634.GA2SN.gapA2_slice_Kb3
#print axioms Erdos634.GA2SN.partKb3_of_open
