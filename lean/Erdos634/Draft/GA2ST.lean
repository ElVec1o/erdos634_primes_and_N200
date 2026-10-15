/-
GA2S, atom T: Lemma S' / slice / `PartKc3` for T odd (any j >= 1) and for T even with j >= 2 (i = 1, k >= 2, an entry divisible by 3 and not by 5).
  `hP_Kc3`, `lemmaS5_Kc3` : relSpace n a = trivSpace n a for n = 5^r * (2 * 3^j), r >= 2, j >= 1, and a tile with an entry T (5 !| T, 3 | T)
                            that is odd or has j >= 2.
  `gapA2_slice_Kc3`       : the corresponding slice of GapA2.
  `PartKc3Open`           : the REMAINING part of PartKc3: j = 1 (n = 6 * 5^k) and T = the EVEN entry (3 | S, S = 6 b).
  `partKc3_of_open`       : PartKc3Open -> PartKc3.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SS
import Erdos634.Draft.GA2SN

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2ST

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2NP7 (chi_neg_one class_sum_eq cast_ite3)
open Erdos634.GA2SP Erdos634.GA2SS

theorem hP_Kc3 (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 1 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t ∧ (2 ≤ j ∨ a t % 2 = 1))
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ r * (2 ^ 1 * 3 ^ j)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ r * (2 ^ 1 * 3 ^ j)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 2 * (5 ^ r * 3 ^ j) := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have h1 : (1 : DirichletCharacter ℂ (2 ^ 1)) (-1) = 1 := MulChar.one_apply isUnit_one.neg
  have HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
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
  obtain ⟨t, ht5, ht3, htj⟩ := hT
  have key3 : ∀ (s : Fin 3), True := fun _ => trivial
  rcases hpar with ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩
  · have hT' : (3 ∣ a 0 ∧ ¬ 5 ∣ a 0) ∨ (3 ∣ a 1 ∧ ¬ 5 ∣ a 1) ∨ (3 ∣ a 2 ∧ ¬ 5 ∣ a 2 ∧ 2 ≤ j) := by
      fin_cases t
      · exact Or.inl ⟨ht3, ht5⟩
      · exact Or.inr (Or.inl ⟨ht3, ht5⟩)
      · refine Or.inr (Or.inr ⟨ht3, ht5, ?_⟩)
        rcases htj with h | h
        · exact h
        · exfalso; have : a 2 % 2 = 1 := h; omega
    have cls := kc_lab r j hr hj (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) h0 h1' h2 g1 g2 g3 hs3 gcd_p0 hT'
      (fun ψ hψ η hodd => HD ψ hψ η hodd) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have hT' : (3 ∣ a 0 ∧ ¬ 5 ∣ a 0) ∨ (3 ∣ a 2 ∧ ¬ 5 ∣ a 2) ∨ (3 ∣ a 1 ∧ ¬ 5 ∣ a 1 ∧ 2 ≤ j) := by
      fin_cases t
      · exact Or.inl ⟨ht3, ht5⟩
      · refine Or.inr (Or.inr ⟨ht3, ht5, ?_⟩)
        rcases htj with h | h
        · exact h
        · exfalso; have : a 1 % 2 = 1 := h; omega
      · exact Or.inr (Or.inl ⟨ht3, ht5⟩)
    have cls := kc_lab r j hr hj (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) h0 h2 h1' g1 g3 g2 (by omega) gcd_p2 hT'
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have hT' : (3 ∣ a 1 ∧ ¬ 5 ∣ a 1) ∨ (3 ∣ a 2 ∧ ¬ 5 ∣ a 2) ∨ (3 ∣ a 0 ∧ ¬ 5 ∣ a 0 ∧ 2 ≤ j) := by
      fin_cases t
      · refine Or.inr (Or.inr ⟨ht3, ht5, ?_⟩)
        rcases htj with h | h
        · exact h
        · exfalso; have : a 0 % 2 = 1 := h; omega
      · exact Or.inl ⟨ht3, ht5⟩
      · exact Or.inr (Or.inl ⟨ht3, ht5⟩)
    have cls := kc_lab r j hr hj (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) h1' h2 h0 g2 g3 g1 (by omega) gcd_p1 hT'
      (fun ψ hψ η hodd => by have := HD ψ hψ η hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

theorem lemmaS5_Kc3 (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 1 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t ∧ (2 ≤ j ∨ a t % 2 = 1)) :
    relSpace (5 ^ r * (2 ^ 1 * 3 ^ j)) a = trivSpace (5 ^ r * (2 ^ 1 * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_Kc3 r j hr hj a hpos hsum hgcd hT e he j' hj')

open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

theorem gapA2_slice_Kc3 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (hnj : n = 5 ^ r * (2 * 3 ^ j))
    (hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t ∧ (2 ≤ j ∨ a t % 2 = 1)) : False := by
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hn' : n = 5 ^ r * (2 ^ 1 * 3 ^ j) := by rw [hnj]; norm_num
  have hSn : relSpace n a = trivSpace n a := by
    subst hn'
    exact lemmaS5_Kc3 r j hr hj a hpos hsum hgcd hT
  have h7 : 7 ≤ n := by
    have h25 : 25 ≤ 5 ^ r := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    have h3 : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    rw [hnj]
    nlinarith [Nat.mul_le_mul h25 h3]
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

/-- The REMAINING part of `PartKc3`: j = 1 (n = 6 * 5^k, k >= 2) and the entry divisible by 3 (not by 5) is EVEN. -/
def PartKc3Open : Prop :=
  Erdos634.GA2QG.GapA2On (fun i j k a => i = 1 ∧ 2 ≤ k ∧ j = 1 ∧
    ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t ∧ a t % 2 = 0)

theorem partKc3_of_open (h : PartKc3Open) : Erdos634.GA2QG.PartKc3 := by
  intro D n a i j k hn hgcd ha e hΦ
  obtain ⟨hi, hk, hj, t, ht5, ht3⟩ := hΦ
  subst hi
  by_cases hj2 : 2 ≤ j
  · exact gapA2_slice_Kc3 D n a hn hgcd ha k j hk hj (by rw [e]; ring) ⟨t, ht5, ht3, Or.inl hj2⟩
  · by_cases hpar : a t % 2 = 1
    · exact gapA2_slice_Kc3 D n a hn hgcd ha k j hk hj (by rw [e]; ring) ⟨t, ht5, ht3, Or.inr hpar⟩
    · exact h D n a 1 j k hn hgcd ha e ⟨rfl, hk, by omega, t, ht5, ht3, by omega⟩

end Erdos634.GA2ST

#print axioms Erdos634.GA2ST.hP_Kc3
#print axioms Erdos634.GA2ST.lemmaS5_Kc3
#print axioms Erdos634.GA2ST.gapA2_slice_Kc3
#print axioms Erdos634.GA2ST.partKc3_of_open
