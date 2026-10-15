/-
GA2P, assembly: Lemma S' (R(a) = R_0(a)) for n = 5 * 3^j (i = 0, Theorem C) and n = 5 * 4 * 3^j (i = 2, Theorem B), j >= 2,
and the slice theorem `gapA2_slice_i02` (the i in {0, 2}, r = 1 slices of GapA2 at N = 15).
  `lemmaS5_i0` / `lemmaS5_i2` : relSpace n a = trivSpace n a for every primitive positive 3-tile of n.
  `gapA2_slice_i02`           : no CongruentDissection of N = 15 with model angles a_k pi / n, gcd(a) = 1, n = 5 * 3^j or 5 * 4 * 3^j, j >= 2.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PG
import Erdos634.Draft.GA2NSlice

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PH

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2PD Erdos634.GA2PF Erdos634.GA2PG
open Erdos634.GA2NP7 (chi_neg_one class_sum_eq cast_ite3)

theorem hP_i0 (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 0 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ 1 * (2 ^ 0 * 3 ^ j)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ 1 * (2 ^ 0 * 3 ^ j)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 5 * 3 ^ j := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have HCe : HC j a (fun t => (e t : ℂ)) := by
    intro ψ hψ η2 η3 hodd
    have hodd' : (chi ψ (chi η2 η3)).Odd := by
      show (chi ψ (chi η2 η3)) (-1) = -1
      rw [chi_neg_one, chi_neg_one, ← mul_assoc]; exact hodd
    have := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he _ hodd'
    simpa using this
  intro j' hj'
  have := theoremC_classes j hj a (fun t => (e t : ℂ)) hpos hs3 hgcd HCe j' hj'
  beta_reduce at this
  exact_mod_cast this


theorem hP_i2 (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 2 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ 1 * (2 ^ 2 * 3 ^ j)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ 1 * (2 ^ 2 * 3 ^ j)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 4 * (5 * 3 ^ j) := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have H3 : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ 2), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (e 0 : ℂ) * bracket (chi ψ (chi η2 η3)) (a 0) + (e 1 : ℂ) * bracket (chi ψ (chi η2 η3)) (a 1) +
          (e 2 : ℂ) * bracket (chi ψ (chi η2 η3)) (a 2) = 0 := by
    intro ψ hψ η2 η3 hodd
    have hodd' : (chi ψ (chi η2 η3)).Odd := by
      show (chi ψ (chi η2 η3)) (-1) = -1
      rw [chi_neg_one, chi_neg_one, ← mul_assoc]; exact hodd
    have := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he _ hodd'
    simpa [Fin.sum_univ_three] using this
  have hnot_all_even : ¬ (a 0 % 2 = 0 ∧ a 1 % 2 = 0 ∧ a 2 % 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    have : 2 ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (by omega) (Nat.dvd_gcd (by omega) (by omega))
    rw [hgcd] at this
    omega
  have hm0 := m0_odd j
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
  rcases hpar with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have cls := theoremB_lab j hj (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) h0 h1 h2 g1 g2 g3 hs3 gcd_p0
      (fun ψ hψ η2 η3 hodd => H3 ψ hψ η2 η3 hodd) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremB_lab j hj (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) h0 h2 h1 g1 g3 g2 (by omega) gcd_p2
      (fun ψ hψ η2 η3 hodd => by have := H3 ψ hψ η2 η3 hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremB_lab j hj (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) h1 h2 h0 g2 g3 g1 (by omega) gcd_p1
      (fun ψ hψ η2 η3 hodd => by have := H3 ψ hψ η2 η3 hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

/-- **Lemma S' at p = 5 for n = 5 * 3^j, j >= 2** (Theorem C). -/
theorem lemmaS5_i0 (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 0 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (5 ^ 1 * (2 ^ 0 * 3 ^ j)) a = trivSpace (5 ^ 1 * (2 ^ 0 * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_i0 j hj a hpos hsum hgcd e he j' hj')

/-- **Lemma S' at p = 5 for n = 5 * 4 * 3^j, j >= 2** (Theorem B). -/
theorem lemmaS5_i2 (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ 1 * (2 ^ 2 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (5 ^ 1 * (2 ^ 2 * 3 ^ j)) a = trivSpace (5 ^ 1 * (2 ^ 2 * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_i2 j hj a hpos hsum hgcd e he j' hj')

open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

/-- **The i in {0, 2}, r = 1 slices of GapA2 (N = 15, Case A):** n = 5 * 3^j or n = 5 * 4 * 3^j with j >= 2. -/
theorem gapA2_slice_i02 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hform : (∃ j : ℕ, 2 ≤ j ∧ n = 5 * 3 ^ j) ∨ (∃ j : ℕ, 2 ≤ j ∧ n = 5 * (2 ^ 2 * 3 ^ j))) : False := by
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have h3j : ∀ j : ℕ, 2 ≤ j → 9 ≤ 3 ^ j := fun j hj => by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  rcases hform with ⟨j, hj, hnj⟩ | ⟨j, hj, hnj⟩
  · have hSn : relSpace n a = trivSpace n a := by
      have hn' : n = 5 ^ 1 * (2 ^ 0 * 3 ^ j) := by rw [hnj]; norm_num
      subst hn'
      exact lemmaS5_i0 j hj a hpos hsum hgcd
    have h7 : 7 ≤ n := by have := h3j j hj; omega
    exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds
  · have hSn : relSpace n a = trivSpace n a := by
      have hn' : n = 5 ^ 1 * (2 ^ 2 * 3 ^ j) := by rw [hnj]; norm_num
      subst hn'
      exact lemmaS5_i2 j hj a hpos hsum hgcd
    have h7 : 7 ≤ n := by have := h3j j hj; omega
    exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

end Erdos634.GA2PH

#print axioms Erdos634.GA2PH.hP_i0
#print axioms Erdos634.GA2PH.hP_i2
#print axioms Erdos634.GA2PH.lemmaS5_i0
#print axioms Erdos634.GA2PH.lemmaS5_i2
#print axioms Erdos634.GA2PH.gapA2_slice_i02
