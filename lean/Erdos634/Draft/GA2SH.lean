/-
GA2S, atom H: Lemma S' and the slice for Prop K-a, and `PartKa`.
  `hP_Ka` / `lemmaS5_Ka`  : relSpace n a = trivSpace n a for n = 5^r * (4 * 3^j), r >= 2, j >= 1, every primitive positive 3-tile.
  `gapA2_slice_Ka`        : no CongruentDissection of N = 15 with model angles a_k pi / n, gcd(a) = 1, n = 5^r * (2^2 * 3^j), r >= 2, j >= 1.
  `partKa`                : `GA2QG.PartKa` (i = 2, k >= 2, j >= 1).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SG
import Erdos634.Draft.GA2QG

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SH

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2NP7 (chi_neg_one class_sum_eq cast_ite3)
open Erdos634.GA2SE Erdos634.GA2SG Erdos634.GA2SC

theorem hP_Ka (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 2 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ r * (2 ^ 2 * 3 ^ j)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ r * (2 ^ 2 * 3 ^ j)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 4 * (5 ^ r * 3 ^ j) := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have H3 : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
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
  have hm0 := m0_odd_r r j
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
  · have cls := theoremKa_lab r j hr hj (a 0) (a 1) (a 2) (e 0) (e 1) (e 2) h0 h1 h2 g1 g2 g3 hs3 gcd_p0
      (fun ψ hψ η2 η3 hodd => H3 ψ hψ η2 η3 hodd) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremKa_lab r j hr hj (a 0) (a 2) (a 1) (e 0) (e 2) (e 1) h0 h2 h1 g1 g3 g2 (by omega) gcd_p2
      (fun ψ hψ η2 η3 hodd => by have := H3 ψ hψ η2 η3 hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremKa_lab r j hr hj (a 1) (a 2) (a 0) (e 1) (e 2) (e 0) h1 h2 h0 g2 g3 g1 (by omega) gcd_p1
      (fun ψ hψ η2 η3 hodd => by have := H3 ψ hψ η2 η3 hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key


/-- **Lemma S' at p = 5 for n = 5^r * 4 * 3^j, r >= 2, j >= 1** (Prop K-a). -/
theorem lemmaS5_Ka (r j : ℕ) (hr : 2 ≤ r) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ 2 * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (5 ^ r * (2 ^ 2 * 3 ^ j)) a = trivSpace (5 ^ r * (2 ^ 2 * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => hP_Ka r j hr hj a hpos hsum hgcd e he j' hj')

open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

/-- **The Prop K-a slice of GapA2 (N = 15, Case A):** n = 5^r * (4 * 3^j), r >= 2, j >= 1. -/
theorem gapA2_slice_Ka (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hform : ∃ r j : ℕ, 2 ≤ r ∧ 1 ≤ j ∧ n = 5 ^ r * (2 ^ 2 * 3 ^ j)) : False := by
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  obtain ⟨r, j, hr, hj, hnj⟩ := hform
  have hSn : relSpace n a = trivSpace n a := by
    subst hnj
    exact lemmaS5_Ka r j hr hj a hpos hsum hgcd
  have h7 : 7 ≤ n := by
    have h25 : 25 ≤ 5 ^ r := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    have h3 : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    rw [hnj]
    nlinarith [Nat.mul_le_mul h25 (Nat.mul_le_mul (le_refl (2 ^ 2)) h3)]
  exact r0c_core15 D rfl hn a ha hSn h7 Erdos634.Draft.Chain15.lemmaH15_holds

/-- **`PartKa` (Prop K-a): i = 2, k >= 2, j >= 1.** -/
theorem partKa : Erdos634.GA2QG.PartKa := by
  intro D n a i j k hn hgcd ha e hΦ
  obtain ⟨rfl, hk, hj⟩ := hΦ
  exact gapA2_slice_Ka D n a hn hgcd ha ⟨k, j, hk, hj, by rw [e]; ring⟩

end Erdos634.GA2SH

#print axioms Erdos634.GA2SH.hP_Ka
#print axioms Erdos634.GA2SH.lemmaS5_Ka
#print axioms Erdos634.GA2SH.gapA2_slice_Ka
#print axioms Erdos634.GA2SH.partKa
