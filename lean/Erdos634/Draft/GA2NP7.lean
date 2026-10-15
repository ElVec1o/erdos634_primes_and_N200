/-
**P7 assembly at p = 5 for i >= 3**:  Lemma S' (R(a) = R_0(a)) for the tiles of n = 5^r 2^(k+3) 3^j, r, j >= 1, k >= 0.

`theoremA_classes` : Theorem A in class form (for every x prime to 5 the class sum over the entries equal to x is 0).
`theoremA_hP`      : for e in R(a) (the sawtooth relation space `LemmaS.relSpace`), via `LemmaSCCrit.mem_relSpace_iff_odd` restricted to
                     chi = psi (eta2 x eta3), the hypothesis `hP` of `LemmaSR.lemmaR` at p = 5.
`lemmaS5_i3`       : relSpace n a = trivSpace n a for n = 5^r (2^(k+3) 3^j), a a primitive 3-tile, via `LemmaSR.lemmaR`.
This is exactly the hypothesis `hSn` of `CaseAN15.r0c_core15` for those n (it does NOT discharge GapA2: the families i <= 2, n = 15, 30, 60
remain).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NT
import Erdos634.Draft.LemmaSR
import Erdos634.Draft.LemmaSCCrit

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NP7

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.GA2NT Erdos634.GA2NB2

theorem chi_neg_one {p r m : ℕ} [Fact p.Prime] [NeZero m] (ψ : DirichletCharacter ℂ (p ^ r))
    (η : DirichletCharacter ℂ m) :
    (chi ψ η) (-1) = ψ (-1) * η (-1) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ r * m) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  show (changeLevel (Nat.dvd_mul_right (p ^ r) m) ψ * changeLevel (Nat.dvd_mul_left m (p ^ r)) η) (-1) = _
  rw [MulChar.mul_apply, changeLevel_neg_one, changeLevel_neg_one]

theorem theoremA_classes (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hSe : 2 ∣ aS) (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 2 ^ (k + 3) * (3 ^ j * 5 ^ r))
    (hgcd : Nat.gcd (Nat.gcd aP aQ) aS = 1)
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + eQ * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aP = x then eP else 0) + (if aQ = x then eQ else 0) + (if aS = x then eS else 0) = 0 := by
  obtain ⟨C1P, C1Q, C1S⟩ := theoremA_lab r k j hr hj aP aQ aS eP eQ eS hPo hQo hSe hP0 hQ0 hS0 hsum hgcd H
  have hPo' : aP % 2 = 1 := Nat.odd_iff.1 hPo
  have hQo' : aQ % 2 = 1 := Nat.odd_iff.1 hQo
  have hSP : aS ≠ aP := by intro h; omega
  have hSQ : aS ≠ aQ := by intro h; omega
  intro x hx
  by_cases hPx : aP = x
  · subst hPx
    have h1 := C1P hx
    by_cases hq : aP = aQ
    · rw [if_pos hq] at h1
      rw [if_pos rfl, if_pos hq.symm, if_neg hSP]
      linear_combination h1
    · rw [if_neg hq] at h1
      rw [if_pos rfl, if_neg (fun h => hq h.symm), if_neg hSP]
      linear_combination h1
  · by_cases hQx : aQ = x
    · subst hQx
      have h1 := C1Q hx
      rw [if_neg (fun h => hPx h.symm)] at h1
      rw [if_neg hPx, if_pos rfl, if_neg hSQ]
      linear_combination h1
    · by_cases hSx : aS = x
      · subst hSx
        rw [if_neg hPx, if_neg hQx, if_pos rfl, C1S hx]; ring
      · rw [if_neg hPx, if_neg hQx, if_neg hSx]; ring

theorem cast_ite3 (p0 p1 p2 : Prop) [Decidable p0] [Decidable p1] [Decidable p2] (q0 q1 q2 : ℚ) :
    ((((if p0 then q0 else 0) + (if p1 then q1 else 0) + (if p2 then q2 else 0) : ℚ)) : ℂ) =
      (if p0 then (q0 : ℂ) else 0) + (if p1 then (q1 : ℂ) else 0) + (if p2 then (q2 : ℂ) else 0) := by
  split_ifs <;> simp

theorem class_sum_eq (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (j' : Fin 3) (hx : ¬ 5 ∣ a j') :
    ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' =
      (if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_three]
  have key : ∀ i : Fin 3, (if ¬ 5 ∣ a i then (if a i = a j' then e i else 0) else 0) =
      (if a i = a j' then e i else 0) := by
    intro i
    by_cases h : a i = a j'
    · simp [h, hx]
    · simp [h]
  rw [key, key, key]

theorem theoremA_hP (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ (k + 3) * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (e : Fin 3 → ℚ) (he : e ∈ relSpace (5 ^ r * (2 ^ (k + 3) * 3 ^ j)) a) :
    ∀ j', ¬ 5 ∣ a j' →
      ∑ k' ∈ (univ.filter (fun k => ¬ 5 ∣ a k)).filter (fun k => a k = a j'), e k' = 0 := by
  haveI : NeZero (5 ^ r * (2 ^ (k + 3) * 3 ^ j)) := ⟨by positivity⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs3 : a 0 + a 1 + a 2 = 2 ^ (k + 3) * (3 ^ j * 5 ^ r) := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    rw [this]; ring
  have H3 : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        (e 0 : ℂ) * bracket (chi ψ (chi η2 η3)) (a 0) + (e 1 : ℂ) * bracket (chi ψ (chi η2 η3)) (a 1) +
          (e 2 : ℂ) * bracket (chi ψ (chi η2 η3)) (a 2) = 0 := by
    intro ψ hψ η2 η3 hodd
    have hodd' : (chi ψ (chi η2 η3)).Odd := by
      show (chi ψ (chi η2 η3)) (-1) = -1
      rw [chi_neg_one, chi_neg_one, ← mul_assoc]; exact hodd
    have := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he _ hodd'
    simpa [Fin.sum_univ_three] using this
  -- parity analysis: exactly two odd entries
  have hn2 : (2 ^ (k + 3) * (3 ^ j * 5 ^ r)) % 2 = 0 := by
    have : 2 ∣ 2 ^ (k + 3) * (3 ^ j * 5 ^ r) := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    omega
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
  rcases hpar with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have cls := theoremA_classes r k j hr hj (a 0) (a 1) (a 2) (e 0) (e 1) (e 2)
      (Nat.odd_iff.2 h0) (Nat.odd_iff.2 h1) (Nat.dvd_of_mod_eq_zero h2) g1 g2 g3 hs3 gcd_p0 H3 (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremA_classes r k j hr hj (a 0) (a 2) (a 1) (e 0) (e 2) (e 1)
      (Nat.odd_iff.2 h0) (Nat.odd_iff.2 h2) (Nat.dvd_of_mod_eq_zero h1) g1 g3 g2 (by omega) gcd_p2
      (fun ψ hψ η2 η3 hodd => by have := H3 ψ hψ η2 η3 hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key
  · have cls := theoremA_classes r k j hr hj (a 1) (a 2) (a 0) (e 1) (e 2) (e 0)
      (Nat.odd_iff.2 h1) (Nat.odd_iff.2 h2) (Nat.dvd_of_mod_eq_zero h0) g2 g3 g1 (by omega) gcd_p1
      (fun ψ hψ η2 η3 hodd => by have := H3 ψ hψ η2 η3 hodd; linear_combination this) (a j') hx
    have key : (((if a 0 = a j' then e 0 else 0) + (if a 1 = a j' then e 1 else 0) +
        (if a 2 = a j' then e 2 else 0) : ℚ) : ℂ) = 0 := by
      rw [cast_ite3]; linear_combination cls
    exact_mod_cast key

/-- **Lemma S' at p = 5 for i >= 3**: R(a) = R_0(a) for every primitive 3-tile of n = 5^r 2^(k+3) 3^j (r, j >= 1). -/
theorem lemmaS5_i3 (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 5 ^ r * (2 ^ (k + 3) * 3 ^ j))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (5 ^ r * (2 ^ (k + 3) * 3 ^ j)) a = trivSpace (5 ^ r * (2 ^ (k + 3) * 3 ^ j)) a :=
  Erdos634.LemmaSR.lemmaR a hpos hsum hgcd (by norm_num : Nat.Prime 5)
    (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _)
    (fun e he j' hj' => theoremA_hP r k j hr hj a hpos hsum hgcd e he j' hj')

/-! ## Witnesses: every hypothesis of `lemmaS5_i3` / `theoremA_lab` is satisfiable, at n = 120, 600, 1800. -/

theorem lemmaS5_witness_120 :
    relSpace (5 ^ 1 * (2 ^ (0 + 3) * 3 ^ 1)) ![67, 7, 46] = trivSpace (5 ^ 1 * (2 ^ (0 + 3) * 3 ^ 1)) ![67, 7, 46] :=
  lemmaS5_i3 1 0 1 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide)

theorem lemmaS5_witness_600 :
    relSpace (5 ^ 2 * (2 ^ (0 + 3) * 3 ^ 1)) ![307, 7, 286] = trivSpace (5 ^ 2 * (2 ^ (0 + 3) * 3 ^ 1)) ![307, 7, 286] :=
  lemmaS5_i3 2 0 1 (by norm_num) le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide)

theorem lemmaS5_witness_1800 :
    relSpace (5 ^ 2 * (2 ^ (0 + 3) * 3 ^ 2)) ![893, 7, 900] = trivSpace (5 ^ 2 * (2 ^ (0 + 3) * 3 ^ 2)) ![893, 7, 900] :=
  lemmaS5_i3 2 0 2 (by norm_num) (by norm_num) _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide)

/-- A tile with a coincidence (a_0 = a_1), where R_0 != 0: the theorem is not just `⊥ = ⊥`. -/
theorem lemmaS5_witness_120_double :
    relSpace (5 ^ 1 * (2 ^ (0 + 3) * 3 ^ 1)) ![1, 1, 118] = trivSpace (5 ^ 1 * (2 ^ (0 + 3) * 3 ^ 1)) ![1, 1, 118] :=
  lemmaS5_i3 1 0 1 le_rfl le_rfl _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide)

theorem trivSpace_ne_bot_120_double :
    trivSpace (5 ^ 1 * (2 ^ (0 + 3) * 3 ^ 1)) ![1, 1, 118] ≠ ⊥ := by
  intro h
  have hv : (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace (5 ^ 1 * (2 ^ (0 + 3) * 3 ^ 1)) ![1, 1, 118] :=
    Submodule.subset_span (Or.inl ⟨0, 1, by decide, by decide, rfl⟩)
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp at this

end Erdos634.GA2NP7

#print axioms Erdos634.GA2NP7.theoremA_classes
#print axioms Erdos634.GA2NP7.theoremA_hP
#print axioms Erdos634.GA2NP7.lemmaS5_i3
#print axioms Erdos634.GA2NP7.lemmaS5_witness_120
#print axioms Erdos634.GA2NP7.lemmaS5_witness_600
#print axioms Erdos634.GA2NP7.lemmaS5_witness_1800
#print axioms Erdos634.GA2NP7.lemmaS5_witness_120_double
#print axioms Erdos634.GA2NP7.trivSpace_ne_bot_120_double
