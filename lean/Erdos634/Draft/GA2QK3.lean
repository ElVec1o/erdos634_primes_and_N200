/-
GA2Q, K-version of part 4 (i = 1): arithmetic helpers, the hypothesis (A) from the bracket formulas, and the labelled theorem `theoremK_lab`
for n = 2 * 5^r * 3^j, r >= 1, with (r >= 2 or j >= 2) and no entry of I divisible by 3  (r = 1, j >= 2 is Proposition D, GA2QD4).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QK1
import Erdos634.Draft.GA2QK2
import Erdos634.Draft.GA2QD3

open scoped BigOperators
open Finset
open scoped Classical

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Erdos634.GA2QK3

open DirichletCharacter Erdos634.GA2QK2 Erdos634.GA2QP Erdos634.GA2QD3
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)

/-! ### arithmetic helpers -/

theorem dvd_cases (N : ℕ) (hN2 : N % 2 = 1) (x : ℤ) (hx : (N : ℤ) ∣ x) (h1 : -(2 * N : ℤ) < x)
    (h2 : x < 2 * N) (hpar : x % 2 = 0) : x = 0 := by
  obtain ⟨k, hk⟩ := hx
  have hNpos : (0 : ℤ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hk1 : -2 < k := by
    by_contra h
    push Not at h
    nlinarith
  have hk2 : k < 2 := by
    by_contra h
    push Not at h
    nlinarith
  have hN2' : (N : ℤ) % 2 = 1 := by omega
  interval_cases k <;> omega


theorem unit_of_not (r j : ℕ) (x : ℕ) (h5 : ¬ 5 ∣ x) (h3 : ¬ 3 ∣ x) :
    IsUnit ((x : ℕ) : ZMod (5 ^ r * 3 ^ j)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5).symm)
    (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm)

theorem N_odd (r j : ℕ) : (5 ^ r * 3 ^ j) % 2 = 1 := by
  have : (5 ^ r * 3 ^ j) % 2 = ((5 ^ r % 2) * (3 ^ j % 2)) % 2 := Nat.mul_mod _ _ _
  rw [this]
  have h1 : 5 ^ r % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : 3 ^ j % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [h1, h2]

theorem exists_half (r j : ℕ) : ∃ h : ZMod (5 ^ r * 3 ^ j), 2 * h = 1 :=
  (two_unit (N_odd r j)).exists_right_inv

theorem N_ge (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) : 15 ≤ 5 ^ r * 3 ^ j := by
  have h3 : 3 ≤ 3 ^ j := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have h5 : 5 ≤ 5 ^ r := by
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  calc 15 = 5 * 3 := by norm_num
    _ ≤ 5 ^ r * 3 ^ j := Nat.mul_le_mul h5 h3

/-- two odd naturals below 2N congruent mod N are equal (N odd) -/
theorem eq_of_cast_eq (N : ℕ) (hN2 : N % 2 = 1) (P Q : ℕ) (hP : P % 2 = 1) (hQ : Q % 2 = 1)
    (hP' : P < 2 * N) (hQ' : Q < 2 * N) (h : (P : ZMod N) = (Q : ZMod N)) : P = Q := by
  have h1 : ((P : ℤ) : ZMod N) = ((Q : ℤ) : ZMod N) := by exact_mod_cast h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have := dvd_cases N hN2 ((Q : ℤ) - P) h1 (by omega) (by omega) (by omega)
  omega

/-- positive even total below 2N is not divisible by N (N odd) -/
theorem not_neg_cast (N : ℕ) (hN2 : N % 2 = 1) (P Q : ℕ) (hP : P % 2 = 1) (hQ : Q % 2 = 1)
    (hpos : 0 < P + Q) (hlt : P + Q < 2 * N) (h : (P : ZMod N) + (Q : ZMod N) = 0) : False := by
  have h1 : (((P + Q : ℕ) : ℤ) : ZMod N) = 0 := by push_cast; exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have := dvd_cases N hN2 ((P + Q : ℕ) : ℤ) h1 (by omega) (by omega) (by omega)
  omega



/-! ### the four points of a family have distinct images mod M' = 5^(r-1) 3^j -/

theorem four_distinct_gen {R : Type*} [CommRing R] [Nontrivial R] (X h : R) (hX : IsUnit X) (hh : 2 * h = 1)
    (h3 : (3 : R) ≠ 0) :
    X ≠ -X ∧ X ≠ X * h ∧ X ≠ -(X * h) ∧ -X ≠ X * h ∧ -X ≠ -(X * h) ∧ X * h ≠ -(X * h) := by
  have hX0 : X ≠ 0 := hX.ne_zero
  have n3 : (3 : R) * X ≠ 0 := fun e => h3 (hX.mul_left_eq_zero.1 e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; exact hX0 (by linear_combination h * e - X * hh)
  · intro e; exact hX0 (by linear_combination 2 * e + X * hh)
  · intro e; exact n3 (by linear_combination 2 * e - X * hh)
  · intro e; exact n3 (by linear_combination (-2) * e - X * hh)
  · intro e; exact hX0 (by linear_combination (-2) * e + X * hh)
  · intro e; exact hX0 (by linear_combination e - X * hh)

theorem three_ne_zeroM (r j : ℕ) (h : 2 ≤ r ∨ 2 ≤ j) : (3 : ZMod (5 ^ (r - 1) * 3 ^ j)) ≠ 0 := by
  intro h0
  have h' : ((3 : ℕ) : ZMod (5 ^ (r - 1) * 3 ^ j)) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at h'
  have h1 := Nat.le_of_dvd (by norm_num) h'
  have : 5 ≤ 5 ^ (r - 1) * 3 ^ j ∨ 9 ≤ 5 ^ (r - 1) * 3 ^ j := by
    rcases h with hr | hj
    · left
      have : 5 ≤ 5 ^ (r - 1) := by
        calc 5 = 5 ^ 1 := by norm_num
          _ ≤ 5 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
      nlinarith
    · right
      have h9 : 9 ≤ 3 ^ j := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      have : 1 ≤ 5 ^ (r - 1) := Nat.one_le_pow _ _ (by norm_num)
      nlinarith
  omega

/-- the family of an odd entry -/
def famP {M : ℕ} (x h : ZMod M) : Finset (ZMod M) := {x, -x, x * h, -(x * h)}
/-- the family of the even entry -/
def famS {M : ℕ} (b : ZMod M) : Finset (ZMod M) := {b, -b}

theorem fam_card_le_one (r j : ℕ) (h3 : (3 : ZMod (5 ^ (r - 1) * 3 ^ j)) ≠ 0)
    (x h2 : ZMod (5 ^ r * 3 ^ j)) (hx : IsUnit (cM r j x))
    (hh : 2 * h2 = 1) (k : ZMod (5 ^ (r - 1) * 3 ^ j)) :
    ((famP x h2).filter (fun g => cM r j g = k)).card ≤ 1 := by
  haveI : Fact (1 < 5 ^ (r - 1) * 3 ^ j) := ⟨by
    by_contra hcon
    push Not at hcon
    have : 5 ^ (r - 1) * 3 ^ j = 1 := by
      have : 0 < 5 ^ (r - 1) * 3 ^ j := by positivity
      omega
    rw [this] at h3
    exact h3 (Subsingleton.elim _ _)⟩
  have h2' : 2 * cM r j h2 = 1 := by
    have := congrArg (cM r j) hh
    simp only [map_mul, map_one, map_ofNat] at this
    exact this
  have hd := four_distinct_gen (cM r j x) (cM r j h2) hx h2' h3
  rw [Finset.card_le_one]
  intro g hg g' hg'
  have e1 := (Finset.mem_filter.1 hg).2
  have e2 := (Finset.mem_filter.1 hg').2
  have heq : cM r j g = cM r j g' := e1.trans e2.symm
  have m1 := (Finset.mem_filter.1 hg).1
  have m2 := (Finset.mem_filter.1 hg').1
  simp only [famP, Finset.mem_insert, Finset.mem_singleton] at m1 m2
  rcases m1 with rfl | rfl | rfl | rfl <;> rcases m2 with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso; simp only [map_neg, map_mul] at heq
       first
       | exact hd.1 heq | exact hd.1 heq.symm | exact hd.2.1 heq | exact hd.2.1 heq.symm
       | exact hd.2.2.1 heq | exact hd.2.2.1 heq.symm | exact hd.2.2.2.1 heq | exact hd.2.2.2.1 heq.symm
       | exact hd.2.2.2.2.1 heq | exact hd.2.2.2.2.1 heq.symm | exact hd.2.2.2.2.2 heq
       | exact hd.2.2.2.2.2 heq.symm)

theorem famS_card_le_one (r j : ℕ) (h3 : (3 : ZMod (5 ^ (r - 1) * 3 ^ j)) ≠ 0)
    (b h2 : ZMod (5 ^ r * 3 ^ j)) (hb : IsUnit (cM r j b))
    (hh : 2 * h2 = 1) (k : ZMod (5 ^ (r - 1) * 3 ^ j)) :
    ((famS b).filter (fun g => cM r j g = k)).card ≤ 1 := by
  haveI : Fact (1 < 5 ^ (r - 1) * 3 ^ j) := ⟨by
    by_contra hcon
    push Not at hcon
    have : 5 ^ (r - 1) * 3 ^ j = 1 := by
      have : 0 < 5 ^ (r - 1) * 3 ^ j := by positivity
      omega
    rw [this] at h3
    exact h3 (Subsingleton.elim _ _)⟩
  have h2' : 2 * cM r j h2 = 1 := by
    have := congrArg (cM r j) hh
    simp only [map_mul, map_one, map_ofNat] at this
    exact this
  have hd := four_distinct_gen (cM r j b) (cM r j h2) hb h2' h3
  rw [Finset.card_le_one]
  intro g hg g' hg'
  have e1 := (Finset.mem_filter.1 hg).2
  have e2 := (Finset.mem_filter.1 hg').2
  have heq : cM r j g = cM r j g' := e1.trans e2.symm
  have m1 := (Finset.mem_filter.1 hg).1
  have m2 := (Finset.mem_filter.1 hg').1
  simp only [famS, Finset.mem_insert, Finset.mem_singleton] at m1 m2
  rcases m1 with rfl | rfl <;> rcases m2 with rfl | rfl <;>
    first
    | rfl
    | (exfalso; simp only [map_neg] at heq
       first | exact hd.1 heq | exact hd.1 heq.symm)

/-! ### the token system -/

/-- coefficient of an entry: zero if divisible by 5 -/
def cof (x : ℕ) (e : ℂ) : ℂ := if 5 ∣ x then 0 else e

/-- the positions of the five tokens: P, P/2, Q, Q/2, b = S/2 -/
def tokY (r j : ℕ) (P Q b : ℕ) (h2 : ZMod (5 ^ r * 3 ^ j)) : Fin 5 → ZMod (5 ^ r * 3 ^ j) :=
  ![(P : ZMod (5 ^ r * 3 ^ j)), (P : ZMod (5 ^ r * 3 ^ j)) * h2, (Q : ZMod (5 ^ r * 3 ^ j)),
    (Q : ZMod (5 ^ r * 3 ^ j)) * h2, (b : ZMod (5 ^ r * 3 ^ j))]

/-- the weights -/
def tokC (cP cQ cS : ℂ) : Fin 5 → ℂ := ![cP, -cP, cQ, -cQ, cS]

theorem chi_half {n : ℕ} (χ : DirichletCharacter ℂ n) (x : ZMod n) (hx : 2 * x = 1) :
    χ x = (χ 2)⁻¹ := by
  have : χ 2 * χ x = 1 := by rw [← map_mul, hx, map_one]
  exact eq_inv_of_mul_eq_one_right this

theorem hA_of_HD (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (P Q b : ℕ) (eP eQ eS : ℂ) (h2 : ZMod (5 ^ r * 3 ^ j))
    (hh2 : 2 * h2 = 1) (hP2 : P % 2 = 1) (hQ2 : Q % 2 = 1)
    (h3P : ¬ 5 ∣ P → ¬ 3 ∣ P) (h3Q : ¬ 5 ∣ Q → ¬ 3 ∣ Q) (h3S : ¬ 5 ∣ 2 * b → ¬ 3 ∣ 2 * b)
    (HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) P +
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) Q +
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (2 * b) = 0) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      ∑ t : Fin 5, tokC (cof P eP) (cof Q eQ) (cof (2 * b) eS) t *
        (ψ (c5 r j (tokY r j P Q b h2 t)) * η (c3 r j (tokY r j P Q b h2 t))) = 0 := by
  intro ψ hψ η hodd
  obtain ⟨κ0, hκ0, hodd_f, heven_f⟩ := Erdos634.GA2QK1.bracket_D r j hr hj ψ hψ η
  have H := HD ψ hψ η hodd
  have hψh : ψ (c5 r j h2) = (ψ 2)⁻¹ := by
    apply chi_half
    have := congrArg (c5 r j) hh2
    simp only [map_mul, map_one, map_ofNat] at this
    exact this
  have hηh : η (c3 r j h2) = (η 2)⁻¹ := by
    apply chi_half
    have := congrArg (c3 r j) hh2
    simp only [map_mul, map_one, map_ofNat] at this
    exact this
  have cop2 : ∀ x : ℕ, x % 2 = 1 → ¬ 3 ∣ x → Nat.Coprime (2 ^ 1 * 3 ^ j) x := by
    intro x hx2 hx3
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ?_) (Nat.Coprime.pow_left _ ?_)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hx3
  have bP : eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) P =
      κ0 * (cof P eP * (ψ (P : ZMod (5 ^ r)) * η (P : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹))) := by
    by_cases h : 5 ∣ P
    · rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := r) hr (Erdos634.GA2PA.not5_dvd' 1 j) hψ _ P h]
      simp [cof, h]
    · rw [hodd_f P h (cop2 P hP2 (h3P h))]
      simp only [cof, h, if_false]
      ring
  have bQ : eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) Q =
      κ0 * (cof Q eQ * (ψ (Q : ZMod (5 ^ r)) * η (Q : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹))) := by
    by_cases h : 5 ∣ Q
    · rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := r) hr (Erdos634.GA2PA.not5_dvd' 1 j) hψ _ Q h]
      simp [cof, h]
    · rw [hodd_f Q h (cop2 Q hQ2 (h3Q h))]
      simp only [cof, h, if_false]
      ring
  have bS : eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (2 * b) =
      κ0 * (cof (2 * b) eS * (ψ (b : ZMod (5 ^ r)) * η (b : ZMod (3 ^ j)))) := by
    by_cases h : 5 ∣ 2 * b
    · rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := r) hr (Erdos634.GA2PA.not5_dvd' 1 j) hψ _ (2 * b) h]
      simp [cof, h]
    · have h3 : ¬ 3 ∣ b := fun h3b => h3S h (Dvd.dvd.mul_left h3b 2)
      rw [heven_f b h h3]
      simp only [cof, h, if_false]
      ring
  have key : ∑ t : Fin 5, tokC (cof P eP) (cof Q eQ) (cof (2 * b) eS) t *
        (ψ (c5 r j (tokY r j P Q b h2 t)) * η (c3 r j (tokY r j P Q b h2 t))) =
      cof P eP * (ψ (P : ZMod (5 ^ r)) * η (P : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹)) +
      cof Q eQ * (ψ (Q : ZMod (5 ^ r)) * η (Q : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹)) +
      cof (2 * b) eS * (ψ (b : ZMod (5 ^ r)) * η (b : ZMod (3 ^ j))) := by
    simp [Fin.sum_univ_five, tokC, tokY, hψh, hηh]
    ring
  rw [key]
  have : κ0 * (cof P eP * (ψ (P : ZMod (5 ^ r)) * η (P : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹)) +
      cof Q eQ * (ψ (Q : ZMod (5 ^ r)) * η (Q : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ r)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹)) +
      cof (2 * b) eS * (ψ (b : ZMod (5 ^ r)) * η (b : ZMod (3 ^ j)))) = 0 := by
    rw [mul_add, mul_add, ← bP, ← bQ, ← bS]
    exact H
  exact (mul_eq_zero.1 this).resolve_left hκ0



theorem natcast_unitM (r j : ℕ) (x : ℕ) (h5 : ¬ 5 ∣ x) (h3 : ¬ 3 ∣ x) :
    IsUnit (cM r j (x : ZMod (5 ^ r * 3 ^ j))) := by
  rw [map_natCast, ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5).symm)
    (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm)

theorem even_tokens (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (hrj : 2 ≤ r ∨ 2 ≤ j) (P Q b : ℕ) (eP eQ eS : ℂ) (h2 : ZMod (5 ^ r * 3 ^ j))
    (hh2 : 2 * h2 = 1) (hP2 : P % 2 = 1) (hQ2 : Q % 2 = 1)
    (h3P : ¬ 5 ∣ P → ¬ 3 ∣ P) (h3Q : ¬ 5 ∣ Q → ¬ 3 ∣ Q) (h3S : ¬ 5 ∣ 2 * b → ¬ 3 ∣ 2 * b)
    (HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) P +
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) Q +
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (2 * b) = 0) :
    ∀ g : ZMod (5 ^ r * 3 ^ j),
      Fv r j Finset.univ (tokY r j P Q b h2) (tokC (cof P eP) (cof Q eQ) (cof (2 * b) eS)) g =
      Fv r j Finset.univ (tokY r j P Q b h2) (tokC (cof P eP) (cof Q eQ) (cof (2 * b) eS)) (-g) := by
  have hu2 : IsUnit h2 := IsUnit.of_mul_eq_one (2 : ZMod (5 ^ r * 3 ^ j)) (by linear_combination hh2)
  have uP : ¬ 5 ∣ P → IsUnit (P : ZMod (5 ^ r * 3 ^ j)) := fun h => unit_of_not r j P h (h3P h)
  have uQ : ¬ 5 ∣ Q → IsUnit (Q : ZMod (5 ^ r * 3 ^ j)) := fun h => unit_of_not r j Q h (h3Q h)
  have ub : ¬ 5 ∣ 2 * b → IsUnit (b : ZMod (5 ^ r * 3 ^ j)) := fun h =>
    unit_of_not r j b (fun h5 => h (Dvd.dvd.mul_left h5 2)) (fun h3 => h3S h (Dvd.dvd.mul_left h3 2))
  have hy : ∀ t ∈ (Finset.univ : Finset (Fin 5)),
      tokC (cof P eP) (cof Q eQ) (cof (2 * b) eS) t ≠ 0 → IsUnit (tokY r j P Q b h2 t) := by
    intro t _ hct
    have nP : ∀ h : 5 ∣ P, (cof P eP) = 0 := fun h => by simp [cof, h]
    have nQ : ∀ h : 5 ∣ Q, (cof Q eQ) = 0 := fun h => by simp [cof, h]
    have nS : ∀ h : 5 ∣ 2 * b, (cof (2 * b) eS) = 0 := fun h => by simp [cof, h]
    fin_cases t
    · have : ¬ 5 ∣ P := fun h => hct (by simp [tokC, nP h])
      simpa [tokY] using uP this
    · have : ¬ 5 ∣ P := fun h => hct (by simp [tokC, nP h])
      simpa [tokY] using (uP this).mul hu2
    · have : ¬ 5 ∣ Q := fun h => hct (by simp [tokC, nQ h])
      simpa [tokY] using uQ this
    · have : ¬ 5 ∣ Q := fun h => hct (by simp [tokC, nQ h])
      simpa [tokY] using (uQ this).mul hu2
    · have : ¬ 5 ∣ 2 * b := fun h => hct (by simp [tokC, nS h])
      simpa [tokY] using ub this
  have hA := hA_of_HD r j hr hj P Q b eP eQ eS h2 hh2 hP2 hQ2 h3P h3Q h3S HD
  set Pset : Finset (ZMod (5 ^ r * 3 ^ j)) :=
    (if 5 ∣ P then ∅ else famP (P : ZMod (5 ^ r * 3 ^ j)) h2) ∪
    (if 5 ∣ Q then ∅ else famP (Q : ZMod (5 ^ r * 3 ^ j)) h2) ∪
    (if 5 ∣ 2 * b then ∅ else famS (b : ZMod (5 ^ r * 3 ^ j))) with hPset
  refine even_of_top r j hr Finset.univ (tokY r j P Q b h2) (tokC (cof P eP) (cof Q eQ) (cof (2 * b) eS)) hy hA Pset ?_ ?_
  · intro t _ hct
    have nP : ∀ h : 5 ∣ P, (cof P eP) = 0 := fun h => by simp [cof, h]
    have nQ : ∀ h : 5 ∣ Q, (cof Q eQ) = 0 := fun h => by simp [cof, h]
    have nS : ∀ h : 5 ∣ 2 * b, (cof (2 * b) eS) = 0 := fun h => by simp [cof, h]
    fin_cases t
    · have h5 : ¬ 5 ∣ P := fun h => hct (by simp [tokC, nP h])
      simp [hPset, tokY, h5, famP]
    · have h5 : ¬ 5 ∣ P := fun h => hct (by simp [tokC, nP h])
      simp [hPset, tokY, h5, famP]
    · have h5 : ¬ 5 ∣ Q := fun h => hct (by simp [tokC, nQ h])
      simp [hPset, tokY, h5, famP]
    · have h5 : ¬ 5 ∣ Q := fun h => hct (by simp [tokC, nQ h])
      simp [hPset, tokY, h5, famP]
    · have h5 : ¬ 5 ∣ 2 * b := fun h => hct (by simp [tokC, nS h])
      simp [hPset, tokY, h5, famS]
  · intro k
    rw [hPset, Finset.filter_union, Finset.filter_union]
    refine le_trans (Finset.card_union_le _ _) ?_
    have c1 : ((if 5 ∣ P then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famP (P : ZMod (5 ^ r * 3 ^ j)) h2).filter
        (fun g => cM r j g = k)).card ≤ 1 := by
      by_cases h : 5 ∣ P
      · simp [h]
      · simp only [h, if_false]
        exact fam_card_le_one r j (three_ne_zeroM r j hrj) _ h2 (natcast_unitM r j P h (h3P h)) hh2 k
    have c2 : ((if 5 ∣ Q then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famP (Q : ZMod (5 ^ r * 3 ^ j)) h2).filter
        (fun g => cM r j g = k)).card ≤ 1 := by
      by_cases h : 5 ∣ Q
      · simp [h]
      · simp only [h, if_false]
        exact fam_card_le_one r j (three_ne_zeroM r j hrj) _ h2 (natcast_unitM r j Q h (h3Q h)) hh2 k
    have c3' : ((if 5 ∣ 2 * b then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famS (b : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k)).card ≤ 1 := by
      by_cases h : 5 ∣ 2 * b
      · simp [h]
      · simp only [h, if_false]
        exact famS_card_le_one r j (three_ne_zeroM r j hrj) _ h2 (natcast_unitM r j b (fun h5 => h (Dvd.dvd.mul_left h5 2)) (fun h3 => h3S h (Dvd.dvd.mul_left h3 2))) hh2 k
    have := Finset.card_union_le ((if 5 ∣ P then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famP (P : ZMod (5 ^ r * 3 ^ j)) h2).filter
        (fun g => cM r j g = k)) ((if 5 ∣ Q then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famP (Q : ZMod (5 ^ r * 3 ^ j)) h2).filter
        (fun g => cM r j g = k))
    omega


theorem cof_eq (x : ℕ) (e : ℂ) (h : ¬ 5 ∣ x) : cof x e = e := by simp [cof, h]
theorem cof_zero (x : ℕ) (e : ℂ) (h : 5 ∣ x) : cof x e = 0 := by simp [cof, h]

/-- **Prop D, labelled form** (n = 2 * 5 * 3^j, j >= 2; P, Q odd, S even; no entry of I divisible by 3). -/
theorem theoremK_lab (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (hrj : 2 ≤ r ∨ 2 ≤ j) (P Q b : ℕ) (eP eQ eS : ℂ)
    (hP2 : P % 2 = 1) (hQ2 : Q % 2 = 1)
    (gP : 0 < P) (gQ : 0 < Q) (gS : 0 < 2 * b)
    (hsum : P + Q + 2 * b = 2 * (5 ^ r * 3 ^ j))
    (h5 : ¬ (5 ∣ P ∧ 5 ∣ Q ∧ 5 ∣ 2 * b))
    (h3P : ¬ 5 ∣ P → ¬ 3 ∣ P) (h3Q : ¬ 5 ∣ Q → ¬ 3 ∣ Q) (h3S : ¬ 5 ∣ 2 * b → ¬ 3 ∣ 2 * b)
    (HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) P +
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) Q +
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) (2 * b) = 0) :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if P = x then eP else 0) + (if Q = x then eQ else 0) + (if 2 * b = x then eS else 0) = 0 := by
  have hN2 := N_odd r j
  have hNge := N_ge r j hr hj
  obtain ⟨h2, hh2⟩ := exists_half r j
  have hev := even_tokens r j hr hj hrj P Q b eP eQ eS h2 hh2 hP2 hQ2 h3P h3Q h3S HD
  have hu2 : IsUnit h2 := IsUnit.of_mul_eq_one (2 : ZMod (5 ^ r * 3 ^ j)) (by linear_combination hh2)
  have hsumR : ((P : ZMod (5 ^ r * 3 ^ j)) + Q + 2 * (b : ZMod (5 ^ r * 3 ^ j))) = 0 := by
    have h : ((P + Q + 2 * b : ℕ) : ZMod (5 ^ r * 3 ^ j)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, mul_zero]
    push_cast at h
    exact h
  have hbR : (b : ZMod (5 ^ r * 3 ^ j)) = -((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2 := by
    linear_combination h2 * hsumR - (b : ZMod (5 ^ r * 3 ^ j)) * hh2
  have hPeq : (P : ZMod (5 ^ r * 3 ^ j)) = 2 * ((P : ZMod (5 ^ r * 3 ^ j)) * h2) := by
    linear_combination (-(P : ZMod (5 ^ r * 3 ^ j))) * hh2
  have hQeq : (Q : ZMod (5 ^ r * 3 ^ j)) = 2 * ((Q : ZMod (5 ^ r * 3 ^ j)) * h2) := by
    linear_combination (-(Q : ZMod (5 ^ r * 3 ^ j))) * hh2
  have hFv : ∀ g, Fv r j Finset.univ (tokY r j P Q b h2) (tokC (cof P eP) (cof Q eQ) (cof (2 * b) eS)) g =
      Fq (2 * ((P : ZMod (5 ^ r * 3 ^ j)) * h2)) ((P : ZMod (5 ^ r * 3 ^ j)) * h2)
        (2 * ((Q : ZMod (5 ^ r * 3 ^ j)) * h2)) ((Q : ZMod (5 ^ r * 3 ^ j)) * h2)
        (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) 1
        (cof P eP) (cof Q eQ) (cof (2 * b) eS) g := by
    intro g
    rw [← hPeq, ← hQeq, ← hbR]
    simp [Fv, Fin.sum_univ_five, tokY, tokC, Fq]
    split_ifs <;> ring
  have H' : ∀ g, Fp ((P : ZMod (5 ^ r * 3 ^ j)) * h2) ((Q : ZMod (5 ^ r * 3 ^ j)) * h2) 1 (cof P eP) (cof Q eQ)
      (cof (2 * b) eS) g + (-1) * Fp ((P : ZMod (5 ^ r * 3 ^ j)) * h2) ((Q : ZMod (5 ^ r * 3 ^ j)) * h2) 1
      (cof P eP) (cof Q eQ) (cof (2 * b) eS) (-g) = 0 := by
    intro g
    have := hev g
    rw [hFv g, hFv (-g)] at this
    unfold Fp
    linear_combination this
  have hPlt : P < 2 * (5 ^ r * 3 ^ j) := by omega
  have hQlt : Q < 2 * (5 ^ r * 3 ^ j) := by omega
  have h5N : 5 ∣ P + Q + 2 * b := by
    rw [hsum]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _) 2
  have uP : ¬ 5 ∣ P → IsUnit (P : ZMod (5 ^ r * 3 ^ j)) := fun h => unit_of_not r j P h (h3P h)
  have uQ : ¬ 5 ∣ Q → IsUnit (Q : ZMod (5 ^ r * 3 ^ j)) := fun h => unit_of_not r j Q h (h3Q h)
  have ub : ¬ 5 ∣ 2 * b → IsUnit (b : ZMod (5 ^ r * 3 ^ j)) := fun h =>
    unit_of_not r j b (fun h5 => h (Dvd.dvd.mul_left h5 2)) (fun h3 => h3S h (Dvd.dvd.mul_left h3 2))
  have hM13 : 13 ≤ 5 ^ r * 3 ^ j := by omega
  intro x hx5
  have hSterm : cof (2 * b) eS = 0 → (if 2 * b = x then eS else 0) = 0 := by
    intro hc
    by_cases h : 5 ∣ 2 * b
    · rw [if_neg (by intro e; exact hx5 (e ▸ h))]
    · rw [cof_eq _ _ h] at hc; simp [hc]
  by_cases hP5 : 5 ∣ P
  · by_cases hQ5 : 5 ∣ Q
    · exact absurd ⟨hP5, hQ5, by omega⟩ h5
    · by_cases hS5 : 5 ∣ 2 * b
      · exfalso; omega
      · -- Case B: P absent
        have hv : IsUnit ((Q : ZMod (5 ^ r * 3 ^ j)) * h2) := (uQ hQ5).mul hu2
        have hw : IsUnit (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) := by
          rw [← hbR]; exact ub hS5
        have H'' : ∀ g, Fq (2 * ((P : ZMod (5 ^ r * 3 ^ j)) * h2)) ((P : ZMod (5 ^ r * 3 ^ j)) * h2)
            (2 * ((Q : ZMod (5 ^ r * 3 ^ j)) * h2)) ((Q : ZMod (5 ^ r * 3 ^ j)) * h2)
            (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) 1 0 (cof Q eQ)
            (cof (2 * b) eS) g + (-1) * Fq (2 * ((P : ZMod (5 ^ r * 3 ^ j)) * h2))
            ((P : ZMod (5 ^ r * 3 ^ j)) * h2) (2 * ((Q : ZMod (5 ^ r * 3 ^ j)) * h2))
            ((Q : ZMod (5 ^ r * 3 ^ j)) * h2)
            (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) 1 0 (cof Q eQ)
            (cof (2 * b) eS) (-g) = 0 := by
          intro g
          have := H' g
          rw [cof_zero P eP hP5] at this
          exact this
        obtain ⟨hq0, hs0⟩ := pattern_two hM13 hN2 hv hw one_ne_zero (Or.inr rfl) _ _ H''
        rw [cof_eq Q eQ hQ5] at hq0
        have hPx : (if P = x then eP else 0) = 0 := by
          rw [if_neg (by intro e; exact hx5 (e ▸ hP5))]
        rw [hSterm hs0, hPx, hq0]
        simp
  · by_cases hQ5 : 5 ∣ Q
    · by_cases hS5 : 5 ∣ 2 * b
      · exfalso; omega
      · -- Case C: Q absent
        have hv : IsUnit ((P : ZMod (5 ^ r * 3 ^ j)) * h2) := (uP hP5).mul hu2
        have hw : IsUnit (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) := by
          rw [← hbR]; exact ub hS5
        have H'' : ∀ g, Fq (2 * ((Q : ZMod (5 ^ r * 3 ^ j)) * h2)) ((Q : ZMod (5 ^ r * 3 ^ j)) * h2)
            (2 * ((P : ZMod (5 ^ r * 3 ^ j)) * h2)) ((P : ZMod (5 ^ r * 3 ^ j)) * h2)
            (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) 1 0 (cof P eP)
            (cof (2 * b) eS) g + (-1) * Fq (2 * ((Q : ZMod (5 ^ r * 3 ^ j)) * h2))
            ((Q : ZMod (5 ^ r * 3 ^ j)) * h2) (2 * ((P : ZMod (5 ^ r * 3 ^ j)) * h2))
            ((P : ZMod (5 ^ r * 3 ^ j)) * h2)
            (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) 1 0 (cof P eP)
            (cof (2 * b) eS) (-g) = 0 := by
          intro g
          have := H' g
          rw [cof_zero Q eQ hQ5] at this
          unfold Fp Fq at this
          unfold Fq
          linear_combination this
        obtain ⟨hp0, hs0⟩ := pattern_two hM13 hN2 hv hw one_ne_zero (Or.inr rfl) _ _ H''
        rw [cof_eq P eP hP5] at hp0
        have hQx : (if Q = x then eQ else 0) = 0 := by
          rw [if_neg (by intro e; exact hx5 (e ▸ hQ5))]
        rw [hSterm hs0, hQx, hp0]
        simp
    · -- Case A: P, Q present
      have hu : IsUnit ((P : ZMod (5 ^ r * 3 ^ j)) * h2) := (uP hP5).mul hu2
      have hv : IsUnit ((Q : ZMod (5 ^ r * 3 ^ j)) * h2) := (uQ hQ5).mul hu2
      have hc : cof (2 * b) eS = 0 ∨ IsUnit (-((P : ZMod (5 ^ r * 3 ^ j)) * h2) - (Q : ZMod (5 ^ r * 3 ^ j)) * h2) := by
        by_cases hS5 : 5 ∣ 2 * b
        · exact Or.inl (cof_zero _ _ hS5)
        · right; rw [← hbR]; exact ub hS5
      rcases pattern_lemma hM13 hN2 hu hv one_ne_zero (Or.inr rfl) hc H' with
        ⟨ha, hb', hc'⟩ | ⟨hvu, hbq, hc'⟩ | ⟨hvu, hc', hbq⟩
      · rw [cof_eq P eP hP5] at ha
        rw [cof_eq Q eQ hQ5] at hb'
        rw [hSterm hc', ha, hb']
        simp
      · have hQP : (Q : ZMod (5 ^ r * 3 ^ j)) = (P : ZMod (5 ^ r * 3 ^ j)) := by
          linear_combination 2 * hvu - ((Q : ZMod (5 ^ r * 3 ^ j)) - P) * hh2
        have hPQ : Q = P := eq_of_cast_eq _ hN2 Q P hQ2 hP2 hQlt hPlt hQP
        rw [cof_eq Q eQ hQ5, cof_eq P eP hP5] at hbq
        rw [hSterm hc', hPQ, hbq]
        split_ifs <;> ring
      · exfalso
        refine not_neg_cast _ hN2 P Q hP2 hQ2 (by omega) (by omega) ?_
        linear_combination 2 * hvu - ((P : ZMod (5 ^ r * 3 ^ j)) + Q) * hh2



end Erdos634.GA2QK3

#print axioms Erdos634.GA2QK3.theoremK_lab
