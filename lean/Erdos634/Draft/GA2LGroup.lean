/-
GA2L, atom P4 (assembly): **group core of TOP** (GA2Y_NOTES Lemma A3, Steps 1-3), r = 1, j >= 2,
general i = k+3 >= 3, general j >= 2.  See GA2LCore.lean header.

`Hyp k j z5 z2 z3 c` : psi(z5) eta2(z2) eta3(z3) = c for every psi primitive mod 5, eta2 primitive mod 2^i,
eta3 NONTRIVIAL mod 3^j with chi = psi eta2 eta3 odd.
`group_core`   : Hyp (+ units) => exists s e in {0,1}: z5 = (-1)^s, z3 = (-1)^s, z2 = (-1)^s (1+2^(i-1))^e, c = (-1)^(s+e).
`group_core_converse` : the converse (witness: the hypothesis set is exactly satisfiable).
-/
import Mathlib
import Erdos634.Draft.GA2LCore

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2LGroup

open Erdos634.GA2LPar Erdos634.GA2LCore

instance fact3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩

def Hyp (k j : ℕ) (z5 z2 z3 : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
  ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
    ψ (-1) * η2 (-1) * η3 (-1) = -1 →
    ψ (z5 : ZMod (5 ^ 1)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ j)) = c

theorem tot3 (j : ℕ) (hj : 2 ≤ j) : 3 ≤ (3 ^ j).totient := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  rw [Nat.totient_prime_pow (by norm_num) (by omega)]
  have : 1 ≤ 3 ^ j' := Nat.one_le_pow _ _ (by norm_num)
  have e : 3 ^ (j' + 2 - 1) = 3 * 3 ^ j' := by
    rw [show j' + 2 - 1 = j' + 1 by omega]; ring
  rw [e]; omega

theorem exists_ne_one3 (j : ℕ) (hj : 2 ≤ j) : ∃ η : DirichletCharacter ℂ (3 ^ j), η ≠ 1 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hN : Fintype.card (DirichletCharacter ℂ (3 ^ j)) = (3 ^ j).totient := by
    have := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (3 ^ j)
    rwa [Nat.card_eq_fintype_card] at this
  have := tot3 j hj
  haveI : Nontrivial (DirichletCharacter ℂ (3 ^ j)) :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  exact exists_ne _

theorem two_ne_zero' {k : ℕ} : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero

theorem nonempty_par2 (k : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) : (PrimPar 2 (k + 3) ε).Nonempty := by
  rw [← card_pos, card_par_two k ε hε]; positivity

theorem group_core (k j : ℕ) (hj : 2 ≤ j) (z5 z2 z3 : ℤ) (c : ℂ)
    (u5 : IsUnit (z5 : ZMod (5 ^ 1))) (u2 : IsUnit (z2 : ZMod (2 ^ (k + 3))))
    (u3 : IsUnit (z3 : ZMod (3 ^ j))) (H : Hyp k j z5 z2 z3 c) :
    ∃ s e : ℕ, s < 2 ∧ e < 2 ∧ (z5 : ZMod (5 ^ 1)) = (-1) ^ s ∧ (z3 : ZMod (3 ^ j)) = (-1) ^ s ∧
      (z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e ∧ c = (-1) ^ (s + e) := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  -- the claim: Hyp, with eta2 of the forced parity
  have claim : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
      ∀ η2 ∈ PrimPar 2 (k + 3) (-(ψ (-1) * η3 (-1))),
        ψ (z5 : ZMod (5 ^ 1)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ j)) = c := by
    intro ψ hψ η3 hη3 η2 hη2
    obtain ⟨hp2, hs2⟩ := mem_PrimPar.1 hη2
    refine H ψ hψ η2 hp2 η3 hη3 ?_
    rw [hs2]
    rcases sign_val ψ with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num
  have sgn : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
      (-(ψ (-1) * η3 (-1))) = 1 ∨ (-(ψ (-1) * η3 (-1))) = -1 := by
    intro ψ η3
    rcases sign_val ψ with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num
  -- existence of the ingredients
  have ne5e : (PrimPar 5 1 1).Nonempty := by
    rw [← card_pos, card_five 1 (Or.inl rfl)]; norm_num
  obtain ⟨ψe, hψe⟩ := ne5e
  obtain ⟨hψe_p, hψe_s⟩ := mem_PrimPar.1 hψe
  obtain ⟨η30, hη30⟩ := exists_ne_one3 j hj
  have A0 : ψe (z5 : ZMod (5 ^ 1)) ≠ 0 := nz ψe _ u5
  -- Step 1: the 2-part
  have step1 : ∃ s e : ℕ, s < 2 ∧ e < 2 ∧
      ((z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e) ∧
      ∀ ε' : ℂ, (ε' = 1 ∨ ε' = -1) → ∀ η ∈ PrimPar 2 (k + 3) ε',
        η (z2 : ZMod (2 ^ (k + 3))) = ε' ^ s * (-1) ^ e := by
    refine two_part_core k (-(ψe (-1) * η30 (-1))) (sgn ψe η30) z2 u2
      ⟨c / (ψe (z5 : ZMod (5 ^ 1)) * η30 (z3 : ZMod (3 ^ j))), fun η hη => ?_⟩
    have h := claim ψe hψe_p η30 hη30 η hη
    have B0 : η30 (z3 : ZMod (3 ^ j)) ≠ 0 := nz η30 _ u3
    rw [eq_div_iff (mul_ne_zero A0 B0)]
    linear_combination h
  obtain ⟨s, e, hs, he, h2eq, hval⟩ := step1
  -- Step 2: the 3-part
  have usg : IsUnit ((-1 : ZMod (3 ^ j)) ^ s) := (isUnit_one.neg).pow s
  have step2 : (z3 : ZMod (3 ^ j)) * (-1) ^ s = 1 := by
    by_contra hne
    set g3 : ZMod (3 ^ j) := (z3 : ZMod (3 ^ j)) * (-1) ^ s with hg3
    have hug : IsUnit g3 := u3.mul usg
    have hAe : ψe (z5 : ZMod (5 ^ 1)) * (-1) ^ (s + e) ≠ 0 :=
      mul_ne_zero A0 (pow_ne_zero _ (by norm_num))
    refine const_nontriv (3 ^ j) g3 hug hne (tot3 j hj)
      (c / (ψe (z5 : ZMod (5 ^ 1)) * (-1) ^ (s + e))) (fun η3 hη3 => ?_)
    obtain ⟨η2, hη2⟩ := nonempty_par2 k (-(ψe (-1) * η3 (-1))) (sgn ψe η3)
    have h := claim ψe hψe_p η3 hη3 η2 hη2
    rw [hval _ (sgn ψe η3) η2 hη2, hψe_s] at h
    rw [eq_div_iff hAe, hg3, map_mul, map_pow]
    rw [neg_pow] at h
    simp only [one_mul] at h
    rw [pow_add]
    linear_combination h
  have z3eq : (z3 : ZMod (3 ^ j)) = (-1) ^ s := by
    have hs2 : ((-1 : ZMod (3 ^ j)) ^ s) * ((-1) ^ s) = 1 := by
      rw [← mul_pow]; simp
    calc (z3 : ZMod (3 ^ j)) = (z3 * (-1) ^ s) * (-1) ^ s := by
          rw [mul_assoc, hs2, mul_one]
      _ = (-1) ^ s := by rw [step2, one_mul]
  -- Step 3: the 5-part
  have step3 : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ψ (z5 : ZMod (5 ^ 1)) * ((-(ψ (-1) * η30 (-1))) ^ s * (-1) ^ e * η30 (-1) ^ s) = c := by
    intro ψ hψ
    obtain ⟨η2, hη2⟩ := nonempty_par2 k (-(ψ (-1) * η30 (-1))) (sgn ψ η30)
    have h := claim ψ hψ η30 hη30 η2 hη2
    rw [hval _ (sgn ψ η30) η2 hη2, z3eq, map_pow] at h
    linear_combination h
  have sq1 : ∀ x : ℂ, (x = 1 ∨ x = -1) → ∀ n : ℕ, x ^ n * x ^ n = 1 := by
    intro x hx n; rw [← mul_pow]; rcases hx with rfl | rfl <;> simp
  have hX := sq1 (η30 (-1)) (sign_val η30) s
  have hb := sq1 (-1 : ℂ) (Or.inr rfl) e
  -- odd psi: psi z5 = (-1)^e * c
  have odd5 : ∀ ψ ∈ PrimPar 5 1 (-1), ψ (z5 : ZMod (5 ^ 1)) = (-1) ^ e * c := by
    intro ψ hψ
    obtain ⟨hp, hs⟩ := mem_PrimPar.1 hψ
    have h := step3 ψ hp
    rw [hs, neg_one_mul, neg_neg] at h
    linear_combination (-1 : ℂ) ^ e * h - ψ (z5 : ZMod (5 ^ 1)) * (η30 (-1) ^ s * η30 (-1) ^ s) * hb
      - ψ (z5 : ZMod (5 ^ 1)) * hX
  have five := five_odd z5 u5 ((-1) ^ e * c) odd5
  -- even psi: c = (-1)^(s+e)
  have zm5 : ∀ {w : ℤ}, z5 ≡ w [ZMOD 5] → (z5 : ZMod (5 ^ 1)) = (w : ZMod (5 ^ 1)) := by
    intro w h
    rw [ZMod.intCast_eq_intCast_iff]; push_cast; simpa using h
  have hcc : c = (-1) ^ (s + e) := by
    have hz5 : (z5 : ZMod (5 ^ 1)) = 1 ∨ (z5 : ZMod (5 ^ 1)) = -1 := by
      rcases five with ⟨h, _⟩ | ⟨h, _⟩
      · left; simpa using zm5 h
      · right; simpa using zm5 h
    have hψ1 : ψe (z5 : ZMod (5 ^ 1)) = 1 := by
      rcases hz5 with h | h <;> rw [h]
      · exact map_one ψe
      · exact hψe_s
    have h := step3 ψe hψe_p
    rw [hψ1, hψe_s, one_mul, one_mul, neg_pow] at h
    rw [pow_add]
    linear_combination -h + (-1 : ℂ) ^ s * (-1) ^ e * hX
  refine ⟨s, e, hs, he, ?_, z3eq, h2eq, hcc⟩
  have hb1 : (-1 : ℂ) ^ e * (-1) ^ (s + e) = (-1) ^ s := by
    rw [pow_add]; linear_combination (-1 : ℂ) ^ s * hb
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · rcases five with ⟨h, h'⟩ | ⟨h, h'⟩
    · simpa using zm5 h
    · exfalso
      rw [hcc, hb1] at h'
      norm_num at h'
  · rcases five with ⟨h, h'⟩ | ⟨h, h'⟩
    · exfalso
      rw [hcc, hb1] at h'
      norm_num at h'
    · simpa using zm5 h


/-! ## Converse (witness) and non-vacuity -/

theorem unit_one_add (k : ℕ) : IsUnit (((1 + 2 ^ (k + 2) : ℤ) : ZMod (2 ^ (k + 3)))) := by
  have h0 : ((2 : ZMod (2 ^ (k + 3))) ^ (k + 3)) = 0 := by
    have := ZMod.natCast_self (2 ^ (k + 3)); push_cast at this; exact this
  refine IsUnit.of_mul_eq_one (b := ((1 + 2 ^ (k + 2) : ℤ) : ZMod (2 ^ (k + 3)))) ?_
  push_cast
  linear_combination (1 + 2 ^ (k + 1) : ZMod (2 ^ (k + 3))) * h0

theorem eta2_val (k : ℕ) (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive) :
    η2 (1 + 2 ^ (k + 2) : ZMod (2 ^ (k + 3))) = -1 := by
  have h := (two_adic_par_value k (η2 (-1)) (sign_val η2) (1 + 2 ^ (k + 2)) (unit_one_add k)).2.1
    (Int.ModEq.refl _) η2 (mem_PrimPar.2 ⟨hη2, rfl⟩)
  push_cast at h
  exact h

theorem group_core_converse (k j : ℕ) (s e : ℕ) (z5 z2 z3 : ℤ)
    (e5 : (z5 : ZMod (5 ^ 1)) = (-1) ^ s) (e3 : (z3 : ZMod (3 ^ j)) = (-1) ^ s)
    (e2 : (z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e) :
    Hyp k j z5 z2 z3 ((-1) ^ (s + e)) := by
  intro ψ _ η2 hη2 η3 _ hodd
  rw [e5, e2, e3, map_pow, map_mul, map_pow, map_pow, map_pow, eta2_val k η2 hη2]
  have key : ψ (-1) ^ s * (η2 (-1) ^ s * (-1) ^ e) * η3 (-1) ^ s =
      (ψ (-1) * η2 (-1) * η3 (-1)) ^ s * (-1) ^ e := by ring
  rw [key, hodd, pow_add]

/-- The admissible family is nonempty: there is an odd chi = psi eta2 eta3 in it (so `Hyp` is not vacuous). -/
theorem admissible_exists (k j : ℕ) (hj : 2 ≤ j) :
    ∃ (ψ : DirichletCharacter ℂ (5 ^ 1)) (η2 : DirichletCharacter ℂ (2 ^ (k + 3)))
      (η3 : DirichletCharacter ℂ (3 ^ j)), ψ.IsPrimitive ∧ η2.IsPrimitive ∧ η3 ≠ 1 ∧
        ψ (-1) * η2 (-1) * η3 (-1) = -1 := by
  have ne5e : (PrimPar 5 1 1).Nonempty := by
    rw [← card_pos, card_five 1 (Or.inl rfl)]; norm_num
  obtain ⟨ψe, hψe⟩ := ne5e
  obtain ⟨hp, hs⟩ := mem_PrimPar.1 hψe
  obtain ⟨η3, h3⟩ := exists_ne_one3 j hj
  have sg : (-(ψe (-1) * η3 (-1))) = 1 ∨ (-(ψe (-1) * η3 (-1))) = -1 := by
    rcases sign_val ψe with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num
  obtain ⟨η2, hη2⟩ := nonempty_par2 k _ sg
  obtain ⟨hp2, hs2⟩ := mem_PrimPar.1 hη2
  refine ⟨ψe, η2, η3, hp, hp2, h3, ?_⟩
  rw [hs2]
  rcases sign_val ψe with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num

end Erdos634.GA2LGroup

#print axioms Erdos634.GA2LGroup.group_core_converse
#print axioms Erdos634.GA2LGroup.admissible_exists
#print axioms Erdos634.GA2LGroup.group_core
