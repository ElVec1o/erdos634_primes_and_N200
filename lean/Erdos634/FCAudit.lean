import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Erdos634.FourCompCongruence

/-!
# Satisfiability of the hypotheses of `Erdos634.FourCompCongruence`

This file contains no new mathematics about the tiling problem.  It exhibits a witness for every
hypothesis of the theorems of `FourCompCongruence.lean`, so that none of them is vacuous.

## What is certified here

* `not_both_even_nonvacuous`, `even_iff_zmod4_both_directions`: the two elementary lemmas apply.
* `B_never_square_nonvacuous`: the hypothesis is satisfiable and the conclusion has content
  (`11` is not a square).
* `A_square_forces_witness`: a simultaneous witness for `IsCoprime e f` and `2f² − e² = u²`:
  `(e,f,u) = (1,5,7)`, `A = 49`, and the conclusion `B = 74 ≡ 2 (mod 4)` is then non-trivial.
* `A_square_forces_needs_coprimality`: at `(e,f,u) = (2,2,2)` the equation `2f² − e² = u²` holds
  but `3f² − e² = 8 ≢ 2 (mod 4)`, so the coprimality hypothesis `hc` is needed.
* `fourcomp_prime_eq_two_witness`, `fourcomp_no_odd_prime_witness`: a non-degenerate
  (`0 < e < f`) simultaneous witness for every hypothesis, at
  `(e,f,u,v,N) = (647,2993,4183,3637,2)`.  A computer sweep of all `2 735 387` coprime pairs with
  `0 < e < f < 3000`, and of all coprime pairs with `f < 40000`, finds this as the only pair for
  which `A · B` is `prime × square`.  The conditional is therefore true and non-vacuous, though very
  thinly so.
* `hsplit_left_branch_is_empty`: the left disjunct of the hypothesis of `fourcomp_no_odd_prime` is
  unsatisfiable for every coprime `e, f` (it is exactly what `B_never_square` forbids).  The
  two-branch `hsplit` is thus a one-branch hypothesis written as a disjunction.
* `A_square_parity_locked`: the mixed-parity cases of `A_square_forces` are vacuous.
* `A_square_forces_mod8`: the sharper congruence `≡ 2 (mod 8)`, noted in parentheses in
  `FourCompCongruence` (which states only `≡ 2 (mod 4)`).

Nothing else imports this file.
-/

namespace Erdos634.FCAudit

open Erdos634.FourCompCongruence

/-! ## `not_both_even` -/

/-- The hypothesis of `not_both_even` is satisfiable (`e = 1`, `f = 2`) and the conclusion is a
genuine statement there. -/
theorem not_both_even_nonvacuous : ¬ ((2 : ℤ) ∣ 1 ∧ (2 : ℤ) ∣ 2) :=
  not_both_even (isCoprime_one_left : IsCoprime (1 : ℤ) 2)

/-! ## `even_iff_zmod4` -/

/-- Both directions of `even_iff_zmod4` fire on concrete data. -/
theorem even_iff_zmod4_both_directions :
    (((6 : ℤ) : ZMod 4) = 0 ∨ ((6 : ℤ) : ZMod 4) = 2) ∧ (2 : ℤ) ∣ 6 := by
  refine ⟨(even_iff_zmod4 6).mp ⟨3, by norm_num⟩, (even_iff_zmod4 6).mpr ?_⟩
  right
  norm_num
  decide

/-- …and the lemma really does refuse an odd input: `7` is not even, and `(7 : ZMod 4) = 3`. -/
theorem even_iff_zmod4_refuses_odd : ¬ (((7 : ℤ) : ZMod 4) = 0 ∨ ((7 : ℤ) : ZMod 4) = 2) := by
  intro h
  have : (2 : ℤ) ∣ 7 := (even_iff_zmod4 7).mpr h
  omega

/-! ## `B_never_square` -/

/-- The hypothesis is satisfiable at `(e,f) = (1,2)` and the conclusion there is the non-trivial
fact that `11` is not a perfect square. -/
theorem B_never_square_nonvacuous : ∀ v : ℤ, (11 : ℤ) ≠ v ^ 2 := by
  intro v h
  exact B_never_square (e := 1) (f := 2) (isCoprime_one_left : IsCoprime (1 : ℤ) 2)
    (by linarith : 3 * (2 : ℤ) ^ 2 - 1 ^ 2 = v ^ 2)

/-! ## `A_square_forces` -/

/-- **The witness that matters.**  `A_square_forces` has *two* hypotheses that must hold at the
same `(e,f)`: coprimality and `2f² − e² = u²`.  Both hold at `(e,f,u) = (1,5,7)`
(`A = 50 − 1 = 49 = 7²`), and the conclusion is then the non-trivial `74 ≡ 2 (mod 4)`. -/
theorem A_square_forces_witness :
    ∃ (e f u : ℤ), IsCoprime e f ∧ 0 < e ∧ e < f ∧ 2 * f ^ 2 - e ^ 2 = u ^ 2 :=
  ⟨1, 5, 7, isCoprime_one_left, by norm_num, by norm_num, by norm_num⟩

/-- The conclusion of `A_square_forces` instantiated at that witness. -/
theorem A_square_forces_at_witness : (((3 * (5 : ℤ) ^ 2 - 1 ^ 2 : ℤ)) : ZMod 4) = 2 :=
  A_square_forces (e := 1) (f := 5) (u := 7) (isCoprime_one_left : IsCoprime (1 : ℤ) 5)
    (by norm_num)

/-- **Coprimality is needed.**  Without it the theorem is false: at `e = f = 2` we have
`2f² − e² = 4 = 2²` yet `3f² − e² = 8 ≡ 0 (mod 4)`.  So `hc` is used essentially. -/
theorem A_square_forces_needs_coprimality :
    2 * (2 : ℤ) ^ 2 - 2 ^ 2 = 2 ^ 2 ∧ (((3 * (2 : ℤ) ^ 2 - 2 ^ 2 : ℤ)) : ZMod 4) ≠ 2 := by
  refine ⟨by norm_num, ?_⟩
  norm_num
  decide

/-- Machine-check of the docstring claim *"the mixed-parity cases are vacuous"*: modulo `4`,
`2F² − E² = U²` forces `E` and `F` to have the **same** parity. -/
theorem A_square_parity_locked :
    ∀ E F U : ZMod 4, 2 * F ^ 2 - E ^ 2 = U ^ 2 → ((E = 0 ∨ E = 2) ↔ (F = 0 ∨ F = 2)) := by
  decide

/-! ## The docstring's `(mod 8 in truth)` parenthetical

`FourCompCongruence.A_square_forces` proves only `B ≡ 2 (mod 4)`; its docstring asserts, without
proof, that `mod 8` is the truth.  That assertion is verified here, so the docstring does not
over-claim. -/

/-- Under the hypotheses of `A_square_forces`, `e` and `f` are **both odd**. -/
theorem A_square_both_odd {e f u : ℤ} (hc : IsCoprime e f) (h : 2 * f ^ 2 - e ^ 2 = u ^ 2) :
    ¬ (2 : ℤ) ∣ e ∧ ¬ (2 : ℤ) ∣ f := by
  have h4 : 2 * ((f : ZMod 4)) ^ 2 - ((e : ZMod 4)) ^ 2 = ((u : ZMod 4)) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod 4)) h; push_cast at this; exact this
  have hiff := A_square_parity_locked _ _ _ h4
  have hne := not_both_even hc
  constructor
  · intro he
    exact hne ⟨he, (even_iff_zmod4 f).mpr (hiff.mp ((even_iff_zmod4 e).mp he))⟩
  · intro hf
    exact hne ⟨(even_iff_zmod4 e).mpr (hiff.mpr ((even_iff_zmod4 f).mp hf)), hf⟩

/-- **The docstring's parenthetical, proved.**  If `2f² − e²` is a square and `gcd(e,f) = 1`, then
`3f² − e² ≡ 2 (mod 8)` — strictly stronger than the `mod 4` statement the file proves. -/
theorem A_square_forces_mod8 {e f u : ℤ} (hc : IsCoprime e f) (h : 2 * f ^ 2 - e ^ 2 = u ^ 2) :
    (((3 * f ^ 2 - e ^ 2 : ℤ)) : ZMod 8) = 2 := by
  obtain ⟨he, hf⟩ := A_square_both_odd hc h
  obtain ⟨a, ha⟩ : ∃ a : ℤ, e = 2 * a + 1 := ⟨e / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, f = 2 * b + 1 := ⟨f / 2, by omega⟩
  obtain ⟨s, hs⟩ : (2 : ℤ) ∣ b * (b + 1) := (Int.even_mul_succ_self b).two_dvd
  obtain ⟨t, ht⟩ : (2 : ℤ) ∣ a * (a + 1) := (Int.even_mul_succ_self a).two_dvd
  have h8 : (8 : ℤ) ∣ (3 * f ^ 2 - e ^ 2 - 2) := ⟨3 * s - t, by subst ha; subst hb; linarith⟩
  have : (((3 * f ^ 2 - e ^ 2 - 2 : ℤ)) : ZMod 8) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h8
  push_cast at this ⊢
  linear_combination this

/-! ## `fourcomp_prime_eq_two` and `fourcomp_no_odd_prime` -/

/-- **The non-vacuity certificate for `fourcomp_prime_eq_two`.**  Every hypothesis holds
simultaneously at `(e,f,u,v,N) = (647, 2993, 4183, 3637, 2)`, and this witness is
**non-degenerate**: `0 < e < f`, which is the geometric range (`s = e/f ∈ (0,1)`).

`A = 2·2993² − 647² = 17497489 = 4183²` and `B = 3·2993² − 647² = 26455538 = 2 · 3637²`. -/
theorem fourcomp_prime_eq_two_witness :
    ∃ (e f u v : ℤ) (N : ℕ), IsCoprime e f ∧ Nat.Prime N ∧ 0 < e ∧ e < f ∧
      2 * f ^ 2 - e ^ 2 = u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2 :=
  ⟨647, 2993, 4183, 3637, 2,
    Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num), Nat.prime_two,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The theorem applied at that witness returns its conclusion. -/
theorem fourcomp_prime_eq_two_at_witness : (2 : ℕ) = 2 :=
  fourcomp_prime_eq_two (e := 647) (f := 2993) (u := 4183) (v := 3637) (N := 2)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)) Nat.prime_two (by norm_num) (by norm_num)

/-- **The `hsplit` hypothesis of `fourcomp_no_odd_prime` is satisfiable**, non-degenerately. -/
theorem fourcomp_no_odd_prime_witness :
    ∃ (e f : ℤ) (N : ℕ), IsCoprime e f ∧ Nat.Prime N ∧ 0 < e ∧ e < f ∧
      ((∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = (N : ℤ) * u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = v ^ 2) ∨
       (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2)) :=
  ⟨647, 2993, 2, Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num), Nat.prime_two,
    by norm_num, by norm_num,
    Or.inr ⟨4183, 3637, by norm_num, by norm_num⟩⟩

/-- **Structural finding.**  The *left* disjunct of `hsplit` is unsatisfiable for every coprime
`e, f` — it is precisely what `B_never_square` forbids.  So `fourcomp_no_odd_prime` is a
one-branch theorem presented as a two-branch one.  (This is not an error: killing that branch is
the content of step (4).  But no witness for it exists, and none should be sought.) -/
theorem hsplit_left_branch_is_empty {e f : ℤ} {N : ℕ} (hc : IsCoprime e f) :
    ¬ (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = (N : ℤ) * u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = v ^ 2) := by
  rintro ⟨u, v, -, hv⟩
  exact B_never_square hc hv

/-- The headline the file's docstring claims — *"no odd prime survives"* — stated as an
explicit contradiction rather than as `N = 2`, so that it cannot be misread. -/
theorem no_odd_prime_explicit {e f : ℤ} {N : ℕ} (hc : IsCoprime e f) (hN : Nat.Prime N)
    (hodd : Odd N)
    (hsplit : (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = (N : ℤ) * u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = v ^ 2) ∨
              (∃ u v : ℤ, 2 * f ^ 2 - e ^ 2 = u ^ 2 ∧ 3 * f ^ 2 - e ^ 2 = (N : ℤ) * v ^ 2)) :
    False := by
  have h2 : N = 2 := fourcomp_no_odd_prime hc hN hsplit
  rw [h2] at hodd
  exact (by decide : ¬ Odd 2) hodd

end Erdos634.FCAudit

#print axioms Erdos634.FCAudit.not_both_even_nonvacuous
#print axioms Erdos634.FCAudit.even_iff_zmod4_both_directions
#print axioms Erdos634.FCAudit.B_never_square_nonvacuous
#print axioms Erdos634.FCAudit.A_square_forces_witness
#print axioms Erdos634.FCAudit.A_square_forces_at_witness
#print axioms Erdos634.FCAudit.A_square_forces_needs_coprimality
#print axioms Erdos634.FCAudit.A_square_parity_locked
#print axioms Erdos634.FCAudit.A_square_both_odd
#print axioms Erdos634.FCAudit.A_square_forces_mod8
#print axioms Erdos634.FCAudit.fourcomp_prime_eq_two_witness
#print axioms Erdos634.FCAudit.fourcomp_prime_eq_two_at_witness
#print axioms Erdos634.FCAudit.fourcomp_no_odd_prime_witness
#print axioms Erdos634.FCAudit.hsplit_left_branch_is_empty
#print axioms Erdos634.FCAudit.no_odd_prime_explicit
