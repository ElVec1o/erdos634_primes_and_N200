import Mathlib.Tactic

/-!
# The offsets lemma as one arithmetic statement

The offsets lemma concerns a number of the form

    x = [ j(3f² − 1) + Σ εᵢ ] / (2f) + k f,     εᵢ ∈ { −(f² − 1), 3f² − 1 },   i < j,

and concludes, from `x` being an integer and `j < f`, that every `εᵢ` equals `−(f² − 1)` and that
`x = (j + k) f`.  `OffsetInterior` and `OffsetForcing` hold the steps (the residues, the
divisibility in either parity, `q = 0`).  Here is the statement itself, with the sum over the
levels, for every `f ≥ 2`:

* `offsets_exact` : if `2f·(x − k f) = j(3f² − 1) + Σ εᵢ` with every `εᵢ` one of the two values
  and `j < f`, then every `εᵢ = −(f² − 1)` and `x = (j + k) f`.

The proof: with `q` the number of levels taking `3f² − 1`, the right
side is `2f²·(j − q) + 2q(3f² − 1)`, so `f ∣ q(3f² − 1)`, hence `f ∣ q`, and `q ≤ j < f`.

No statement here is about a tiling.  Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.OffsetsExact

open Finset

/-- The sum of the offsets, with `q` the number of levels taking the value `3f² − 1`. -/
theorem sum_eps (f : ℤ) (j : ℕ) (ε : Fin j → ℤ)
    (hε : ∀ i, ε i = -(f ^ 2 - 1) ∨ ε i = 3 * f ^ 2 - 1) :
    ∑ i, ε i = -(f ^ 2 - 1) * ((j : ℤ) - ((univ.filter fun i => ε i = 3 * f ^ 2 - 1).card : ℤ))
      + (3 * f ^ 2 - 1) * ((univ.filter fun i => ε i = 3 * f ^ 2 - 1).card : ℤ) := by
  classical
  have hsplit : ∑ i, ε i = ∑ i, (-(f ^ 2 - 1) + (if ε i = 3 * f ^ 2 - 1 then 4 * f ^ 2 - 2 else 0)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hε i with h | h
    · by_cases h2 : ε i = 3 * f ^ 2 - 1
      · rw [if_pos h2]; rw [h] at h2; rw [h]; linarith
      · rw [if_neg h2, h]; ring
    · rw [if_pos h, h]; ring
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero]
  simp only [nsmul_eq_mul, add_zero]
  ring

/-- **`lem:offsets`, the arithmetic statement.** -/
theorem offsets_exact (f : ℤ) (hf : 2 ≤ f) (j : ℕ) (hj : (j : ℤ) < f) (k x : ℤ) (ε : Fin j → ℤ)
    (hε : ∀ i, ε i = -(f ^ 2 - 1) ∨ ε i = 3 * f ^ 2 - 1)
    (hx : 2 * f * (x - k * f) = (j : ℤ) * (3 * f ^ 2 - 1) + ∑ i, ε i) :
    (∀ i, ε i = -(f ^ 2 - 1)) ∧ x = ((j : ℤ) + k) * f := by
  classical
  set q : ℕ := (univ.filter fun i => ε i = 3 * f ^ 2 - 1).card with hq
  have hqj : q ≤ j := by
    have := Finset.card_filter_le (univ : Finset (Fin j)) (fun i => ε i = 3 * f ^ 2 - 1)
    simpa [hq] using this
  have hsum := sum_eps f j ε hε
  rw [← hq] at hsum
  -- `f * (x − k f − (j − q) f) = q (3 f² − 1)`
  have hmain : f * (x - k * f - ((j : ℤ) - q) * f - 3 * f * q) = -(q : ℤ) := by
    have hf0 : (2 : ℤ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ hf0
    rw [hsum] at hx
    linear_combination hx
  have hdvd : f ∣ (q : ℤ) := by
    have : f ∣ -(q : ℤ) := ⟨_, hmain.symm⟩
    exact (dvd_neg).mp this
  have hq0 : q = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    have hqf : (q : ℤ) < f := lt_of_le_of_lt (by exact_mod_cast hqj) hj
    have hq_nn : (0 : ℤ) ≤ q := Int.natCast_nonneg q
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [ht0, mul_zero] at ht
    exact_mod_cast ht
  have hall : ∀ i, ε i = -(f ^ 2 - 1) := by
    intro i
    rcases hε i with h | h
    · exact h
    · exfalso
      have hmem : i ∈ univ.filter fun i => ε i = 3 * f ^ 2 - 1 := by simp [h]
      have : 0 < q := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
  refine ⟨hall, ?_⟩
  rw [hq0] at hmain
  simp only [Nat.cast_zero, sub_zero, mul_zero, neg_zero] at hmain
  have hf0 : f ≠ 0 := by omega
  have := (mul_eq_zero.mp hmain).resolve_left hf0
  linarith

/-- Non-vacuity: `f = 3`, `j = 2`, `k = 1`, both levels at `−(f² − 1) = −8`; `x = 9`. -/
example : (2 : ℤ) * 3 * (9 - 1 * 3) = ((2 : ℕ) : ℤ) * (3 * 3 ^ 2 - 1) + ∑ _i : Fin 2, (-(3 ^ 2 - 1) : ℤ) := by
  simp

end Erdos634.Draft.OffsetsExact
