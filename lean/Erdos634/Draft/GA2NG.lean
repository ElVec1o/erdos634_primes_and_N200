/-
GA2N, item (2a): **lemma G (constancy) at 5^r, r >= 2, with parity classes** (GA2Y_NOTES (I3)).

For r = t+2 >= 2, psi(z) constant (= c) over the primitive characters psi mod 5^r OF ONE PARITY eps forces
  (z = 1 mod 5^r and c = 1)  or  (z = -1 mod 5^r and c = eps).
Proof: one character-sum identity (`LemmaSGpp.sum_prim` + `GA2LPar.parsum`):
  2 sum_{prim, parity eps} psi(z) = S(z) + eps S(-z),  S(z) = phi(5^r)[z=1] - phi(5^(r-1))[z = 1 mod 5^(r-1)],
with #{prim, parity eps} = 8 * 5^t; the four cases of (z = 1 mod 5^(r-1)?, -z = 1 mod 5^(r-1)?) give c = 0 or
|c| = 1/4 (impossible) except the two stated.  `five_odd_R` is the r >= 2 analogue of `GA2LCore.five_odd`.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2LGroup

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NG

open Erdos634.GA2LPar Erdos634.GA2LCore
open Erdos634.LemmaSGpp (sum_prim)

instance neZero5 (r : ℕ) : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩

theorem pred_dvd5 (t : ℕ) : 5 ^ (t + 2 - 1) ∣ 5 ^ (t + 2) := pow_dvd_pow 5 (by omega)

theorem totient_A (t : ℕ) : (((5 ^ (t + 2)).totient : ℕ) : ℂ) = ((4 * 5 ^ (t + 1) : ℕ) : ℂ) := by
  rw [Nat.totient_prime_pow (by norm_num) (by omega)]
  have : t + 2 - 1 = t + 1 := by omega
  rw [this]; push_cast; ring

theorem totient_B (t : ℕ) : (((5 ^ (t + 2 - 1)).totient : ℕ) : ℂ) = ((4 * 5 ^ t : ℕ) : ℂ) := by
  have : t + 2 - 1 = t + 1 := by omega
  rw [this, Nat.totient_prime_pow (by norm_num) (by omega)]
  have : t + 1 - 1 = t := by omega
  rw [this]; push_cast; ring

theorem S_R (t : ℕ) (z : ℤ) (hz : IsUnit ((z : ZMod (5 ^ (t + 2))))) :
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (5 ^ (t + 2)) => χ.IsPrimitive),
        χ (z : ZMod (5 ^ (t + 2)))) =
      (if z ≡ 1 [ZMOD 5 ^ (t + 2)] then ((4 * 5 ^ (t + 1) : ℕ) : ℂ) else 0) -
        (if z ≡ 1 [ZMOD 5 ^ (t + 1)] then ((4 * 5 ^ t : ℕ) : ℂ) else 0) := by
  set g : (ZMod (5 ^ (t + 2)))ˣ := hz.unit with hg
  have hgz : (g : ZMod (5 ^ (t + 2))) = (z : ZMod _) := rfl
  have hS := sum_prim (q := 5) (v := t + 2) (by omega) g
  rw [hgz] at hS
  rw [hS]
  have e1 : ((z : ℤ) : ZMod (5 ^ (t + 2))) = 1 ↔ z ≡ 1 [ZMOD 5 ^ (t + 2)] := by
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]; push_cast; rfl
  have e0 : ((((z : ℤ) : ZMod (5 ^ (t + 2))).cast : ZMod (5 ^ (t + 2 - 1))) = 1) ↔
      z ≡ 1 [ZMOD 5 ^ (t + 1)] := by
    rw [ZMod.cast_intCast (pred_dvd5 t), ← Int.cast_one, ZMod.intCast_eq_intCast_iff]
    push_cast; exact Iff.rfl
  rw [totient_A, totient_B]
  by_cases h1 : z ≡ 1 [ZMOD 5 ^ (t + 2)] <;> by_cases h0 : z ≡ 1 [ZMOD 5 ^ (t + 1)] <;>
    simp only [e1, e0, h1, h0, if_true, if_false]

theorem key_R (t : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ)
    (hz : IsUnit ((z : ZMod (5 ^ (t + 2))))) :
    2 * ∑ χ ∈ PrimPar 5 (t + 2) ε, χ (z : ZMod (5 ^ (t + 2))) =
      ((if z ≡ 1 [ZMOD 5 ^ (t + 2)] then ((4 * 5 ^ (t + 1) : ℕ) : ℂ) else 0) -
        (if z ≡ 1 [ZMOD 5 ^ (t + 1)] then ((4 * 5 ^ t : ℕ) : ℂ) else 0)) +
      ε * ((if -z ≡ 1 [ZMOD 5 ^ (t + 2)] then ((4 * 5 ^ (t + 1) : ℕ) : ℂ) else 0) -
        (if -z ≡ 1 [ZMOD 5 ^ (t + 1)] then ((4 * 5 ^ t : ℕ) : ℂ) else 0)) := by
  have h := parsum (q := 5) (v := t + 2) ε hε (z : ZMod (5 ^ (t + 2)))
  have e : -((z : ℤ) : ZMod (5 ^ (t + 2))) = ((-z : ℤ) : ZMod (5 ^ (t + 2))) := by push_cast; rfl
  rw [e] at h
  rw [h, S_R t z hz, S_R t (-z) (by rw [← e]; exact hz.neg)]

theorem pow5_ge (t : ℕ) : (3 : ℤ) ≤ 5 ^ (t + 1) := by
  have : (5 : ℤ) ^ 1 ≤ 5 ^ (t + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  simpa using this.trans' (by norm_num : (3 : ℤ) ≤ 5 ^ 1)

theorem card_R (t : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    ((PrimPar 5 (t + 2) ε).card : ℂ) = 8 * 5 ^ t := by
  have h := key_R t ε hε 1 (by simp)
  have e1 : ∀ χ ∈ PrimPar 5 (t + 2) ε, χ (((1 : ℤ)) : ZMod (5 ^ (t + 2))) = 1 := by
    intro χ _; simp
  rw [sum_congr rfl e1, sum_const, nsmul_eq_mul, mul_one] at h
  have hA : (1 : ℤ) ≡ 1 [ZMOD 5 ^ (t + 2)] := rfl
  have hA' : (1 : ℤ) ≡ 1 [ZMOD 5 ^ (t + 1)] := rfl
  have hn2 : ¬ (-1 : ℤ) ≡ 1 [ZMOD 5 ^ (t + 2)] := L_negone (by
    have := pow5_ge (t + 1); simpa using this)
  have hn1 : ¬ (-1 : ℤ) ≡ 1 [ZMOD 5 ^ (t + 1)] := L_negone (pow5_ge t)
  rw [if_pos hA, if_pos hA', if_neg hn2, if_neg hn1] at h
  push_cast at h
  have : (5 : ℂ) ^ (t + 1) = 5 * 5 ^ t := by ring
  rw [this] at h
  linear_combination h / 2

theorem G_R (t : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ)
    (hz : IsUnit ((z : ZMod (5 ^ (t + 2))))) (c : ℂ)
    (hc : ∀ ψ ∈ PrimPar 5 (t + 2) ε, ψ (z : ZMod (5 ^ (t + 2))) = c) :
    (z ≡ 1 [ZMOD 5 ^ (t + 2)] ∧ c = 1) ∨ (z ≡ -1 [ZMOD 5 ^ (t + 2)] ∧ c = ε) := by
  have hk := key_R t ε hε z hz
  have hcard := card_R t ε hε
  rw [sum_congr rfl hc, sum_const, nsmul_eq_mul, hcard] at hk
  have hp5 : (5 : ℂ) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpos : (PrimPar 5 (t + 2) ε).Nonempty := by
    rw [← card_pos]
    have : ((PrimPar 5 (t + 2) ε).card : ℂ) ≠ 0 := by rw [hcard]; exact mul_ne_zero (by norm_num) hp5
    exact Nat.pos_of_ne_zero (fun h => this (by simp [h]))
  obtain ⟨ψ0, h0⟩ := hpos
  have hcn : ‖c‖ = 1 := by
    rw [← hc ψ0 h0]
    have := ψ0.unit_norm_eq_one hz.unit
    simpa using this
  have m1 : z ≡ 1 [ZMOD 5 ^ (t + 2)] → z ≡ 1 [ZMOD 5 ^ (t + 1)] := fun h =>
    h.of_dvd (pow_dvd_pow 5 (by omega))
  have m2 : -z ≡ 1 [ZMOD 5 ^ (t + 2)] → -z ≡ 1 [ZMOD 5 ^ (t + 1)] := fun h =>
    h.of_dvd (pow_dvd_pow 5 (by omega))
  have hboth : ¬ (z ≡ 1 [ZMOD 5 ^ (t + 1)] ∧ -z ≡ 1 [ZMOD 5 ^ (t + 1)]) := fun ⟨a, b⟩ =>
    L_both (pow5_ge t) a b
  have five : (5 : ℂ) ^ (t + 1) = 5 * 5 ^ t := by ring
  have quarter : ∀ w : ℂ, (w = 1 ∨ w = -1) → (4 * c + w) * (4 * 5 ^ t) = 0 → False := by
    intro w hw h
    have h4 : 4 * c + w = 0 := (mul_eq_zero.1 h).resolve_right (mul_ne_zero (by norm_num) hp5)
    have : c = -w / 4 := by linear_combination h4 / 4
    rw [this] at hcn
    rcases hw with rfl | rfl <;> norm_num at hcn
  by_cases i1' : z ≡ 1 [ZMOD 5 ^ (t + 1)]
  · have j1' : ¬ (-z ≡ 1 [ZMOD 5 ^ (t + 1)]) := fun h => hboth ⟨i1', h⟩
    have j1 : ¬ (-z ≡ 1 [ZMOD 5 ^ (t + 2)]) := fun h => j1' (m2 h)
    by_cases i1 : z ≡ 1 [ZMOD 5 ^ (t + 2)]
    · rw [if_pos i1, if_pos i1', if_neg j1, if_neg j1'] at hk
      push_cast at hk
      rw [five] at hk
      left; refine ⟨i1, ?_⟩
      apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) hp5)
      linear_combination hk
    · rw [if_neg i1, if_pos i1', if_neg j1, if_neg j1'] at hk
      push_cast at hk
      exfalso
      exact quarter 1 (Or.inl rfl) (by linear_combination hk)
  · by_cases j1' : -z ≡ 1 [ZMOD 5 ^ (t + 1)]
    · have i1 : ¬ (z ≡ 1 [ZMOD 5 ^ (t + 2)]) := fun h => i1' (m1 h)
      by_cases j1 : -z ≡ 1 [ZMOD 5 ^ (t + 2)]
      · rw [if_neg i1, if_neg i1', if_pos j1, if_pos j1'] at hk
        push_cast at hk
        rw [five] at hk
        right; refine ⟨L_neg_one_iff.1 j1, ?_⟩
        rcases hε with rfl | rfl
        · apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) hp5)
          linear_combination hk
        · apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) hp5)
          linear_combination hk
      · rw [if_neg i1, if_neg i1', if_neg j1, if_pos j1'] at hk
        push_cast at hk
        exfalso
        rcases hε with rfl | rfl
        · exact quarter 1 (Or.inl rfl) (by linear_combination hk)
        · exact quarter (-1) (Or.inr rfl) (by linear_combination hk)
    · have i1 : ¬ (z ≡ 1 [ZMOD 5 ^ (t + 2)]) := fun h => i1' (m1 h)
      have j1 : ¬ (-z ≡ 1 [ZMOD 5 ^ (t + 2)]) := fun h => j1' (m2 h)
      rw [if_neg i1, if_neg i1', if_neg j1, if_neg j1'] at hk
      exfalso
      have hc0 : c = 0 := by
        have : (16 * 5 ^ t : ℂ) * c = 0 := by linear_combination hk
        exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (by norm_num) hp5)
      rw [hc0, norm_zero] at hcn; exact zero_ne_one hcn

/-- r >= 2 analogue of `GA2LCore.five_odd`. -/
theorem five_odd_R (t : ℕ) (z : ℤ) (hz : IsUnit ((z : ZMod (5 ^ (t + 2))))) (c : ℂ)
    (hc : ∀ ψ ∈ PrimPar 5 (t + 2) (-1), ψ (z : ZMod (5 ^ (t + 2))) = c) :
    (z ≡ 1 [ZMOD 5 ^ (t + 2)] ∧ c = 1) ∨ (z ≡ -1 [ZMOD 5 ^ (t + 2)] ∧ c = -1) :=
  G_R t (-1) (Or.inr rfl) z hz c hc

/-- Both parity classes of primitive characters mod 5^(t+2) are nonempty (8 * 5^t each): witness for `G_R`. -/
theorem nonempty_R (t : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) : (PrimPar 5 (t + 2) ε).Nonempty := by
  rw [← card_pos]
  have h := card_R t ε hε
  have : ((PrimPar 5 (t + 2) ε).card : ℂ) ≠ 0 := by
    rw [h]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  exact Nat.pos_of_ne_zero (fun h0 => this (by simp [h0]))

end Erdos634.GA2NG

#print axioms Erdos634.GA2NG.card_R
#print axioms Erdos634.GA2NG.G_R
#print axioms Erdos634.GA2NG.five_odd_R
#print axioms Erdos634.GA2NG.nonempty_R
