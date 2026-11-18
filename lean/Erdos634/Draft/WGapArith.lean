/-
Draft/WGapArith.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P1).
Not imported by any aggregate.

Module W0 of the W-gap Lean plan (PROOF.md P12): arithmetic of the semigroup `S = <a, b, c>` of the tile
`(a, b, c) = (e f, f^2 - e^2, f^2)`, coprime `1 ≤ e < f`, stated over `ℤ` (no natural subtraction).

* `WS e f n`        : `n` is a non-negative integer combination of `a, b, c` (so `0 ∈ S`).
* `relation_lattice`: PROOF Lemma 1.1/1.2: every integer relation `x a + y b + z c = 0` is `u R1 + w R2` with
                      `R1 = (f, 0, -e)`, `R2 = (d, -f, d)`, `d = f - e`; and conversely (`R1`, `R2` are relations).
* `nonmem_table`    : PROOF Lemma 1.3 as non-membership: for `1 ≤ m ≤ f - 1`,
                      `m c - b, m b - a, m b - c, m a - b, m a - c ∉ S` (so none is `0` either).
                      Derived from the existing nat-form `SideRunGArith.A1 / A5 / Aa` (the residue proofs of E2R6; the
                      lattice proof of PROOF.md 1.3 is not used).
* `c_sub_b_nonmem`, `c_sub_a_nonmem` (`e ≥ 2`): PROOF Lemma 1.5(iv).
* `rep_mc_no_b`     : PROOF Lemma 1.4: representations of `m c` with `y = 0` are `(u f, 0, m - u e)`.
* `sharp_fb`, `sharp_fc`, `sharp_fa`: negative control at `m = f`: each of the three families fails at `m = f`.
* Instances at `(e, f) = (2, 3)`: the table at `m = 1, 2` and the controls at `m = 3` by explicit representations.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.SideRunGArith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapArith
open Erdos634.Draft.WStripArith

/-- `n ∈ S = {x a + y b + z c}` with `a = e f`, `b = f^2 - e^2`, `c = f^2`, over `ℤ`. -/
def WS (e f : ℕ) (n : ℤ) : Prop :=
  ∃ x y z : ℕ, (x : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z : ℤ) * (f : ℤ) ^ 2 = n

theorem cast_b {e f : ℕ} (hef : e < f) :
    ((f ^ 2 - e ^ 2 : ℕ) : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
  rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]
  push_cast
  ring

/-- the integer equation gives the nat-form equation used by `SideRunGArith` -/
theorem nat_eq_of_int_eq {e f x y z n : ℕ} (hef : e < f)
    (h : (x : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z : ℤ) * (f : ℤ) ^ 2 = (n : ℤ)) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = n := by
  have hb := cast_b hef
  have : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℤ) = (n : ℤ) := by
    push_cast
    rw [hb]
    exact h
  exact_mod_cast this

/-! ## Lemma 1.1 / 1.2: the relation lattice -/

/-- `R1 = (f, 0, -e)` and `R2 = (d, -f, d)`, `d = f - e`, are relations. -/
theorem R1_rel (e f : ℕ) :
    (f : ℤ) * ((e : ℤ) * f) + 0 * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (-(e : ℤ)) * (f : ℤ) ^ 2 = 0 := by ring

theorem R2_rel (e f : ℕ) :
    ((f : ℤ) - e) * ((e : ℤ) * f) + (-(f : ℤ)) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + ((f : ℤ) - e) * (f : ℤ) ^ 2 = 0 := by
  ring

/-- **Lemma 1.1** (relation lattice): every integer relation among `a, b, c` is an integer combination of
`R1 = (f, 0, -e)` and `R2 = (f - e, -f, f - e)`. -/
theorem relation_lattice {e f : ℕ} (hf0 : 0 < f) (hco : Nat.Coprime e f) (x y z : ℤ)
    (h : x * ((e : ℤ) * f) + y * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + z * (f : ℤ) ^ 2 = 0) :
    ∃ u w : ℤ, x = u * f + w * ((f : ℤ) - e) ∧ y = -w * f ∧ z = -u * e + w * ((f : ℤ) - e) := by
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * y :=
    ⟨y * f + x * e + z * f, by linear_combination (-1 : ℤ) * h⟩
  have hdy : (f : ℤ) ∣ y := dvd_of_coprime_mul_sq hco hd
  obtain ⟨w1, hw1⟩ := hdy
  -- y = f * w1; put w = -w1
  have hf : (f : ℤ) ≠ 0 := by
    exact_mod_cast hf0.ne'
  have h2 : x * (e : ℤ) + w1 * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + z * f = 0 := by
    apply mul_left_cancel₀ hf
    rw [hw1] at h
    linear_combination h
  have hd2 : (f : ℤ) ∣ (e : ℤ) * (x - w1 * e) :=
    ⟨-w1 * f - z, by linear_combination h2⟩
  have hd3 : (f : ℤ) ∣ x - w1 * e := dvd_of_coprime_mul hco hd2
  obtain ⟨u', hu'⟩ := hd3
  refine ⟨u' + w1, -w1, ?_, ?_, ?_⟩
  · linear_combination hu'
  · linear_combination hw1
  · have h3 : (f : ℤ) * (z + w1 * f + e * u') = 0 := by
      have hx : x = f * u' + w1 * e := by linarith
      rw [hx] at h2
      linear_combination h2
    have h4 : z + w1 * f + e * u' = 0 := by
      rcases mul_eq_zero.mp h3 with h5 | h5
      · exact absurd h5 hf
      · exact h5
    linear_combination h4

/-! ## Lemma 1.3 as non-membership (m ≤ f - 1) -/

section table
variable {e f : ℕ}

theorem nonmem_mc_sub_b (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ f - 1) :
    ¬ WS e f ((m : ℤ) * (f : ℤ) ^ 2 - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
  rintro ⟨x, y, z, h⟩
  have h' : (x : ℤ) * ((e : ℤ) * f) + ((y + 1 : ℕ) : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z : ℤ) * (f : ℤ) ^ 2
      = ((m * f ^ 2 : ℕ) : ℤ) := by
    push_cast
    linarith
  have := SideRunGArith.A5 he hef hco hm1 hm (nat_eq_of_int_eq hef h')
  omega

theorem nonmem_mb_sub_a (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ f - 1) :
    ¬ WS e f ((m : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) - ((e : ℤ) * f)) := by
  rintro ⟨x, y, z, h⟩
  have h' : ((x + 1 : ℕ) : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z : ℤ) * (f : ℤ) ^ 2
      = ((m * (f ^ 2 - e ^ 2) : ℕ) : ℤ) := by
    push_cast
    rw [cast_b hef]
    linarith
  have := (SideRunGArith.A1 he hef hco hm1 hm (nat_eq_of_int_eq hef h')).1
  omega

theorem nonmem_mb_sub_c (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ f - 1) :
    ¬ WS e f ((m : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) - (f : ℤ) ^ 2) := by
  rintro ⟨x, y, z, h⟩
  have h' : (x : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + ((z + 1 : ℕ) : ℤ) * (f : ℤ) ^ 2
      = ((m * (f ^ 2 - e ^ 2) : ℕ) : ℤ) := by
    push_cast
    rw [cast_b hef]
    linarith
  have := (SideRunGArith.A1 he hef hco hm1 hm (nat_eq_of_int_eq hef h')).2.2
  omega

theorem nonmem_ma_sub_b (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ f - 1) :
    ¬ WS e f ((m : ℤ) * ((e : ℤ) * f) - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
  rintro ⟨x, y, z, h⟩
  have h' : (x : ℤ) * ((e : ℤ) * f) + ((y + 1 : ℕ) : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z : ℤ) * (f : ℤ) ^ 2
      = ((m * (e * f) : ℕ) : ℤ) := by
    push_cast
    linarith
  have := (SideRunGArith.Aa he hef hco hm1 hm (nat_eq_of_int_eq hef h')).2.1
  omega

theorem nonmem_ma_sub_c (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ f - 1) :
    ¬ WS e f ((m : ℤ) * ((e : ℤ) * f) - (f : ℤ) ^ 2) := by
  rintro ⟨x, y, z, h⟩
  have h' : (x : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + ((z + 1 : ℕ) : ℤ) * (f : ℤ) ^ 2
      = ((m * (e * f) : ℕ) : ℤ) := by
    push_cast
    linarith
  have := (SideRunGArith.Aa he hef hco hm1 hm (nat_eq_of_int_eq hef h')).2.2
  omega

/-- **Lemma 1.3 (the non-membership table)**: for coprime `1 ≤ e < f` and `1 ≤ m ≤ f - 1`,
none of `m c - b, m b - a, m b - c, m a - b, m a - c` lies in `S` (in particular none is `0`). -/
theorem nonmem_table (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ f - 1) :
    ¬ WS e f ((m : ℤ) * (f : ℤ) ^ 2 - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) ∧
    ¬ WS e f ((m : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) - ((e : ℤ) * f)) ∧
    ¬ WS e f ((m : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) - (f : ℤ) ^ 2) ∧
    ¬ WS e f ((m : ℤ) * ((e : ℤ) * f) - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) ∧
    ¬ WS e f ((m : ℤ) * ((e : ℤ) * f) - (f : ℤ) ^ 2) :=
  ⟨nonmem_mc_sub_b he hef hco hm1 hm, nonmem_mb_sub_a he hef hco hm1 hm, nonmem_mb_sub_c he hef hco hm1 hm,
    nonmem_ma_sub_b he hef hco hm1 hm, nonmem_ma_sub_c he hef hco hm1 hm⟩

/-- `c - b ∉ S` (`= e^2`; PROOF 1.5(iv)): the case `m = 1` of the table. -/
theorem c_sub_b_nonmem (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ¬ WS e f ((f : ℤ) ^ 2 - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
  have h := nonmem_mc_sub_b he hef hco (m := 1) le_rfl (by omega)
  simpa using h

/-! ## Lemma 1.4: representations of `m c` without `b` -/

/-- A representation of `m c` with `y = 0` is `(u f, 0, m - u e)`: `x = u f` and `z + u e = m`. -/
theorem rep_mc_no_b (hef : e < f) (hco : Nat.Coprime e f) {m x z : ℕ}
    (h : (x : ℤ) * ((e : ℤ) * f) + (z : ℤ) * (f : ℤ) ^ 2 = (m : ℤ) * (f : ℤ) ^ 2) :
    ∃ u : ℕ, x = u * f ∧ z + u * e = m := by
  have hf : (0 : ℤ) < f := by exact_mod_cast (show 0 < f by omega)
  have h1 : (x : ℤ) * e + (z : ℤ) * f = (m : ℤ) * f := by
    apply mul_left_cancel₀ hf.ne'
    linear_combination h
  have hd : (f : ℤ) ∣ (e : ℤ) * x := ⟨m - z, by linear_combination h1⟩
  have hd2 : (f : ℤ) ∣ (x : ℤ) := dvd_of_coprime_mul hco hd
  obtain ⟨u, hu⟩ := hd2
  have hu0 : 0 ≤ u := by
    by_contra hc
    push_neg at hc
    have := mul_neg_of_pos_of_neg hf hc
    have : (0 : ℤ) ≤ x := by positivity
    linarith
  refine ⟨u.toNat, ?_, ?_⟩
  · have : (x : ℤ) = ((u.toNat * f : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hu0, hu]
      ring
    exact_mod_cast this
  · have : ((z + u.toNat * e : ℕ) : ℤ) = (m : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hu0]
      rw [hu] at h1
      apply mul_left_cancel₀ hf.ne'
      linear_combination h1
    exact_mod_cast this

/-- `c - a ∉ S` for `e ≥ 2` (PROOF 1.5(iv)). -/
theorem c_sub_a_nonmem (he : 2 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ¬ WS e f ((f : ℤ) ^ 2 - ((e : ℤ) * f)) := by
  rintro ⟨x, y, z, h⟩
  have h' : ((x + 1 : ℕ) : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z : ℤ) * (f : ℤ) ^ 2
      = ((1 * f ^ 2 : ℕ) : ℤ) := by
    push_cast
    linarith
  have hy := SideRunGArith.A5 (by omega) hef hco le_rfl (by omega) (nat_eq_of_int_eq hef h')
  subst hy
  have h0 : ((x + 1 : ℕ) : ℤ) * ((e : ℤ) * f) + (z : ℤ) * (f : ℤ) ^ 2 = ((1 : ℕ) : ℤ) * (f : ℤ) ^ 2 := by
    have : ((1 * f ^ 2 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) * (f : ℤ) ^ 2 := by push_cast; ring
    rw [this] at h'
    simpa using h'
  obtain ⟨u, hu1, hu2⟩ := rep_mc_no_b hef hco h0
  -- x + 1 = u f, z + u e = 1 with e ≥ 2: u = 0, contradicting x + 1 ≥ 1
  have hu0 : u = 0 := by
    by_contra hne
    have : 1 ≤ u := Nat.pos_of_ne_zero hne
    nlinarith
  subst hu0
  omega

/-! ## Negative control at `m = f` -/

theorem sharp_fb (he : 1 ≤ e) (hef : e < f) :
    WS e f ((f : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) - ((e : ℤ) * f)) := by
  refine ⟨f - e - 1, 0, f - e, ?_⟩
  have h1 : ((f - e - 1 : ℕ) : ℤ) = (f : ℤ) - e - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((f - e : ℕ) : ℤ) = (f : ℤ) - e := by
    rw [Nat.cast_sub (by omega)]
  rw [h1, h2]
  push_cast
  ring

theorem sharp_fc (he : 1 ≤ e) (hef : e < f) :
    WS e f ((f : ℤ) * (f : ℤ) ^ 2 - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
  refine ⟨e, f - 1, 0, ?_⟩
  have h1 : ((f - 1 : ℕ) : ℤ) = (f : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h1]
  push_cast
  ring

theorem sharp_fa (he : 1 ≤ e) (hef : e < f) :
    WS e f ((f : ℤ) * ((e : ℤ) * f) - (f : ℤ) ^ 2) := by
  refine ⟨0, 0, e - 1, ?_⟩
  have h1 : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h1]
  push_cast
  ring

end table

/-! ## Instances at `(e, f) = (2, 3)`: `a = 6, b = 5, c = 9` -/

example : Nat.Coprime 2 3 := by decide

/-- the table at `m = 2` (so `2c - b = 13`, `2b - a = 4`, `2b - c = 1`, `2a - b = 7`, `2a - c = 3`) -/
example :
    ¬ WS 2 3 (((2 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) ^ 2 - (((3 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) ^ 2)) ∧
    ¬ WS 2 3 (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) ^ 2) - (((2 : ℕ) : ℤ) * ((3 : ℕ) : ℤ))) ∧
    ¬ WS 2 3 (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) ^ 2) - ((3 : ℕ) : ℤ) ^ 2) ∧
    ¬ WS 2 3 (((2 : ℕ) : ℤ) * (((2 : ℕ) : ℤ) * ((3 : ℕ) : ℤ)) - (((3 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) ^ 2)) ∧
    ¬ WS 2 3 (((2 : ℕ) : ℤ) * (((2 : ℕ) : ℤ) * ((3 : ℕ) : ℤ)) - ((3 : ℕ) : ℤ) ^ 2) :=
  nonmem_table (e := 2) (f := 3) (by norm_num) (by norm_num) (by decide) (m := 2) (by norm_num) (by norm_num)

/-- negative control: at `m = f = 3` the three families fail: `3 b - a = 9 = c`, `3 c - b = 22 = 2a + 2b`,
`3 a - c = 9 = c` all lie in `S`. -/
example :
    WS 2 3 (((3 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) ^ 2) - (((2 : ℕ) : ℤ) * ((3 : ℕ) : ℤ))) ∧
    WS 2 3 (((3 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) ^ 2 - (((3 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) ^ 2)) ∧
    WS 2 3 (((3 : ℕ) : ℤ) * (((2 : ℕ) : ℤ) * ((3 : ℕ) : ℤ)) - ((3 : ℕ) : ℤ) ^ 2) :=
  ⟨sharp_fb (e := 2) (f := 3) (by norm_num) (by norm_num), sharp_fc (e := 2) (f := 3) (by norm_num) (by norm_num),
    sharp_fa (e := 2) (f := 3) (by norm_num) (by norm_num)⟩

#print axioms nonmem_table
#print axioms relation_lattice
#print axioms c_sub_a_nonmem
#print axioms rep_mc_no_b

end Erdos634.Draft.WGapArith
