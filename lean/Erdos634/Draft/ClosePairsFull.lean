/-
Draft/ClosePairsFull.lean -- the extra base columns at close pairs.

A column is a solution `(x, y, z) ∈ ℕ³` of the base equation of the `m = 1` base-`β` target of the member `(e, f)`,
`x·ef + y(f² − e²) + z f² = e(3f² − e²)` (`IsCol`); it is extra when `y > e`.

General statements (coprime `1 ≤ e < f`):
* `col_reduce`, `col_of_reduced`: `(x, y, z)` is an extra column iff `y = e + kf` with `k ≥ 1` and
  `xe + zf = 2ef − k(f² − e²)`;
* `no_x_zero`: no extra column has `x = 0`;
* `size_iff`, `sep_iff`: the size constraint is `k(f² − e²) ≤ 2ef`, and it excludes `k ≥ 1` exactly when
  `f² > 2ef + e²`;
* `k_one_pinned`, `k_one_iff`: at `k = 1` the column is `(e, e + f, 2e − f)`; it has `z ≥ 1` iff `f ≤ 2e − 1`;
* `z_lt_e`, `one_per_k`: every column with `k ≥ 1` has `z < e`, and there is at most one column for each `k`;
* `close_pairs_infinite`: there are infinitely many coprime close pairs.

Enumerations (`colList`, complete by `mem_colList`; all by kernel evaluation):
* `e ≤ 9`, `f ≤ 15`: 71 extra columns, 9 with `z = 0`, 8 more with `x + z ≤ 3`, 54 left, the first `(3, 7, 2)` at
  `(3, 4)`, all with `x < f`;
* close pairs with `e ≤ 25`, `f ≤ 59`: 655 surviving columns at 198 members; the surviving `k` are `1, …, n`; the
  bound `k ≤ ⌊(2ef − 3e − f)/(f² − e²)⌋` is attained at 186 members, and at the other 12 the reduced equation has no
  solution with `x, z ≥ 1` at that `k`.

No sorry, no native_decide.
-/
import Erdos634.Draft.RemClosePairFormal

namespace Erdos634.Draft.ClosePairsFull

open Erdos634.Draft.RemClosePairFormal

/-- the base equation of the `m = 1` target for a column `(x, y, z)` -/
def IsCol (e f x y z : ℕ) : Prop :=
  x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)

instance (e f x y z : ℕ) : Decidable (IsCol e f x y z) := by unfold IsCol; infer_instance

/-! ## The reduced equation -/

/-- an extra column has `y = e + kf`, `k ≥ 1`, and satisfies the reduced equation -/
theorem col_reduce {e f x y z : ℕ} (hco : Nat.Coprime e f) (hef : e < f) (hy : e < y)
    (h : IsCol e f x y z) :
    ∃ k : ℕ, 1 ≤ k ∧ y = e + k * f ∧
      (x : ℤ) * e + (z : ℤ) * f = 2 * (e : ℤ) * f - (k : ℤ) * ((f : ℤ) * f - (e : ℤ) * e) := by
  unfold IsCol at h
  have h1 : e * e ≤ f * f := by nlinarith
  have h3 : e * e ≤ 3 * (f * f) := by nlinarith
  have hcast : (x : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) * f - (e : ℤ) * e) +
      (z : ℤ) * ((f : ℤ) * f) = (e : ℤ) * (3 * ((f : ℤ) * f) - (e : ℤ) * e) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h3] at this
    linarith [this]
  obtain ⟨k', hk'⟩ := y_form_nat hco hef h
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hyZ : (e : ℤ) < y := by exact_mod_cast hy
  have hk'pos : 0 < k' := by
    rcases le_or_gt k' 0 with hneg | hpos
    · exfalso
      have : (f : ℤ) * k' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hfpos.le hneg
      linarith
    · exact hpos
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk'pos.le
  have hk0 : 0 < k := by exact_mod_cast hk'pos
  have hyk' : (y : ℤ) = e + k * f := by linarith
  have hyk : y = e + k * f := by exact_mod_cast hyk'
  refine ⟨k, hk0, hyk, ?_⟩
  rw [hyk'] at hcast
  have hzero : (f : ℤ) * ((x : ℤ) * e + (z : ℤ) * f
      - (2 * (e : ℤ) * f - (k : ℤ) * ((f : ℤ) * f - (e : ℤ) * e))) = 0 := by
    linear_combination hcast
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact absurd h0 hfpos.ne'
  · linear_combination h0

/-- conversely -/
theorem col_of_reduced {e f x k z : ℕ} (hef : e < f)
    (h : (x : ℤ) * e + (z : ℤ) * f = 2 * (e : ℤ) * f - (k : ℤ) * ((f : ℤ) * f - (e : ℤ) * e)) :
    IsCol e f x (e + k * f) z := by
  have h1 : e * e ≤ f * f := by nlinarith
  have h3 : e * e ≤ 3 * (f * f) := by nlinarith
  unfold IsCol
  zify [h1, h3]
  linear_combination (f : ℤ) * h

/-- **No extra column has `x = 0`.** -/
theorem no_x_zero {e f y z : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) (hy : e < y)
    (h : IsCol e f 0 y z) : False := by
  obtain ⟨k, hk1, -, hred⟩ := col_reduce hco hef hy h
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hepos : (0 : ℤ) < e := by exact_mod_cast (by omega : 0 < e)
  have hefZ : (e : ℤ) < f := by exact_mod_cast hef
  have hkpos : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
  have hred' : (z : ℤ) * f = 2 * (e : ℤ) * f - (k : ℤ) * ((f : ℤ) * f - (e : ℤ) * e) := by
    have := hred
    push_cast at this
    linarith
  have hdvd : (f : ℤ) ∣ (k : ℤ) * ((e : ℤ) * e) :=
    ⟨(z : ℤ) - 2 * e + k * f, by linear_combination (-1 : ℤ) * hred'⟩
  have hcop : IsCoprime (f : ℤ) ((e : ℤ) * e) := by
    have : IsCoprime (f : ℤ) (e : ℤ) := (Nat.isCoprime_iff_coprime.mpr hco).symm
    exact this.mul_right this
  have hfk : (f : ℤ) ∣ (k : ℤ) := hcop.dvd_of_dvd_mul_right hdvd
  have hkf : (f : ℤ) ≤ k := Int.le_of_dvd hkpos hfk
  have hz0 : (0 : ℤ) ≤ (z : ℤ) * f := mul_nonneg (by positivity) hfpos.le
  have hb : (f : ℤ) + e ≤ (f : ℤ) * f - e * e := by
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (f : ℤ) + e) (by linarith : (0 : ℤ) ≤ (f : ℤ) - e - 1)]
  have h5 : (f : ℤ) * ((f : ℤ) * f - e * e) ≤ k * ((f : ℤ) * f - e * e) :=
    mul_le_mul_of_nonneg_right hkf (by linarith)
  have h6 : (f : ℤ) * ((f : ℤ) + e) ≤ f * ((f : ℤ) * f - e * e) := mul_le_mul_of_nonneg_left hb hfpos.le
  have h7 : (f : ℤ) * (2 * e) < f * ((f : ℤ) + e) := mul_lt_mul_of_pos_left (by linarith) hfpos
  linarith

/-- the size constraint `y b ≤ e(3f² − e²)` at `y = e + kf` reads `k b ≤ 2ef` -/
theorem size_iff (e f k : ℤ) (hf : 0 < f) :
    (e + k * f) * (f * f - e * e) ≤ e * (3 * (f * f) - e * e) ↔ k * (f * f - e * e) ≤ 2 * e * f := by
  constructor
  · intro h
    have h' : f * (k * (f * f - e * e)) ≤ f * (2 * e * f) := by linarith
    exact le_of_mul_le_mul_left h' hf
  · intro h
    have h' := mul_le_mul_of_nonneg_left h hf.le
    linarith

/-- the size constraint excludes every `k ≥ 1` exactly at the separated pairs -/
theorem sep_iff (e f : ℤ) : 2 * e * f < f * f - e * e ↔ 2 * e * f + e * e < f * f := by
  constructor <;> intro h <;> linarith

/-! ## `k = 1`, and uniqueness for each `k` -/

/-- at `k = 1` the column is `(e, e + f, 2e − f)` -/
theorem k_one_pinned {e f x z : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (h : (x : ℤ) * e + (z : ℤ) * f = 2 * (e : ℤ) * f - 1 * ((f : ℤ) * f - (e : ℤ) * e)) :
    x = e ∧ z + f = 2 * e := by
  have hcop : IsCoprime (f : ℤ) (e : ℤ) := (Nat.isCoprime_iff_coprime.mpr hco).symm
  obtain ⟨t, ht⟩ := Erdos634.Frontier.column_x_congruence (e : ℤ) f 1 x z hcop h
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hepos : (0 : ℤ) < e := by exact_mod_cast (by omega : 0 < e)
  have hefZ : (e : ℤ) < f := by exact_mod_cast hef
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hx : (x : ℤ) = e + f * t := by linarith
  have hzt : t * (e : ℤ) + z = 2 * e - f := by
    have h2 : (f : ℤ) * (t * (e : ℤ) + z) = f * (2 * e - f) := by
      rw [hx] at h
      linear_combination h
    exact mul_left_cancel₀ hfpos.ne' h2
  have ht0 : t = 0 := by
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · exfalso
      have h1 : t ≤ -1 := by omega
      have h2 : (f : ℤ) * t ≤ f * (-1) := mul_le_mul_of_nonneg_left h1 hfpos.le
      linarith
    · exact hzero
    · exfalso
      have h1 : 1 ≤ t := by omega
      have h2 : (1 : ℤ) * e ≤ t * e := mul_le_mul_of_nonneg_right h1 hepos.le
      linarith
  subst ht0
  constructor
  · have : (x : ℤ) = e := by linarith
    exact_mod_cast this
  · have : (z : ℤ) + f = 2 * e := by linarith
    exact_mod_cast this

/-- the `k = 1` column has `z ≥ 1` exactly when `f ≤ 2e − 1` -/
theorem k_one_iff {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    (∃ x z : ℕ, 1 ≤ z ∧
      (x : ℤ) * e + (z : ℤ) * f = 2 * (e : ℤ) * f - 1 * ((f : ℤ) * f - (e : ℤ) * e)) ↔ f + 1 ≤ 2 * e := by
  constructor
  · rintro ⟨x, z, hz, h⟩
    obtain ⟨-, h2⟩ := k_one_pinned hco he hef h
    omega
  · intro h
    refine ⟨e, 2 * e - f, by omega, ?_⟩
    push_cast [Nat.cast_sub (by omega : f ≤ 2 * e)]
    ring

/-- every column with `k ≥ 1` has `z < e` -/
theorem z_lt_e {e f k x z : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) (hk : 1 ≤ k)
    (h : (x : ℤ) * e + (z : ℤ) * f = 2 * (e : ℤ) * f - (k : ℤ) * ((f : ℤ) * f - (e : ℤ) * e)) : z < e := by
  have hcop : IsCoprime (f : ℤ) (e : ℤ) := (Nat.isCoprime_iff_coprime.mpr hco).symm
  obtain ⟨u, hu⟩ := Erdos634.Frontier.column_x_congruence (e : ℤ) f k x z hcop h
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hepos : (0 : ℤ) < e := by exact_mod_cast (by omega : 0 < e)
  have hefZ : (e : ℤ) < f := by exact_mod_cast hef
  have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hx : (x : ℤ) = k * e + f * u := by linarith
  have hu1 : 1 - (k : ℤ) ≤ u := by
    rcases le_or_gt (1 - (k : ℤ)) u with h1 | h1
    · exact h1
    · exfalso
      have h2 : u ≤ -(k : ℤ) := by omega
      have h3 : (f : ℤ) * u ≤ f * (-(k : ℤ)) := mul_le_mul_of_nonneg_left h2 hfpos.le
      have h4 : (k : ℤ) * e < k * f := mul_lt_mul_of_pos_left hefZ (by linarith)
      linarith
  have hz : (z : ℤ) = 2 * e - k * f - u * e := by
    have h2 : (f : ℤ) * (z : ℤ) = f * (2 * e - k * f - u * e) := by
      rw [hx] at h
      linear_combination h
    exact mul_left_cancel₀ hfpos.ne' h2
  have h4 : (1 - (k : ℤ)) * e ≤ u * e := mul_le_mul_of_nonneg_right hu1 hepos.le
  have h5 : (1 : ℤ) * ((f : ℤ) - e) ≤ k * ((f : ℤ) - e) := mul_le_mul_of_nonneg_right hkZ (by linarith)
  have : (z : ℤ) < e := by linarith
  exact_mod_cast this

/-- **at most one column for each `k ≥ 1`** -/
theorem one_per_k {e f k x z x' z' : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) (hk : 1 ≤ k)
    (h : (x : ℤ) * e + (z : ℤ) * f = 2 * (e : ℤ) * f - (k : ℤ) * ((f : ℤ) * f - (e : ℤ) * e))
    (h' : (x' : ℤ) * e + (z' : ℤ) * f = 2 * (e : ℤ) * f - (k : ℤ) * ((f : ℤ) * f - (e : ℤ) * e)) :
    x = x' ∧ z = z' := by
  have hz := z_lt_e hco he hef hk h
  have hz' := z_lt_e hco he hef hk h'
  have hcop : IsCoprime (f : ℤ) (e : ℤ) := (Nat.isCoprime_iff_coprime.mpr hco).symm
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hepos : (0 : ℤ) < e := by exact_mod_cast (by omega : 0 < e)
  have hd : (f : ℤ) ∣ ((x : ℤ) - x') * e := ⟨(z' : ℤ) - z, by linear_combination h - h'⟩
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right hd
  have hzz : (z' : ℤ) - z = t * e := by
    have h2 : (f : ℤ) * ((z' : ℤ) - z) = f * (t * e) := by
      linear_combination (-1 : ℤ) * (h - h') + (e : ℤ) * ht
    exact mul_left_cancel₀ hfpos.ne' h2
  have hzZ : (z : ℤ) < e := by exact_mod_cast hz
  have hzZ' : (z' : ℤ) < e := by exact_mod_cast hz'
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hz0' : (0 : ℤ) ≤ z' := by positivity
  have ht0 : t = 0 := by
    rcases lt_trichotomy t 0 with hneg | h0 | hpos
    · exfalso
      have h1 : t ≤ -1 := by omega
      have h2 : t * (e : ℤ) ≤ (-1) * e := mul_le_mul_of_nonneg_right h1 hepos.le
      linarith
    · exact h0
    · exfalso
      have h1 : 1 ≤ t := by omega
      have h2 : (1 : ℤ) * e ≤ t * e := mul_le_mul_of_nonneg_right h1 hepos.le
      linarith
  subst ht0
  constructor
  · have : (x : ℤ) = x' := by linarith
    exact_mod_cast this
  · have : (z : ℤ) = z' := by linarith
    exact_mod_cast this

/-! ## Close pairs are not a finite exception -/

theorem close_pairs_infinite :
    {p : ℕ × ℕ | 1 ≤ p.1 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      p.2 * p.2 ≤ 2 * p.1 * p.2 + p.1 * p.1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n + 1, n + 2)) ?_ ?_
  · intro m n h
    simp only [Prod.mk.injEq] at h
    omega
  · intro n
    show 1 ≤ n + 1 ∧ n + 1 < n + 2 ∧ Nat.Coprime (n + 1) (n + 2) ∧
      (n + 2) * (n + 2) ≤ 2 * (n + 1) * (n + 2) + (n + 1) * (n + 1)
    refine ⟨by omega, by omega, ?_, by nlinarith⟩
    have h1 := Nat.gcd_dvd_left (n + 1) (n + 2)
    have h2 : Nat.gcd (n + 1) (n + 2) ∣ n + 1 + 1 := Nat.gcd_dvd_right (n + 1) (n + 2)
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2)

/-- `(5, 6)` and `(4, 7)` are close pairs, with `N = 83` and `N = 131` -/
theorem close_83_131 :
    (6 * 6 ≤ 2 * 5 * 6 + 5 * 5 ∧ 3 * (6 * 6) - 5 * 5 = 83 ∧ Nat.Coprime 5 6) ∧
    (7 * 7 ≤ 2 * 4 * 7 + 4 * 4 ∧ 3 * (7 * 7) - 4 * 4 = 131 ∧ Nat.Coprime 4 7) := by decide

/-! ## The list of extra columns of a member -/

/-- the extra columns of the member `(e, f)`, by the reduced equation: `k + 1 ≤ 2ef/(f² − e²)`, `x ≤ 2f` -/
def colList (e f : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (2 * e * f / (f * f - e * e))).flatMap fun k =>
    (List.range (2 * f + 1)).filterMap fun x =>
      if (k + 1) * (f * f - e * e) + x * e ≤ 2 * e * f ∧
          f ∣ 2 * e * f - ((k + 1) * (f * f - e * e) + x * e) then
        some (x, e + (k + 1) * f, (2 * e * f - ((k + 1) * (f * f - e * e) + x * e)) / f)
      else none

/-- **`colList` is the set of extra columns.** -/
theorem mem_colList {e f x y z : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    (x, y, z) ∈ colList e f ↔ e < y ∧ IsCol e f x y z := by
  have h1 : e * e ≤ f * f := by nlinarith
  have hbb : e * e + f + e ≤ f * f := by nlinarith
  have hbpos : 0 < f * f - e * e := by omega
  have hf0 : 0 < f := by omega
  unfold colList
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨k, -, x', -, hite⟩
    split_ifs at hite with hc
    · obtain ⟨hle, q, hq⟩ := hc
      have hzq : (2 * e * f - ((k + 1) * (f * f - e * e) + x' * e)) / f = q := by
        rw [hq]
        exact Nat.mul_div_cancel_left q hf0
      rw [hzq] at hite
      simp only [Option.some.injEq, Prod.mk.injEq] at hite
      obtain ⟨rfl, rfl, rfl⟩ := hite
      refine ⟨?_, ?_⟩
      · have : 0 < (k + 1) * f := Nat.mul_pos (by omega) hf0
        omega
      · have hq' : f * q + ((k + 1) * (f * f - e * e) + x' * e) = 2 * e * f := by omega
        have hZ : (f : ℤ) * q + (((k : ℤ) + 1) * ((f : ℤ) * f - (e : ℤ) * e) + (x' : ℤ) * e)
            = 2 * (e : ℤ) * f := by
          have := congrArg (fun n : ℕ => (n : ℤ)) hq'
          push_cast [Nat.cast_sub h1] at this
          linarith
        apply col_of_reduced hef (k := k + 1)
        push_cast
        linear_combination hZ
  · rintro ⟨hy, hcol⟩
    obtain ⟨k, hk1, hyk, hred⟩ := col_reduce hco hef hy hcol
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hN : x * e + z * f + (j + 1) * (f * f - e * e) = 2 * e * f := by
      zify [h1]
      push_cast at hred
      linear_combination hred
    have hj : j < 2 * e * f / (f * f - e * e) := by
      have : j + 1 ≤ 2 * e * f / (f * f - e * e) :=
        (Nat.le_div_iff_mul_le hbpos).mpr (by omega)
      omega
    have hx : x < 2 * f + 1 := by
      have h9 : x * e ≤ 2 * f * e := by
        have : 2 * f * e = 2 * e * f := by ring
        omega
      have := Nat.le_of_mul_le_mul_right h9 (by omega : 0 < e)
      omega
    refine ⟨j, hj, x, hx, ?_⟩
    have c1 : (j + 1) * (f * f - e * e) + x * e ≤ 2 * e * f := by omega
    have c2' : 2 * e * f - ((j + 1) * (f * f - e * e) + x * e) = z * f := by omega
    have c2 : f ∣ 2 * e * f - ((j + 1) * (f * f - e * e) + x * e) := Dvd.intro_left z c2'.symm
    rw [if_pos ⟨c1, c2⟩, hyk, Nat.div_eq_of_eq_mul_left hf0 c2']

/-- the coprime members `1 ≤ e ≤ E`, `e < f ≤ F` -/
def pairs (E F : ℕ) : List (ℕ × ℕ) :=
  (List.range (E + 1)).flatMap fun e => (List.range (F + 1)).filterMap fun f =>
    if 1 ≤ e ∧ e < f ∧ Nat.Coprime e f then some (e, f) else none

theorem mem_pairs {E F e f : ℕ} :
    (e, f) ∈ pairs E F ↔ 1 ≤ e ∧ e ≤ E ∧ e < f ∧ f ≤ F ∧ Nat.Coprime e f := by
  unfold pairs
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨e', he', f', hf', hite⟩
    split_ifs at hite with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hite
      obtain ⟨rfl, rfl⟩ := hite
      exact ⟨hc.1, by omega, hc.2.1, by omega, hc.2.2⟩
  · rintro ⟨a1, a2, a3, a4, a5⟩
    exact ⟨e, by omega, f, by omega, by rw [if_pos ⟨a1, a3, a5⟩]⟩

/-- all extra columns `(e, f, x, y, z)` of the members in the range -/
def allCols (E F : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (pairs E F).flatMap fun p => (colList p.1 p.2).map fun c => (p.1, p.2, c.1, c.2.1, c.2.2)

/-- **`allCols E F` is the set of extra columns of the coprime members with `e ≤ E`, `f ≤ F`.** -/
theorem mem_allCols {E F e f x y z : ℕ} :
    (e, f, x, y, z) ∈ allCols E F ↔
      1 ≤ e ∧ e ≤ E ∧ e < f ∧ f ≤ F ∧ Nat.Coprime e f ∧ e < y ∧ IsCol e f x y z := by
  unfold allCols
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨e', f'⟩, hp, ⟨x', y', z'⟩, hc, heq⟩
    dsimp only at hc heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    obtain ⟨a1, a2, a3, a4, a5⟩ := mem_pairs.mp hp
    obtain ⟨b1, b2⟩ := (mem_colList a5 a1 a3).mp hc
    exact ⟨a1, a2, a3, a4, a5, b1, b2⟩
  · rintro ⟨a1, a2, a3, a4, a5, b1, b2⟩
    exact ⟨(e, f), mem_pairs.mpr ⟨a1, a2, a3, a4, a5⟩, (x, y, z), (mem_colList a5 a1 a3).mpr ⟨b1, b2⟩, rfl⟩

/-! ## `rem:closepairs`: the range `e ≤ 9`, `f ≤ 15` -/

/-- a column removed by the corner parallelogram: `z ≠ 0`, `x + z ≤ 3`, in a word of at least four edges -/
def cornerKilled (q : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (q.2.2.2.2 ≠ 0 ∧ q.2.2.1 + q.2.2.2.2 ≤ 3 ∧ 4 ≤ q.2.2.1 + q.2.2.2.1 + q.2.2.2.2)

/-- a column left by the two filters -/
def survives (q : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (q.2.2.2.2 ≠ 0) && !cornerKilled q

theorem allCols_nodup : (allCols 9 15).Nodup := by decide +kernel

theorem count_extra : (allCols 9 15).length = 71 := by decide +kernel

theorem count_gamma_trap : ((allCols 9 15).filter fun q => decide (q.2.2.2.2 = 0)).length = 9 := by
  decide +kernel

theorem count_cornerpara : ((allCols 9 15).filter cornerKilled).length = 8 := by decide +kernel

theorem count_survivors : ((allCols 9 15).filter survives).length = 54 := by decide +kernel

theorem first_survivor : ((allCols 9 15).filter survives).head? = some (3, 4, 3, 7, 2) := by decide +kernel

theorem survivors_x_lt_f : ∀ q ∈ (allCols 9 15).filter survives, q.2.2.1 < q.2.1 := by decide +kernel

/-! ## `rem:columnreduction`: the close pairs with `e ≤ 25`, `f ≤ 59` -/

/-- the coprime close pairs in the range -/
def closePairs (E F : ℕ) : List (ℕ × ℕ) :=
  (pairs E F).filter fun p => decide (p.2 * p.2 ≤ 2 * p.1 * p.2 + p.1 * p.1)

/-- the surviving columns of a member: `z ≥ 1` and `x + z ≥ 4` -/
def surv (e f : ℕ) : List (ℕ × ℕ × ℕ) :=
  (colList e f).filter fun c => decide (1 ≤ c.2.2 ∧ 4 ≤ c.1 + c.2.2)

theorem mem_surv {e f x y z : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    (x, y, z) ∈ surv e f ↔ (e < y ∧ IsCol e f x y z) ∧ 1 ≤ z ∧ 4 ≤ x + z := by
  unfold surv
  rw [List.mem_filter, mem_colList hco he hef]
  simp

/-- the `k` of a column `y = e + kf` -/
def kOf (e f : ℕ) (c : ℕ × ℕ × ℕ) : ℕ := (c.2.1 - e) / f

/-- the bound of `Frontier.k_bound_sharp` -/
def kmax (e f : ℕ) : ℕ := (2 * e * f - 3 * e - f) / (f * f - e * e)

/-- the surviving `k` of a member, in increasing order -/
def survK (e f : ℕ) : List ℕ := (surv e f).map (kOf e f)

/-- the members carrying survivors -/
def carriers : List (ℕ × ℕ) := (closePairs 25 59).filter fun p => decide (0 < (surv p.1 p.2).length)

theorem closePairs_count : (closePairs 25 59).length = 282 := by decide +kernel

theorem colList_nodup_range : ∀ p ∈ closePairs 25 59, (colList p.1 p.2).Nodup := by decide +kernel

theorem count_surviving : ((closePairs 25 59).map fun p => (surv p.1 p.2).length).sum = 655 := by
  decide +kernel

theorem count_carriers : carriers.length = 198 := by decide +kernel

/-- the surviving `k` of a member are `1, 2, …, n` -/
theorem survK_initial_segment :
    ∀ p ∈ carriers, survK p.1 p.2 = (List.range (surv p.1 p.2).length).map (· + 1) := by decide +kernel

/-- the bound is attained at 186 of the 198 members -/
theorem count_attained :
    (carriers.filter fun p => decide ((surv p.1 p.2).length = kmax p.1 p.2)).length = 186 := by
  decide +kernel

/-- no member exceeds the bound -/
theorem surviving_le_kmax : ∀ p ∈ carriers, (surv p.1 p.2).length ≤ kmax p.1 p.2 := by decide +kernel

/-- the columns of a member at `k = kmax` with `x, z ≥ 1` -/
def topCols (e f : ℕ) : List (ℕ × ℕ × ℕ) :=
  (colList e f).filter fun c => decide (kOf e f c = kmax e f ∧ 1 ≤ c.1 ∧ 1 ≤ c.2.2)

/-- the bound is not attained exactly when the reduced equation has no solution with `x, z ≥ 1` at `k = kmax` -/
theorem not_attained_iff :
    ∀ p ∈ carriers, ((surv p.1 p.2).length < kmax p.1 p.2 ↔ topCols p.1 p.2 = []) := by decide +kernel

theorem count_not_attained :
    (carriers.filter fun p => decide ((surv p.1 p.2).length < kmax p.1 p.2)).length = 12 := by
  decide +kernel

/-- the instance `(15, 23)`, `k = 2`: `2ef − kb − e − f = 44` is a gap of `⟨15, 23⟩` -/
theorem gap_15_23 : (15, 23) ∈ carriers ∧ kmax 15 23 = 2 ∧ (surv 15 23).length = 1 ∧
    2 * 15 * 23 - 2 * (23 * 23 - 15 * 15) - 15 - 23 = 44 ∧ ∀ u v : ℕ, 15 * u + 23 * v ≠ 44 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by norm_num, ?_⟩
  intro u v
  omega

end Erdos634.Draft.ClosePairsFull

#print axioms Erdos634.Draft.ClosePairsFull.mem_allCols
#print axioms Erdos634.Draft.ClosePairsFull.no_x_zero
#print axioms Erdos634.Draft.ClosePairsFull.one_per_k
#print axioms Erdos634.Draft.ClosePairsFull.k_one_iff
#print axioms Erdos634.Draft.ClosePairsFull.close_pairs_infinite
#print axioms Erdos634.Draft.ClosePairsFull.count_survivors
#print axioms Erdos634.Draft.ClosePairsFull.count_surviving
#print axioms Erdos634.Draft.ClosePairsFull.not_attained_iff
