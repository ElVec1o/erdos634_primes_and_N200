-- The arithmetic of the monochain and close-pair facts.
-- Monochain: a c-chord blocked at both ends has far-side word `(0,0,1)` at every member with
-- `e ≥ 2` and additionally `(f,0,0)` exactly at `e = 1` (`c_decompositions`, an iff).
-- Close pairs: for coprime `1 ≤ e < f` the base equation
-- `x·ef + y(f²−e²) + z f² = e(3f²−e²)` has a solution with `y > e` iff `f ≤ 2e` (`extra_column_iff`);
-- hence the close pairs `2e < f ≤ (1+√2)e` admit none (`close_pair_counts`: 82 of the 282 coprime
-- close pairs with `e ≤ 25`).
-- Checked by computation for 4651 members, with no exception.
import Erdos634.CChord
import Erdos634.Frontier

namespace Erdos634.Draft.RemClosePairFormal

/-- **`rem:monochain`, arithmetic.**  The decompositions of `c = f²` into tile edges
`x·ef + y(f²−e²) + z f²`: a single `c`, or (exactly at `e = 1`) `f` `a`-edges. -/
theorem c_decompositions {e f x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    x * (e * f) + y * (f * f - e * e) + z * (f * f) = f * f ↔
      ((x = 0 ∧ y = 0 ∧ z = 1) ∨ (e = 1 ∧ x = f ∧ y = 0 ∧ z = 0)) := by
  constructor
  · intro h
    have hb : (f * f - e * e) + e * e = f * f := Nat.sub_add_cancel (by nlinarith)
    exact Erdos634.CChord.c_chord_dichotomy hco he hef (a := e * f) (b := f * f - e * e)
      (c := f * f) rfl hb rfl h
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · ring
    · ring

/-- At every member with `e ≥ 2` the far side is a single `c`. -/
theorem c_decomposition_unique {e f x y z : ℕ} (he : 2 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    x * (e * f) + y * (f * f - e * e) + z * (f * f) = f * f ↔ (x = 0 ∧ y = 0 ∧ z = 1) := by
  rw [c_decompositions (by omega) hef hco]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · omega
  · exact Or.inl

/-- **`rem:closepairbase`, the existence criterion.**  A decomposition of the base equation with
`y > e` exists iff `f ≤ 2e`. -/
theorem extra_column_iff {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    (∃ x y z : ℕ, e < y ∧
        x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e))
      ↔ f ≤ 2 * e := by
  constructor
  · rintro ⟨x, y, z, hy, h⟩
    by_contra hf
    have hf2 : 2 * e < f := by omega
    rcases Erdos634.CChord.base_trichotomy_2e_nat he hf2 hco h with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ |
      ⟨-, h2, -⟩ <;> omega
  · intro h2e
    have h1 : e * e ≤ f * f := by nlinarith
    have h3 : e * e ≤ 3 * (f * f) := by nlinarith
    refine ⟨e, e + f, 2 * e - f, by omega, ?_⟩
    zify [h1, h3, h2e]
    ring

/-- `z = 2e − f` vanishes only at `(e,f) = (1,2)` among coprime members. -/
theorem extra_column_z_zero {e f : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (hz : 2 * e - f = 0) (h2e : f ≤ 2 * e) : e = 1 ∧ f = 2 := by
  have hf : f = 2 * e := by omega
  subst hf
  have : e ∣ Nat.gcd e (2 * e) := Nat.dvd_gcd (dvd_refl e) (dvd_mul_left e 2)
  rw [hco] at this
  have : e = 1 := Nat.dvd_one.mp this
  exact ⟨this, by omega⟩

/-- Every base-equation solution has `y ≡ e (mod f)` (ℕ form of `Frontier.base_column_y_form`). -/
theorem y_form_nat {e f x y z : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)) :
    (f : ℤ) ∣ (y : ℤ) - e := by
  have h1 : e * e ≤ f * f := by nlinarith
  have h3 : e * e ≤ 3 * (f * f) := by nlinarith
  have hcast : (x : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) * f - (e : ℤ) * e) +
      (z : ℤ) * ((f : ℤ) * f) = (e : ℤ) * (3 * ((f : ℤ) * f) - (e : ℤ) * e) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h3] at this
    linarith [this]
  have hcop : IsCoprime (f : ℤ) ((e : ℤ) * e) := by
    have : IsCoprime (f : ℤ) (e : ℤ) := (Nat.isCoprime_iff_coprime.mpr hco).symm
    exact this.mul_right this
  exact Erdos634.Frontier.base_column_y_form e f x y z hcop hcast

/-- **`rem:closepairbase`, as one statement**, for coprime `1 ≤ e < f`: the solution set is finite,
every solution has `y ≡ e (mod f)`, and an extra column (`y > e`) exists iff `f ≤ 2e`. -/
theorem rem_closepairbase {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    {p : ℕ × ℕ × ℕ | p.1 * (e * f) + p.2.1 * (f * f - e * e) + p.2.2 * (f * f)
        = e * (3 * (f * f) - e * e)}.Finite ∧
    (∀ x y z : ℕ, x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e) →
        (f : ℤ) ∣ (y : ℤ) - e) ∧
    ((∃ x y z : ℕ, e < y ∧
        x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e))
      ↔ f ≤ 2 * e) :=
  ⟨Erdos634.Frontier.base_solutions_finite (by omega) hef,
   fun _ _ _ h => y_form_nat hco hef h, extra_column_iff hco he hef⟩

/-- The counts of the remark: among the coprime close pairs `f² ≤ 2ef + e²` with `e ≤ 25`
there are `282`, and `82` of them have `f > 2e` (so admit no extra column). -/
theorem close_pair_counts :
    ((Finset.range 26 ×ˢ Finset.range 60).filter fun p : ℕ × ℕ =>
        1 ≤ p.1 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          p.2 * p.2 ≤ 2 * p.1 * p.2 + p.1 * p.1).card = 282 ∧
    ((Finset.range 26 ×ˢ Finset.range 60).filter fun p : ℕ × ℕ =>
        1 ≤ p.1 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          p.2 * p.2 ≤ 2 * p.1 * p.2 + p.1 * p.1 ∧ 2 * p.1 < p.2).card = 82 := by
  constructor <;> decide +kernel

/-- Controls: `(3,7)` is the first close pair without an extra column (`7 > 6`), `(3,4)` carries
`(3,7,2)`, `(1,2)` carries `(1,3,0)`. -/
theorem controls :
    ¬ (7 ≤ 2 * 3) ∧ (3 * (3 * 4) + 7 * (4 * 4 - 3 * 3) + 2 * (4 * 4)
        = 3 * (3 * (4 * 4) - 3 * 3) ∧ 3 < 7) ∧
      (1 * (1 * 2) + 3 * (2 * 2 - 1 * 1) + 0 * (2 * 2) = 1 * (3 * (2 * 2) - 1 * 1) ∧ 1 < 3) := by
  refine ⟨by omega, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end Erdos634.Draft.RemClosePairFormal

#print axioms Erdos634.Draft.RemClosePairFormal.c_decompositions
#print axioms Erdos634.Draft.RemClosePairFormal.c_decomposition_unique
#print axioms Erdos634.Draft.RemClosePairFormal.extra_column_iff
#print axioms Erdos634.Draft.RemClosePairFormal.extra_column_z_zero
#print axioms Erdos634.Draft.RemClosePairFormal.y_form_nat
#print axioms Erdos634.Draft.RemClosePairFormal.rem_closepairbase
#print axioms Erdos634.Draft.RemClosePairFormal.close_pair_counts
#print axioms Erdos634.Draft.RemClosePairFormal.controls
