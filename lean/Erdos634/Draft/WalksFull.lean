/-
Draft/WalksFull.lean: the boundary walks of the base-`β` target at `m = 1`, all
clauses in one statement, with the converse of the parametrization.

Tile `(a, b, c) = (ef, B, f²)`, `B = f² − e²`, coprime `1 ≤ e < f`; base length `e (3f² − e²) = e (2f² + B)`, equal
sides `f³`.  A walk along a side is a triple `(P, Q, R)` of natural numbers with `P a + Q b + R c` equal to the
length of the side.

* parametrization (both directions): base walks are `(je + fp, e + fj, R)` with `pe + jf + R = 2e`; side walks are
  `(qe + fp, fq, R)` with `pe + qf + R = f` (`base_walk_conv`, `side_walk_conv` are the converses);
* (i), (ii) for `f > 2e` (`BaseBetaWalks.base_trichotomy`, `side_dichotomy`);
* (iii), (iv) under `R ≥ 1`, which the `γ`-trap supplies for a tiling (`side_no_b`, `base_b_bound`);
* the two consequences: `e = 1` gives `Q = 1` on the base; `f > 2e` gives `Q = e`.

No sorry, no native_decide.
-/
import Erdos634.BaseBetaWalks

namespace Erdos634.Draft.WalksFull

open Erdos634.BaseBetaWalks

/-- every parametrized triple is a base walk -/
theorem base_walk_conv (e f P Q R B j : ℕ) (p : ℤ) (hB : B + e ^ 2 = f ^ 2) (hQ : Q = e + f * j)
    (hP : (P : ℤ) = j * e + f * p) (hlev : p * e + j * f + R = 2 * e) :
    P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B) := by
  have hQz : (Q : ℤ) = e + f * j := by exact_mod_cast hQ
  have hBz : (B : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
  have h : ((P * (e * f) + Q * B + R * f ^ 2 : ℕ) : ℤ) = ((e * (2 * f ^ 2 + B) : ℕ) : ℤ) := by
    push_cast
    linear_combination ((e : ℤ) * f) * hP + (B : ℤ) * hQz + (f : ℤ) ^ 2 * hlev + ((f : ℤ) * j) * hBz
  exact_mod_cast h

/-- every parametrized triple is a side walk -/
theorem side_walk_conv (e f P Q R B q : ℕ) (p : ℤ) (hB : B + e ^ 2 = f ^ 2) (hQ : Q = f * q)
    (hP : (P : ℤ) = q * e + f * p) (hlev : p * e + q * f + R = f) :
    P * (e * f) + Q * B + R * f ^ 2 = f ^ 3 := by
  have hQz : (Q : ℤ) = f * q := by exact_mod_cast hQ
  have hBz : (B : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
  have h : ((P * (e * f) + Q * B + R * f ^ 2 : ℕ) : ℤ) = ((f ^ 3 : ℕ) : ℤ) := by
    push_cast
    linear_combination ((e : ℤ) * f) * hP + (B : ℤ) * hQz + (f : ℤ) ^ 2 * hlev + ((f : ℤ) * q) * hBz
  exact_mod_cast h

/-- **`thm:walks`.** -/
theorem thm_walks (e f B : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2) :
    -- the base walks are exactly the parametrized triples at level `2e`
    (∀ P Q R : ℕ, P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B) ↔
      ∃ j : ℕ, ∃ p : ℤ, Q = e + f * j ∧ (P : ℤ) = j * e + f * p ∧ p * e + j * f + R = 2 * e) ∧
    -- the side walks are exactly the parametrized triples at level `f`
    (∀ P Q R : ℕ, P * (e * f) + Q * B + R * f ^ 2 = f ^ 3 ↔
      ∃ q : ℕ, ∃ p : ℤ, Q = f * q ∧ (P : ℤ) = q * e + f * p ∧ p * e + q * f + R = f) ∧
    -- (i) trichotomy, thin regime
    (2 * e < f → ∀ P Q R : ℕ, P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B) →
      (P = 0 ∧ Q = e ∧ R = 2 * e) ∨ (P = f ∧ Q = e ∧ R = e) ∨ (P = 2 * f ∧ Q = e ∧ R = 0)) ∧
    -- (ii) dichotomy, thin regime
    (2 * e < f → ∀ P Q R : ℕ, P * (e * f) + Q * B + R * f ^ 2 = f ^ 3 →
      (P = e ∧ Q = f ∧ R = 0) ∨ ∃ u : ℕ, Q = 0 ∧ P = f * u ∧ u * e + R = f) ∧
    -- (iii) with a `c`-edge on the side: no `b`-edge
    (∀ P Q R : ℕ, 1 ≤ R → P * (e * f) + Q * B + R * f ^ 2 = f ^ 3 →
      Q = 0 ∧ ∃ u : ℕ, P = f * u ∧ u * e + R = f) ∧
    -- (iv) with a `c`-edge on the base: `j (f − e) ≤ e − 1`
    (∀ P Q R j : ℕ, 1 ≤ R → Q = e + f * j → P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B) →
      j * (f - e) ≤ e - 1) ∧
    -- consequences: one `b`-edge on the base at `e = 1`; `e` of them in the thin regime
    (e = 1 → ∀ P Q R : ℕ, 1 ≤ R → P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B) → Q = 1) ∧
    (2 * e < f → ∀ P Q R : ℕ, 1 ≤ R → P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B) → Q = e) := by
  have hbound : ∀ P Q R j : ℕ, 1 ≤ R → Q = e + f * j →
      P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B) → j * (f - e) ≤ e - 1 := by
    intro P Q R j hR hQ h
    have h1 := base_b_bound e f P Q R B j he hef hcop hB hR hQ h
    have h2 : j * (f - e) + j * e = j * f := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hef.le]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, hbound, ?_, ?_⟩
  · intro P Q R
    constructor
    · intro h
      obtain ⟨j, p, hQ, hP, hlev, -⟩ := base_walk_param e f P Q R B he hef hcop hB h
      exact ⟨j, p, hQ, hP, hlev⟩
    · rintro ⟨j, p, hQ, hP, hlev⟩
      exact base_walk_conv e f P Q R B j p hB hQ hP hlev
  · intro P Q R
    constructor
    · intro h
      obtain ⟨q, p, hQ, hP, hlev, -⟩ := side_walk_param e f P Q R B he hef hcop hB h
      exact ⟨q, p, hQ, hP, hlev⟩
    · rintro ⟨q, p, hQ, hP, hlev⟩
      exact side_walk_conv e f P Q R B q p hB hQ hP hlev
  · intro h2e P Q R h
    exact base_trichotomy e f P Q R B he h2e hcop hB h
  · intro h2e P Q R h
    exact side_dichotomy e f P Q R B he h2e hcop hB h
  · intro P Q R hR h
    exact side_no_b e f P Q R B he hef hcop hB hR h
  · intro he1 P Q R hR h
    obtain ⟨j, p, hQ, -, -, -⟩ := base_walk_param e f P Q R B he hef hcop hB h
    have hb := hbound P Q R j hR hQ h
    have hj : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · exact h0
      · have : 1 * (f - e) ≤ j * (f - e) := Nat.mul_le_mul_right _ h0
        omega
    rw [hQ, hj, he1]
    omega
  · intro h2e P Q R hR h
    obtain ⟨j, p, hQ, -, -, -⟩ := base_walk_param e f P Q R B he hef hcop hB h
    have hb := hbound P Q R j hR hQ h
    have hj : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · exact h0
      · have : 1 * (f - e) ≤ j * (f - e) := Nat.mul_le_mul_right _ h0
        omega
    rw [hQ, hj]
    omega

end Erdos634.Draft.WalksFull

#print axioms Erdos634.Draft.WalksFull.thm_walks
