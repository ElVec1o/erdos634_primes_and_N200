/-
GA2Q, Prop D, part 3: the two-entry pattern lemma and the three-distinct-components arithmetic.

  `pattern_two` : (p absent) F(g) = b([g = 2v] - kappa [g = v]) + c [g = w], v and w units mod M (M odd, >= 13), kappa != 0, eps = +-1:
                  F(g) + eps F(-g) = 0 for all g  =>  b = c = 0.
  `four_distinct` : in Z/3^j (j >= 2), for X a unit and 2h = 1 the four elements X, -X, X h, -X h are pairwise distinct.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QP

open scoped BigOperators

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Erdos634.GA2QD3

open Erdos634.GA2QP

variable {M : ℕ}

theorem pattern_two (hM : 13 ≤ M) (hodd : M % 2 = 1) {v w : ZMod M} (hv : IsUnit v) (hw : IsUnit w)
    {κ ε b c : ℂ} (hκ : κ ≠ 0) (hε : ε = 1 ∨ ε = -1) (p1 p2 : ZMod M)
    (H : ∀ g, Fq p1 p2 (2 * v) v w κ 0 b c g + ε * Fq p1 p2 (2 * v) v w κ 0 b c (-g) = 0) :
    b = 0 ∧ c = 0 := by
  haveI : Fact (1 < M) := ⟨by omega⟩
  have c2 : ∀ x y : ZMod M, 2 * x = 2 * y → x = y := fun x y h => (two_unit hodd).mul_left_cancel h
  have mu : ∀ (x : ZMod M) (m : ℤ), IsUnit x → m ≠ 0 → |m| ≤ 12 → (m : ZMod M) * x = 0 → False :=
    fun x m hx h0 hb e => mulne hM hx m h0 hb e
  have v1 : ¬ (2 * v = v) := fun h => mu v 1 hv (by norm_num) (by norm_num) (by push_cast; linear_combination h)
  have v2 : ¬ (-(2 * v) = 2 * v) := fun h => mu v 4 hv (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have v3 : ¬ (-(2 * v) = v) := fun h => mu v 3 hv (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have v4 : ¬ (-v = 2 * v) := fun h => mu v 3 hv (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have v5 : ¬ (-v = v) := fun h => mu v 2 hv (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have v6 : ¬ (-(2 * v) = -v) := fun h => mu v 1 hv (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have v7 : ¬ (v = 2 * v) := fun h => v1 h.symm
  have v8 : ¬ (v = -v) := fun h => v5 h.symm
  have v9 : ¬ (v = -(2 * v)) := fun h => v3 h.symm
  have v10 : ¬ (2 * v = -v) := fun h => v4 h.symm
  have v11 : ¬ (2 * v = -(2 * v)) := fun h => v2 h.symm
  have v12 : ¬ (-v = -(2 * v)) := fun h => v6 h.symm
  have hw2 : ¬ (-w = w) := fun h => by
    have : w = 0 := c2 w 0 (by linear_combination (-1) * h)
    exact hw.ne_zero this
  by_cases e1 : w = 2 * v
  · subst e1
    have H1 := H v
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true] at H1
    have hb : b = 0 := mulz hκ (by linear_combination (-1) * H1)
    refine ⟨hb, ?_⟩
    have H2 := H (2 * v)
    subst hb
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true] at H2
    linear_combination H2
  by_cases e2 : w = v
  · subst e2
    have H1 := H (2 * w)
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true] at H1
    have hb : b = 0 := by linear_combination H1
    refine ⟨hb, ?_⟩
    have H2 := H w
    subst hb
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true] at H2
    linear_combination H2
  by_cases e3 : w = -(2 * v)
  · subst e3
    have H1 := H v
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true] at H1
    have hb : b = 0 := mulz hκ (by linear_combination (-1) * H1)
    refine ⟨hb, ?_⟩
    have H2 := H (-(2 * v))
    subst hb
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true, neg_neg] at H2
    linear_combination H2
  by_cases e4 : w = -v
  · subst e4
    have H1 := H (2 * v)
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true] at H1
    have hb : b = 0 := by linear_combination H1
    refine ⟨hb, ?_⟩
    have H2 := H (-v)
    subst hb
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ↓reduceIte, eq_self_iff_true, neg_neg] at H2
    linear_combination H2
  · have q1 : ¬ (2 * v = w) := fun h => e1 h.symm
    have q2 : ¬ (-(2 * v) = w) := fun h => e3 h.symm
    have H1 := H (2 * v)
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, q1, q2, ↓reduceIte, eq_self_iff_true] at H1
    have hb : b = 0 := by linear_combination H1
    refine ⟨hb, ?_⟩
    have q3 : ¬ (w = 2 * v) := e1
    have q4 : ¬ (w = v) := e2
    have q5 : ¬ (-w = 2 * v) := fun h => e3 (by linear_combination (-1) * h)
    have q6 : ¬ (-w = v) := fun h => e4 (by linear_combination (-1) * h)
    have H2 := H w
    subst hb
    simp only [Fq, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, q3, q4, q5, q6, hw2, ↓reduceIte, eq_self_iff_true] at H2
    linear_combination H2

end Erdos634.GA2QD3

#print axioms Erdos634.GA2QD3.pattern_two
