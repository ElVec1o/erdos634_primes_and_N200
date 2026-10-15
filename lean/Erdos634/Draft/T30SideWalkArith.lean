import Mathlib.Tactic
import Erdos634.Draft.ChordWord

/-!
# T30 side-walk arithmetic: partition lemma for R1

Erdős #634, T30L stage 6 (R1 obligation support). directly; narrows R1 from "what OEdge words appear"
to "which arithmetic partitions are possible."

## Main result

`side_walk_count_T30`: for natural numbers na, nb, nc satisfying
  na * sa + nb * sb + nc * sc = 60
(where sa = 9+√21, sb = 9-√21, sc = 12 are the T30 tile's edge lengths),
the only non-negative integer solutions are:
  (na, nb, nc) = (0, 0, 5)   -- 5 edges all of type c
  (na, nb, nc) = (2, 2, 2)   -- 6 edges, 2 each of type a, b, c

The key steps are:
1. Separate rational and irrational parts: 9*(na+nb) + 12*nc = 60 and (na-nb)*√21 = 0
2. Irrationality of √21 → na = nb
3. omega: 18*na + 12*nc = 60 → (na=0 ∧ nc=5) ∨ (na=2 ∧ nc=2)

The (0,0,5) solution gives a 5-edge side word.  Pi3Enum.sides true 1 has 0 words with C2
(verified by kernel in T30LPi3Enum), so the (0,0,5) case is excluded by the fan+C2 rules —
this is the content of the full R1 obligation; the present lemma is the arithmetic half.
-/

namespace Erdos634.T30SideWalkArith

open Erdos634.ChordWord (sa sb sc)

/-- √21 is irrational (21 is not a perfect square). -/
theorem sqrt21_irrational : Irrational (Real.sqrt 21) := Erdos634.ChordWord.sqrt21_irrational

/-- √21 is positive. -/
theorem sqrt21_pos : (0 : ℝ) < Real.sqrt 21 :=
  Real.sqrt_pos.mpr (by norm_num)

/-- √21 is nonzero. -/
theorem sqrt21_ne_zero : Real.sqrt 21 ≠ 0 :=
  ne_of_gt sqrt21_pos

/-- The integer (n : ℤ) cast to ℝ is rational (and any rational multiple of √21 with
    nonzero coefficient is irrational). -/
theorem int_mul_sqrt21_eq_int_iff (k : ℤ) (n : ℤ) :
    (k : ℝ) * Real.sqrt 21 = (n : ℝ) → k = 0 := by
  intro h
  by_contra hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have : Real.sqrt 21 = (n : ℝ) / (k : ℝ) := by field_simp at h ⊢; linarith
  have hirr := sqrt21_irrational
  apply hirr
  rw [this]
  exact ⟨n / k, by push_cast; ring⟩

/-- Key arithmetic: the rational-irrational separation.
    If na*(9+√21) + nb*(9-√21) + nc*12 = 60, then na = nb. -/
theorem na_eq_nb_of_side_walk (na nb nc : ℕ)
    (h : (na : ℝ) * sa + (nb : ℝ) * sb + (nc : ℝ) * sc = 60) : na = nb := by
  unfold sa sb sc at h
  -- Rearrange to isolate the √21 coefficient
  have hrearr : ((na : ℝ) - (nb : ℝ)) * Real.sqrt 21 =
      60 - (9 * (na : ℝ) + 9 * (nb : ℝ) + 12 * (nc : ℝ)) := by linarith [h]
  -- The RHS is an integer (hence rational)
  have hrhs_int : ∃ (k : ℤ), (k : ℝ) = 60 - (9 * (na : ℝ) + 9 * (nb : ℝ) + 12 * (nc : ℝ)) := by
    exact ⟨60 - 9 * (na : ℤ) - 9 * (nb : ℤ) - 12 * (nc : ℤ), by push_cast; ring⟩
  obtain ⟨k, hk⟩ := hrhs_int
  rw [← hk] at hrearr
  -- Cast na - nb to ℤ
  have hcoeff : ((na : ℤ) - (nb : ℤ)) = 0 := by
    have : ((na : ℝ) - (nb : ℝ)) * Real.sqrt 21 = (k : ℝ) := hrearr
    have hc : ((na : ℝ) - (nb : ℝ)) = ((na : ℤ) - (nb : ℤ) : ℤ) := by push_cast; ring
    rw [hc] at this
    exact int_mul_sqrt21_eq_int_iff ((na : ℤ) - (nb : ℤ)) k this
  omega

/-- Rational part: if na = nb and na*(9+√21) + nb*(9-√21) + nc*12 = 60, then 3*na + 2*nc = 10. -/
theorem nat_eq_of_side_walk_rational (na nc : ℕ)
    (h : (na : ℝ) * sa + (na : ℝ) * sb + (nc : ℝ) * sc = 60) : 3 * na + 2 * nc = 10 := by
  unfold sa sb sc at h
  have h' : 18 * (na : ℝ) + 12 * (nc : ℝ) = 60 := by
    have : (na : ℝ) * (9 + Real.sqrt 21) + (na : ℝ) * (9 - Real.sqrt 21) = 18 * (na : ℝ) := by
      ring
    linarith [this]
  have h'' : 18 * (na : ℕ) + 12 * (nc : ℕ) = 60 := by exact_mod_cast h'
  omega

/-- Main result: the only non-negative integer solutions to na*sa + nb*sb + nc*sc = 60 are
    (0, 0, 5) and (2, 2, 2). -/
theorem side_walk_count_T30 (na nb nc : ℕ)
    (h : (na : ℝ) * sa + (nb : ℝ) * sb + (nc : ℝ) * sc = 60) :
    (na = 0 ∧ nb = 0 ∧ nc = 5) ∨ (na = 2 ∧ nb = 2 ∧ nc = 2) := by
  have hna_eq : na = nb := na_eq_nb_of_side_walk na nb nc h
  subst hna_eq
  have hrat : 3 * na + 2 * nc = 10 := by
    exact nat_eq_of_side_walk_rational na nc h
  -- omega gives the two solutions
  omega

#print axioms side_walk_count_T30

end Erdos634.T30SideWalkArith
