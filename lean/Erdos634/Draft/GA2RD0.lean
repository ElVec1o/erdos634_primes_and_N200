/-
GA2R-D0: the table at denominator n = 60/c (c = 1: n = 60; c = 2: n = 30) satisfies (T).
-/
import Mathlib
import Erdos634.Draft.GA2RC
import Erdos634.Draft.GA2RA

namespace Erdos634.GA2R

/-- table at denominator `n = 60 / c` -/
def slc (c u : ℕ) : ℕ := SL60.getD (c * u) 0
def shc (c u : ℕ) : ℕ := SH60.getD (c * u) 0

theorem tab_c (c n : ℕ) (hc : c * n = 60) : Tab n (slc c) (shc c) := by
  intro u hu
  have hn : (n : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hc
    · exact_mod_cast h.ne'
  have h := sin_tab60 (c * u) (by nlinarith)
  have e : ((c * u : ℕ) : ℝ) * Real.pi / 60 = u * Real.pi / n := by
    have : (60 : ℝ) = c * n := by exact_mod_cast hc.symm
    have hc0 : (c : ℝ) ≠ 0 := by
      rintro h0; rw [h0] at this; norm_num at this
    rw [this]; push_cast; field_simp
  rw [e] at h
  exact h

#print axioms tab_c

end Erdos634.GA2R
