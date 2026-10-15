import Erdos634.MarchRecurrence
namespace Erdos634.Draft.MarchRecurrenceWrap
open Erdos634.MarchRecurrence

theorem wrap_shift_to_fibonacci (a : ℕ → ℤ)
    (h : ∀ n, a (n + 2) = a (n + 1) + a n + 2) :
    ∀ n, (a (n + 2) + 2) = (a (n + 1) + 2) + (a n + 2) :=
  shift_to_fibonacci a h

theorem wrap_fibonacci_to_shift (b : ℕ → ℤ)
    (h : ∀ n, b (n + 2) = b (n + 1) + b n) :
    ∀ n, (b (n + 2) - 2) = (b (n + 1) - 2) + (b n - 2) + 2 :=
  fibonacci_to_shift b h

theorem wrap_march_counts (a : ℕ → ℤ) (n : ℕ)
    (hstep : a (n + 2) = (a (n + 1) + a n) + 2) :
    a (n + 2) - a (n + 1) - a n = 2 :=
  march_counts a n hstep

theorem wrap_golden_ratio_growth : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 :=
  golden_ratio_growth

theorem wrap_seeds_check : (299 : ℤ) + 506 + 2 = 807 ∧ (506 : ℤ) + 807 + 2 = 1315 :=
  seeds_check

theorem wrap_flush_displacement (b c : ℤ) : (b - b) = 0 ∧ (c - c) = 0 :=
  flush_displacement b c

theorem wrap_offset_displacement (f : ℕ) (hf : 1 ≤ f) :
    (f * f) - (f * f - 1) = 1 :=
  offset_displacement f hf

theorem wrap_junction_forces_single_alpha (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 0) :
    x = 1 ∧ y = 0 ∧ z = 0 :=
  junction_forces_single_alpha x y z h1 h2

theorem wrap_second_family_shift (a : ℕ → ℤ) (n : ℕ)
    (h : a (n + 2) = 3 * a (n + 1) - a n - 31) :
    (a (n + 2) - 31) = 3 * (a (n + 1) - 31) - (a n - 31) :=
  second_family_shift a n h

theorem wrap_second_family_base : (3 : ℤ) * 235 - 109 - 31 = 565 :=
  second_family_base

theorem wrap_first_family_base : (205 : ℤ) + 92 + 2 = 299 :=
  first_family_base

example : True := trivial
#print axioms wrap_shift_to_fibonacci
#print axioms wrap_golden_ratio_growth
end Erdos634.Draft.MarchRecurrenceWrap
