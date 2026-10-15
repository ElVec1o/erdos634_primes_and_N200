import Erdos634.BaseWord

/-!
# Base walk word arithmetic: wrapper

Re-exports results of `BaseWord`:
- `base_param`: the walk equation forces a parameter identity
- `b_count_is_e`: if 2e ≤ f, then j = 0 (pinned b-count)
- `eightythree_words`: five base words for N=83 satisfy the length equation

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseWordWrap

open Erdos634.BaseWord

theorem bw_b_count_is_e (e f j : ℤ) (he : 1 ≤ e) (hef : e < f) (hj : 0 ≤ j)
    (hiv : j * (f - e) ≤ e - 1) (hbig : 2 * e ≤ f) : j = 0 :=
  b_count_is_e e f j he hef hj hiv hbig

theorem bw_eightythree : (83 : ℤ) = 3 * 6 ^ 2 - 5 ^ 2 ∧ (6 : ℤ) < 2 * 5 :=
  eightythree

theorem bw_eightythree_words :
    (0 * 30 + 5 * 11 + 10 * 36 : ℤ) = 415 ∧ (6 * 30 + 5 * 11 + 5 * 36 : ℤ) = 415
    ∧ (5 * 30 + 11 * 11 + 4 * 36 : ℤ) = 415 ∧ (4 * 30 + 17 * 11 + 3 * 36 : ℤ) = 415
    ∧ (3 * 30 + 23 * 11 + 2 * 36 : ℤ) = 415 :=
  eightythree_words

theorem bw_param_word (e f j t : ℤ) :
    (j * e + f * t) * (e * f) + (e + f * j) * (f ^ 2 - e ^ 2) +
      (2 * e - t * e - j * f) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) :=
  param_word e f j t

#print axioms bw_b_count_is_e
#print axioms bw_eightythree_words
#print axioms bw_param_word

end Erdos634.Draft.BaseWordWrap
