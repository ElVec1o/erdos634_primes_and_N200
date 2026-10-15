import Erdos634.Route1

/-!
# Route 1 word count: wrapper

Key results:
- `run_le`: w.i ≤ f−2 for any Route 1 word
- `starved_west`: w.i < f (starvation)
- `exists_word`: Route 1 words exist for f ≥ 4
- `three_is_rigid`: at f=3, the unique word is (1,1,1)

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.Route1Wrap

open Erdos634.Route1

theorem r1_run_le (f : ℕ) (w : Word f) : w.i ≤ f - 2 :=
  run_le f w

theorem r1_starved_west (f : ℕ) (hf : 3 ≤ f) (w : Word f) : w.i < f :=
  starved_west f hf w

theorem r1_exists_word (f : ℕ) (hf : 4 ≤ f) : Nonempty (Word f) :=
  exists_word f hf

theorem r1_three_is_rigid (w : Word 3) : w.i = 1 ∧ w.j = 1 ∧ w.k = 1 :=
  three_is_rigid w

-- Non-vacuity: word at f=4 exists
example : Nonempty (Word 4) := r1_exists_word 4 (by norm_num)

#print axioms r1_three_is_rigid
#print axioms r1_exists_word

end Erdos634.Draft.Route1Wrap
