import Erdos634.CornerRule

/-!
# CornerRule: corner vertex figure and wall forces, wrapper

Key results:
- `corner_figure`: base corner angle equation has unique solution (one β tile)
- `apex_figure`: apex angle equation has unique solution (three α tiles)
- `corner_tally`: corner rule as count
- `both_sides_begin_c` + `walls_forces_a_ends`: consequences of the wall hypothesis
- `e_one_words`: the three e=1 base words satisfy the base equation

No sorry, standard axioms (propext, Classical.choice, Quot.sound).
-/

namespace Erdos634.Draft.CornerRuleWrap

open Erdos634.CornerRule

theorem cr_corner_figure (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := corner_figure x y z h1 h2

theorem cr_apex_figure (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 0) :
    x = 3 ∧ y = 0 ∧ z = 0 := apex_figure x y z h1 h2

theorem cr_corner_tally (baseC sideC : ℕ) (hcorners : baseC + sideC = 2) :
    baseC = 2 - sideC ∧ sideC = 2 - baseC := corner_tally baseC sideC hcorners

theorem cr_walls_forces_a_ends (P baseC sideC : ℕ) (hcorners : baseC + sideC = 2)
    (hsides : sideC = 2) (hP : baseC = 0 → 1 ≤ P) : 1 ≤ P :=
  walls_forces_a_ends P baseC sideC hcorners hsides hP

theorem cr_e_one_words (f : ℤ) :
    (0 * f + 1 * (f ^ 2 - 1) + 2 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (2 * f * f + 1 * (f ^ 2 - 1) + 0 * f ^ 2 = 3 * f ^ 2 - 1) := e_one_words f

-- Non-vacuity: corner_figure at x=0, y=1, z=0
example : cr_corner_figure 0 1 0 (by norm_num) (by norm_num) = ⟨rfl, rfl, rfl⟩ := rfl

#print axioms cr_corner_figure
#print axioms cr_walls_forces_a_ends

end Erdos634.Draft.CornerRuleWrap
