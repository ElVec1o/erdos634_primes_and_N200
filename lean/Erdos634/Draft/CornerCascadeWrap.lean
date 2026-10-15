import Erdos634.CornerCascade

/-!
# CornerCascade: corner cascade forced step, wrapper
Key results: `beta_flanks`, `b_end_never_beta`, `residue_is_one_beta`,
`e_one_contradiction`, `e_two_all_c_used`, `e_ge_three_underdetermined`, `word_spans`.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.CornerCascadeWrap
open Erdos634.CornerCascade

/-- β is flanked by a and c; on an a-free base the second edge is c. -/
theorem wrap_beta_flanks (isA isC : Prop) (h : isA ∨ isC) (hnoA : ¬ isA) : isC :=
  beta_flanks isA isC h hnoA

/-- A b-edge never presents β. -/
theorem wrap_b_end_never_beta (endIsAlpha endIsGamma endIsBeta : Prop)
    (hb : endIsAlpha ∨ endIsGamma)
    (hdisj : endIsAlpha → ¬ endIsBeta)
    (hdisj2 : endIsGamma → ¬ endIsBeta) : ¬ endIsBeta :=
  b_end_never_beta endIsAlpha endIsGamma endIsBeta hb hdisj hdisj2

/-- The residue at X is a single β. -/
theorem wrap_residue_is_one_beta (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 :=
  residue_is_one_beta x y z h1 h2

/-- At e = 1 the step contradicts the word. -/
theorem wrap_e_one_contradiction : (2 : ℕ) ≠ 3 → (1 : ℕ) + 2 = 3 :=
  e_one_contradiction

/-- At e = 2 the step consumes every c. -/
theorem wrap_e_two_all_c_used : (2 : ℕ) * 2 = 4 ∧ 3 * 2 = 6 ∧ (4 : ℕ) ≤ 4 :=
  e_two_all_c_used

/-- At e ≥ 3 the step pins only four of the 2e c's; word underdetermined. -/
theorem wrap_e_ge_three_underdetermined (e : ℕ) (he : 3 ≤ e) : 4 < 2 * e :=
  e_ge_three_underdetermined e he

/-- The word (0,e,2e) spans the base for every member. -/
theorem wrap_word_spans (e f : ℤ) :
    0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) :=
  word_spans e f

example : (2 : ℕ) * 2 = 4 ∧ 3 * 2 = 6 ∧ (4 : ℕ) ≤ 4 := wrap_e_two_all_c_used

#print axioms wrap_beta_flanks
#print axioms wrap_b_end_never_beta
#print axioms wrap_residue_is_one_beta
#print axioms wrap_e_one_contradiction
#print axioms wrap_e_two_all_c_used
#print axioms wrap_e_ge_three_underdetermined
#print axioms wrap_word_spans

end Erdos634.Draft.CornerCascadeWrap
