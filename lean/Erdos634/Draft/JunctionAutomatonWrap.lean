import Erdos634.JunctionAutomaton

namespace Erdos634.Draft.JunctionAutomatonWrap

open Erdos634.JunctionAutomaton Angle

theorem ja_only_forbidden_pair_is_gg :
    ∀ T B : Angle, ¬ admissible T B ↔ T = gamma ∧ B = gamma :=
  only_forbidden_pair_is_gg

theorem ja_gg_inadmissible : ¬ admissible gamma gamma :=
  gg_inadmissible

theorem ja_admissible_of_ne_gg {T B : Angle} (h : ¬ (T = gamma ∧ B = gamma)) : admissible T B :=
  admissible_of_ne_gg h

theorem ja_witness_alpha_beta : admissible alpha beta :=
  witness_alpha_beta

example : ja_gg_inadmissible = gg_inadmissible := rfl

#print axioms ja_only_forbidden_pair_is_gg
#print axioms ja_gg_inadmissible

end Erdos634.Draft.JunctionAutomatonWrap
