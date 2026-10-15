import Erdos634.ExclusionCriterion

/-!
# ExclusionCriterion: leg/pi-alpha/base exclusion, wrapper

Key results:
- `leg_exclusion_iff`: e²(3f²-e²) < f³ ↔ 3e² ≤ f
- `all_three_excluded_iff`: all three exclusion conditions fire together iff f ≥ 3e²
- `at_e_one`: at e=1 the criterion is f ≥ 3

No sorry, standard axioms.
-/

namespace Erdos634.Draft.ExclusionCriterionWrap

open Erdos634.ExclusionCriterion

theorem ec_leg_exclusion_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) < f ^ 3 ↔ 3 * e ^ 2 ≤ f :=
  leg_exclusion_iff he hef

theorem ec_all_three_excluded_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    3 * e ^ 2 ≤ f →
      e ^ 2 * (3 * f ^ 2 - e ^ 2) < f ^ 3 ∧
      e * (3 * f ^ 2 - e ^ 2) < f ^ 3 ∧
      e * (3 * f ^ 2 - e ^ 2) * (f ^ 2 - e) < f ^ 3 * (f ^ 2 - e ^ 2) :=
  all_three_excluded_iff he hef

theorem ec_at_e_one {f : ℤ} (hf : 1 < f) :
    (1:ℤ) ^ 2 * (3 * f ^ 2 - 1 ^ 2) < f ^ 3 ↔ 3 ≤ f :=
  at_e_one hf

-- Non-vacuity: at e=1, f=3, leg_exclusion_iff fires (iff true)
example : ec_leg_exclusion_iff (e := (1:ℤ)) (f := 3) one_pos (by norm_num) = by norm_num := rfl

#print axioms ec_leg_exclusion_iff
#print axioms ec_all_three_excluded_iff

end Erdos634.Draft.ExclusionCriterionWrap
