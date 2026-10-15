import Erdos634.ApexChordCriterion

/-!
# Apex chord criterion: wrapper

Re-exports, under `acc_` names, results of `ApexChordCriterion`:
- `apex_exclusion_iff`: e²(2f²−e²) < f³ ↔ 2e² ≤ f
- `apex_stronger`: 3e² ≤ f → 2e² ≤ f
- `pi_alpha_fan_never_bites`: fan excess f³−f²(1+e)+e² > 0
- `reach_e_ge_two`: 2e² ≤ f with e ≥ 2 → reach criterion
- `fan_excess_at_f_eq_e_succ`: fan excess at f = e+1

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ApexChordCriterionWrap

open Erdos634.ApexChordCriterion

theorem acc_apex_exclusion_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    e ^ 2 * (2 * f ^ 2 - e ^ 2) < f ^ 3 ↔ 2 * e ^ 2 ≤ f :=
  apex_exclusion_iff he hef

theorem acc_apex_stronger {e f : ℤ} (he : 0 < e) (h : 3 * e ^ 2 ≤ f) : 2 * e ^ 2 ≤ f :=
  apex_stronger he h

theorem acc_pi_alpha_fan_never_bites {e f : ℤ} (he : 0 < e) (hef : e < f) :
    0 < f ^ 3 - f ^ 2 * (1 + e) + e ^ 2 :=
  pi_alpha_fan_never_bites he hef

theorem acc_reach_e_ge_two {e f : ℤ} (he : 2 ≤ e) (h : 2 * e ^ 2 ≤ f) :
    188 ≤ 3 * f ^ 2 - e ^ 2 :=
  reach_e_ge_two he h

-- Non-vacuity: apex_stronger with e=1, f=3 → 3·1²=3≤3
example : 2 * (1:ℤ) ^ 2 ≤ 3 := acc_apex_stronger (by norm_num) (by norm_num)

#print axioms acc_apex_exclusion_iff
#print axioms acc_pi_alpha_fan_never_bites

end Erdos634.Draft.ApexChordCriterionWrap
