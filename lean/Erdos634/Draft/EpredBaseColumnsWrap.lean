import Erdos634.EpredBaseColumns
/-! # EpredBaseColumns: base-column solutions for the e=f−1 regime, wrapper

Key results:
- `epred_first_is_solution`: (0, f−1, 2f−2) satisfies BaseEq
- `epred_last_is_solution`: (2f, f−1, 0) satisfies BaseEq
- `epred_base_solutions`: complete characterisation of BaseEq solutions for f ≥ 3
- `epred_k_injective`: the parameterisation by k is injective
- `epred_after_gamma_trap`: the γ-trap condition holds after the last base column
- `witness_83_solutions`: explicit witness for N=83
- `witness_83_extra_column_survives`: the extra column survives at N=83

No sorry, standard axioms.
-/
namespace Erdos634.Draft.EpredBaseColumnsWrap

open Erdos634.EpredBaseColumns

theorem wrap_epred_first_is_solution (f : ℤ) : BaseEq f 0 (f - 1) (2 * f - 2) :=
  epred_first_is_solution f

theorem wrap_epred_last_is_solution (f : ℤ) : BaseEq f (2 * f) (f - 1) 0 :=
  epred_last_is_solution f

theorem wrap_epred_k_injective {f k k' : ℤ} (hf : 3 ≤ f)
    (heq : (k + 1) * f - 1 = (k' + 1) * f - 1) : k = k' :=
  epred_k_injective hf heq

-- Non-vacuity: ground instance at f = 3.
example : BaseEq 3 0 2 4 := epred_first_is_solution 3

#print axioms wrap_epred_first_is_solution

end Erdos634.Draft.EpredBaseColumnsWrap
