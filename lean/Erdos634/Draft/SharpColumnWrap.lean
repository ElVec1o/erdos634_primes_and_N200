import Erdos634.Frontier

/-!
# Sharp criterion for an extra base column: arithmetic kernel

At a close-pair member, the extra base columns are characterised
by a sharp arithmetic criterion. The column `(x, y, z)` (with `y = e + kf`) has `z ≥ 1` exactly
when `kf ≤ (m+2)e − 1`, where `x = ke − mf` is the least positive representative of `ke mod f`.
At `k = 1` this forces `f ≤ 2e − 1`. The residue index `m` moves by 0 or 1 per step in `k`.

All four arithmetic facts are proved in `Frontier.lean`:

1. **`column_criterion_identity`**: the ring identity `(ke−mf)e + f + k(f²−e²) − 2ef = f(kf−(m+2)e+1)`.
2. **`column_criterion`**: given `x = ke−mf`, `z ≥ 1`, `x·e + z·f = 2ef − k(f²−e²)` implies `kf ≤ (m+2)e−1`.
3. **`k_one_forces_f_le_two_e_sub_one`**: at k=1, `z ≥ 1` forces `f ≤ 2e−1`.
4. **`residue_step`**: the residue index `m` satisfies `m ≤ m' ≤ m+1` in successive steps.

That an extra base column exists in a real base-β tiling is a placement statement and is not part of this module.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.SharpColumnWrap

open Erdos634.Frontier

/-- The column criterion identity: (ke−mf)e + f + k(f²−e²) − 2ef = f·(kf−(m+2)e+1). -/
theorem sharp_col_identity (e f k m : ℤ) :
    (k * e - m * f) * e + f + k * (f * f - e * e) - 2 * e * f
      = f * (k * f - (m + 2) * e + 1) :=
  column_criterion_identity e f k m

/-- The sharp criterion: x=ke−mf, z≥1, x·e+z·f=2ef−k(f²−e²) ⟹ kf ≤ (m+2)e−1. -/
theorem sharp_col_criterion {e f k m x z : ℤ} (hf : 0 < f) (hz : 1 ≤ z)
    (hx : x = k * e - m * f)
    (hkey : x * e + z * f = 2 * e * f - k * (f * f - e * e)) :
    k * f ≤ (m + 2) * e - 1 :=
  column_criterion hf hz hx hkey

/-- At k=1, z≥1 forces f ≤ 2e−1 (no extra column at separated members). -/
theorem sharp_col_k_one {e f z : ℤ} (hf : 0 < f) (hz : 1 ≤ z)
    (hkey : e * e + z * f = 2 * e * f - (f * f - e * e)) :
    f ≤ 2 * e - 1 :=
  k_one_forces_f_le_two_e_sub_one hf hz hkey

/-- Residue step: successive least-positive reps satisfy m ≤ m' ≤ m+1. -/
theorem sharp_col_residue_step {e f k m m' x x' : ℤ} (he : 0 < e) (hef : e < f)
    (hx : x = k * e - m * f) (hx' : x' = (k + 1) * e - m' * f)
    (h1 : 1 ≤ x) (h2 : x ≤ f) (h1' : 1 ≤ x') (h2' : x' ≤ f) :
    m ≤ m' ∧ m' ≤ m + 1 :=
  residue_step he hef hx hx' h1 h2 h1' h2'

/-- Non-vacuity: at (e,f,k,m)=(2,3,1,0): x=2, criterion gives 3≤3, k_one gives 3≤3. -/
theorem sharp_col_witness :
    (0 : ℤ) < 3 ∧ (1 : ℤ) ≤ 1 ∧ (2 : ℤ) = 1 * 2 - 0 * 3 ∧
    2 * 2 + 1 * 3 = 2 * 2 * 3 - 1 * (3 * 3 - 2 * 2) ∧
    1 * 3 ≤ (0 + 2) * 2 - 1 := by norm_num

#print axioms sharp_col_identity
#print axioms sharp_col_criterion
#print axioms sharp_col_k_one
#print axioms sharp_col_residue_step

end Erdos634.Draft.SharpColumnWrap
