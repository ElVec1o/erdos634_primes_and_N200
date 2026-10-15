import Erdos634.OrderForcing

/-!
# The α-vertex gap, general: arithmetic wrapper

At a general coprime member (e,f) with f≥2, no tiling vertex
on the α-row has integer abscissa in two specific senses:

1. **`avgen_no_f2_divides_e2`**: ¬(f² ∣ e²), so the direct-foot lattice condition fails.
2. **`avgen_no_f_divides_e3`**: ¬(f ∣ e³), so the mirrored-foot lattice condition fails.
3. **`avgen_foot_offset_cleared`**: the offset identity f·(2c·cosβ − 3a) = −e³ (ℤ form).
4. **`avgen_foot_offset_real`**: the identity 2f²·cosβ − 3a = −e³/f in ℝ.

Only the arithmetic exclusions and the foot offset are formalized.  The notions 'cover piece',
'foot', 'row origin', 'direct'/'mirrored' are not defined in Lean, and there is no Lean
statement of the row-1 placement exclusion.
-/

namespace Erdos634.Draft.AvgenWrap

open Erdos634.OrderForcing

/-- lem:avgen arithmetic (i): f² ∤ e² when Coprime e f, f ≥ 2. -/
theorem avgen_no_f2_divides_e2 {e f : ℕ} (hf : 2 ≤ f) (hco : Nat.Coprime e f) :
    ¬ (f * f ∣ e * e) :=
  (alpha_vertex_gap_gen hf hco).1

/-- lem:avgen arithmetic (ii): f ∤ e³ when Coprime e f, f ≥ 2. -/
theorem avgen_no_f_divides_e3 {e f : ℕ} (hf : 2 ≤ f) (hco : Nat.Coprime e f) :
    ¬ (f ∣ e * e * e) :=
  (alpha_vertex_gap_gen hf hco).2

/-- lem:avgen offset identity (ℤ form): f·(2c·cosβ − 3a) = −e³. -/
theorem avgen_foot_offset_cleared (e f : ℤ) :
    e * (3 * f ^ 2 - e ^ 2) - 3 * (e * f) * f = -(e ^ 3) :=
  mirrored_foot_offset_cleared e f

/-- lem:avgen offset identity (ℝ form): 2f²·cosβ − 3a = −e³/f. -/
theorem avgen_foot_offset_real (e f cb : ℝ) (hf : f ≠ 0)
    (hcb : cb = e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3)) :
    2 * f ^ 2 * cb - 3 * (e * f) = -(e ^ 3) / f :=
  mirrored_foot_offset e f cb hf hcb

#print axioms avgen_no_f2_divides_e2
#print axioms avgen_no_f_divides_e3
#print axioms avgen_foot_offset_cleared
#print axioms avgen_foot_offset_real

end Erdos634.Draft.AvgenWrap
