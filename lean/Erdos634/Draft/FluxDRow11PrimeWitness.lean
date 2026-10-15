-- Draft/FluxDRow11PrimeWitness.lean: witnesses for Draft/FluxDRow11Prime.lean.
--
-- `Row11.prime_excluded` concludes `False`; its geometric hypotheses (a tiling of the base-α target)
-- have no known instance at any `N`, so it is a conditional.  What is witnessed is the arithmetic
-- chain it runs, at the algebraic model `s = e/f = 1/2`, `M = 5`, `N = 21` (`d = 1`, `m = 1`, leg
-- `3c`, `X' = 12`): every arithmetic hypothesis holds there except primality (`21 = 3·7`), and the
-- intermediate conclusion `(2f+e) ∣ M` is reached through `IsoAlpha.isoalpha_X_forces`.
import Erdos634.Draft.FluxDRow11Prime

namespace Erdos634.Draft.FluxDRow11PrimeWitness

/-- The algebraic model's data: the tiling equation `q = F(s)` at `s = 1/2, M = 5, N = 21`, the leg
integrality `X'(2f+e) = M f²(f+e)` with `X' = 12`, the reduced equation `N d = m²(2e+d)(e²+4ed+2d²)`,
coprimality — and `21` is not prime. -/
theorem model21 : (21 : ℝ) * (1 - 1 / 2) * (2 + 1 / 2) ^ 2 = (5 : ℝ) ^ 2 * (1 + 1 / 2) * (2 - (1 / 2) ^ 2) ∧
    12 * (2 * (1 + 1) + 1) = 5 * ((1 + 1 + 1) * (1 + 1) ^ 2) ∧
    21 * 1 = 1 ^ 2 * ((2 * 1 + 1) * (1 ^ 2 + 4 * 1 * 1 + 2 * 1 ^ 2)) ∧
    Nat.Coprime 1 (1 + 1) ∧ ¬ Nat.Prime 21 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `IsoAlpha.isoalpha_X_forces` on the model: `(2f + e) = 5 ∣ M = 5`. -/
theorem X_forces_21 : (2 * (1 + 1) + 1) ∣ 5 :=
  Erdos634.IsoAlpha.isoalpha_X_forces 1 (1 + 1) 5 12 (by norm_num) (by norm_num)

end Erdos634.Draft.FluxDRow11PrimeWitness

#print axioms Erdos634.Draft.FluxDRow11PrimeWitness.model21
#print axioms Erdos634.Draft.FluxDRow11PrimeWitness.X_forces_21
