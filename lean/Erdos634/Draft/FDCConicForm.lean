-- Draft/FDCConicForm.lean — the "requires" direction of the conic form.
-- A 2π/3 tiling of an equilateral target with integer sides yields the conic form.
-- Composition of `FDCEqSpec.eqspecint_paper` (tiling → s,t,q integers)
-- with `EquilateralConic.conicform_2pi3` (s,t,q → conic factorization).
-- Imported by `All`.

import Erdos634.Draft.FDCEqSpec
import Erdos634.EquilateralConic

namespace Erdos634.Draft.FDCConicForm

open Erdos634.Geometry Erdos634.Draft

/-- **`prop:conicform`, 2π/3 half, "requires" direction from a real tiling.**
Given a `CongruentDissection N` of an equilateral target by a 2π/3 tile with integer sides,
the count N satisfies the conic form: there exist integers u,v with
  u·v = 16N², 2 ∣ (u+v), (u+v)/2 − 5N = s², and s ∣ 3N.

Proof: `eqspecint_paper` extracts integers s,t,q; `conicform_2pi3` packages them.
-/
theorem conicform_of_tiling {N : ℕ} (D : CongruentDissection N) {α a b c S : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (hint : ∃ a' b' c' : ℤ, (a' : ℝ) = a ∧ (b' : ℝ) = b ∧ (c' : ℝ) = c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hS : ∀ k, D.target.oppLen k = S) :
    ∃ u v : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      ∃ s : ℤ, (u + v) / 2 - 5 * (N : ℤ) = s ^ 2 ∧ s ∣ 3 * (N : ℤ) := by
  obtain ⟨s, t, q, _, _, _, _, _, _, _, _, _, hst, hconic⟩ :=
    FDCEqSpec.eqspecint_paper D hα h hint hP hS
  obtain ⟨u, v, huv, hpar, hsum, hdvd⟩ := EquilateralConic.conicform_2pi3 s t N q
    (mul_comm s t ▸ hst) hconic
  exact ⟨u, v, huv, hpar, s, hsum, hdvd⟩

#print axioms Erdos634.Draft.FDCConicForm.conicform_of_tiling

end Erdos634.Draft.FDCConicForm
