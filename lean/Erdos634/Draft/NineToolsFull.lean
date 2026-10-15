import Erdos634.Draft.NineToolsWrap
import Erdos634.Draft.LemCensusFormal
import Erdos634.Draft.EdgeParity

/-!
# Seven tool classes whose failure point is a theorem

Nine tool classes cannot answer the crossing question.  For seven of them the failure point is a theorem;
`Draft/NineToolsWrap.lean` holds six of the seven, and this file adds the seventh (equilibrium
stresses) and collects the statements in one place.  The other two (the Conway–Lagarias tiling
group, a finite-quotient computation, and the `b`-residue calculus, a count on the kernel-checked
tilings) are computations and are not treated here.

* tool 1, linear direction invariants: `NineToolsWrap.ninetools_metric_never_fires`;
* tool 2, Euler and angle-sum counting: `tool2_one_relation`
  (`LemCensusFormal.census_equations_equiv`: the three balance equations are one relation);
* tool 3, edge-pairing parity: `EdgeParity.edge_count_parity` (for edge-to-edge dissections
  `3N − B` is even) and `tool3_silent` (`Inflation.parity_silent_witnesses`: the parity condition
  is satisfiable at `(1,3)` and `(3,7)`);
* tool 5, similarity-invariant criteria: `NineToolsWrap.ninetools_no_similarity_proof`;
* tool 6, the `γ`-count on a stretch: `NineToolsWrap.ninetools_gamma_two_endpoints_unsat`;
* tool 8, De Bruijn–Hamel functionals: `NineToolsWrap.ninetools_dBH_linear_dep`;
* tool 9, equilibrium stresses: `stress_slack_straight`, `stress_slack_full`: at a vertex of a
  planar framework the balance of the stresses is two scalar equations in as many unknowns as there
  are edges at the vertex; at every vertex figure of a base-`β` tiling other than a corner of the
  target (a straight junction with `k` corners has `k + 1` edges, a full vertex with `k` corners has
  `k`) the number of edges exceeds two by at least two.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.NineToolsFull

/-- Tool 2: the three balance equations of the vertex census are exactly one relation. -/
theorem tool2_one_relation {N n1 n2 v1 v2 v3 v4 : ℕ} :
    (3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N ∧
      2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N ∧ n1 + 3 * v1 + 2 * v2 + v3 = N)
    ↔ (3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N ∧ v1 = 1 + n2 + v3 + 2 * v4) :=
  Erdos634.Draft.LemCensusFormal.census_equations_equiv

/-- Tool 3: the parity condition is satisfiable at `(1,3)` and `(3,7)`. -/
theorem tool3_silent :
    (3 * 3 ^ 2 = 2 * 8 + 11 ∧ 11 + 1 = 4 * 3) ∧ (3 * 7 ^ 2 = 2 * 61 + 25 ∧ 25 + 3 = 4 * 7) :=
  Erdos634.Inflation.parity_silent_witnesses

/-- Tool 9, straight junctions: the figures are `{γ, α, β}` and `{3α, 2β}`; with `k` corners there
are `k + 1` edges at the point, and `k + 1 − 2 ≥ 2`. -/
theorem stress_slack_straight (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 2) :
    2 ≤ (x + y + z + 1) - 2 := by omega

/-- Tool 9, full vertices: the figures are `{β, 3γ}`, `{2α, 2β, 2γ}`, `{4α, 3β, γ}`, `{6α, 4β}`;
with `k` corners there are `k` edges at the point, and `k − 2 ≥ 2`. -/
theorem stress_slack_full (x y z : ℕ) (h1 : x + 2 * z = 6) (h2 : y + z = 4) :
    2 ≤ (x + y + z) - 2 := by omega

/-- The slack `2` is attained: at the figures `{γ, α, β}` and `{β, 3γ}`. -/
theorem stress_slack_attained : (1 + 1 + 1 + 1) - 2 = 2 ∧ (0 + 1 + 3) - 2 = 2 := by decide

end Erdos634.Draft.NineToolsFull
