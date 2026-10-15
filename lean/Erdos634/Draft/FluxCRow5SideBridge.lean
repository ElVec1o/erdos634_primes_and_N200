-- Draft/FluxCRow5SideBridge.lean: the side decomposition `S = p•a + q•b + r•c`, `p, q, r ≥ 0`, of a
-- target side of length `S` into edges of the three types of a `CongruentDissection`, in the shape
-- of the hypothesis `hside` of `Row5.twoPiThree_forces_le_three` and
-- `Row5.sixty_forces_not_gt_three`.
--
-- The existence statement follows from generic machinery that needs no flux functional and no
-- direction grid: `Geometry.Dissection.side_walk_abc` (`EdgeChain.lean`) and
-- `EdgeWordConversion.side_walk_congruent`, which discharges `side_walk_abc`'s edge-length
-- hypothesis for a `CongruentDissection` via `edge_length_trichotomy`.  No angle, tile-relation or
-- irrationality hypothesis is used.
--
-- The remaining work is a reconciliation of conventions: `EdgeWordConversion.sideLen D i` is
-- `dist (D.model.pts i) (D.model.pts (i+1))` (adjacent vertices), while
-- `Tri.oppLen T k := dist (T.pts (k+1)) (T.pts (k+2))` (opposite vertices) is used by `Row5.area`,
-- `Row5.equilateral_boundary` and the corner bridge.  They differ by a fixed index shift,
-- `sideLen D i = oppLen D.model (i-1)`, proved by `decide` on the `Fin 3` shifts.
--
-- Main results: `row5_side_decomposition` and `row5_side_decomposition_int`, for a
-- `CongruentDissection` whose target has a side of length `S` and whose model has opposite-side
-- lengths `a, b, c`.  Not covered: the vanishing `r = 0` needed by `Row5.sixty_forces_not_gt_three`
-- (that is the edge-level sign argument of `FluxCRow5Hr0.lean`); the equality of the three target
-- sides from `∀ k, D.target.angleAt k = π/3` (that is `Row5.equilateral_boundary`; here the single
-- side length `S` is a hypothesis); and the assembly of a full instance of
-- `Row5.twoPiThree_forces_le_three`, which needs `hc2`, `hD`, `hab2` from `Row5.area` and
-- `Row5.equilateral_boundary`.  The statement is unconditional; combined with Theorem E's full
-- hypothesis set it inherits the conditionality noted in `FluxCRow5Complete.lean`.
import Erdos634.EdgeWordConversion
import Erdos634.Draft.FluxCRow5

namespace Erdos634.Row5SideBridge

open Erdos634.Geometry

variable {N : ℕ}

/-- **Naming reconciliation.** `EdgeWordConversion.sideLen`'s adjacent-vertex convention and
`Tri.oppLen`'s opposite-vertex convention differ by the fixed shift `i ↦ i - 1` on `Fin 3` — a
`decide`-checkable fact about the two `Fin 3` indices, not a new geometric input. -/
theorem sideLen_eq_oppLen (D : CongruentDissection N) :
    Erdos634.EdgeWordConversion.sideLen D 0 = D.model.oppLen 2 ∧
    Erdos634.EdgeWordConversion.sideLen D 1 = D.model.oppLen 0 ∧
    Erdos634.EdgeWordConversion.sideLen D 2 = D.model.oppLen 1 := by
  have h20 : (2 : Fin 3) + 1 = 0 := by decide
  have h21 : (2 : Fin 3) + 2 = 1 := by decide
  have h01 : (0 : Fin 3) + 1 = 1 := by decide
  have h02 : (0 : Fin 3) + 2 = 2 := by decide
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have h12 : (1 : Fin 3) + 2 = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · show dist (D.model.pts 0) (D.model.pts 1) = dist (D.model.pts (2 + 1)) (D.model.pts (2 + 2))
    rw [h20, h21]
  · show dist (D.model.pts 1) (D.model.pts (1 + 1)) = dist (D.model.pts (0 + 1)) (D.model.pts (0 + 2))
    rw [h01, h02, h11]
  · show dist (D.model.pts 2) (D.model.pts (2 + 1)) = dist (D.model.pts (1 + 1)) (D.model.pts (1 + 2))
    rw [h20, h11, h12]

/-- **The E8 side-decomposition EXISTENCE half, unconditional.** For a real `CongruentDissection`
whose target's `0`-side has length `S` and whose model's opposite-side lengths are `a, b, c`, `S`
is a nonnegative-integer combination of `a, b, c` — the shape `Row5.twoPiThree_forces_le_three` /
`Row5.sixty_forces_not_gt_three` need for `hside`, built here from `side_walk_abc` alone (no angle
or tile-relation hypothesis). -/
theorem row5_side_decomposition (D : CongruentDissection N) (a b c S : ℝ)
    (ha : D.model.oppLen 0 = a) (hb : D.model.oppLen 1 = b) (hc : D.model.oppLen 2 = c)
    (hS : dist (D.target.pts 0) (D.target.pts 1) = S) :
    ∃ p q r : ℕ, S = (p : ℝ) * a + (q : ℝ) * b + (r : ℝ) * c ∧ p + q + r ≤ 3 * N := by
  obtain ⟨P, Q, R, hPQR, hcard⟩ := Erdos634.EdgeWordConversion.side_walk_congruent D 0
  obtain ⟨e0, e1, e2⟩ := sideLen_eq_oppLen D
  have h01 : (0 : Fin 3) + 1 = 1 := by decide
  rw [h01] at hPQR
  rw [e0, e1, e2, ha, hb, hc, hS] at hPQR
  exact ⟨Q, R, P, by linarith [hPQR], by omega⟩

/-- **The ℤ form, matching `Row5.twoPiThree_forces_le_three`'s `hside`/`hp0`/`hq0` exactly.** -/
theorem row5_side_decomposition_int (D : CongruentDissection N) (a b c S : ℝ)
    (ha : D.model.oppLen 0 = a) (hb : D.model.oppLen 1 = b) (hc : D.model.oppLen 2 = c)
    (hS : dist (D.target.pts 0) (D.target.pts 1) = S) :
    ∃ p q r : ℤ, 0 ≤ p ∧ 0 ≤ q ∧ S = (p : ℝ) * a + (q : ℝ) * b + (r : ℝ) * c := by
  obtain ⟨p, q, r, heq, -⟩ := row5_side_decomposition D a b c S ha hb hc hS
  exact ⟨(p : ℤ), (q : ℤ), (r : ℤ), by positivity, by positivity, by push_cast; exact heq⟩

end Erdos634.Row5SideBridge

#print axioms Erdos634.Row5SideBridge.sideLen_eq_oppLen
#print axioms Erdos634.Row5SideBridge.row5_side_decomposition
#print axioms Erdos634.Row5SideBridge.row5_side_decomposition_int
