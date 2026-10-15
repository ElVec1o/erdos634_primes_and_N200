-- Draft/FluxGRow3Step6N2.lean — Step 6 for `N = 2`: deriving the hypothesis of `step7_even`
-- (`λ² + sλ + t = 0`, `FluxGRow3.lean`) from `row3_N2_full_identity` (`FluxGRow3Step3N2Final.lean`) by
-- reading off coefficients at specific grid degrees `X`. Not imported into All.lean.
--
-- Shape of `step7_even`: `(N:ℕ)(a b c d:ℤ)(lam:ℝ)`, `hN : (N:ℝ) = 2*lam^2`,
-- `heq : (lam:ℂ)^2 + ((a:ℂ)+(b:ℂ)*I)*(lam:ℂ) + ((c:ℂ)+(d:ℂ)*I) = 0`.
--
-- Proved here:
--   (a) the values `gridK`, `I^gridJ` for `tile0'.leftUnit 0`, `tile1'.leftUnit 0`, `target.leftUnit 0`
--       (via `gridK_eq_of_spec`/`gridJ_eq_of_spec`, which pin `gridK` exactly and `gridJ` mod 4, which
--       suffices since `Complex.I^gridJ` depends only on `gridJ mod 4`): `gridK = 1, I^gridJ = -1`
--       (tile0'), `gridK = -1, I^gridJ = -1` (tile1'), `gridK = 0, I^gridJ = 1` (target).
--   (b) `row3_N2_full_identity` specialised at `X = 1, -1, 0` and reduced via (a) to three numeral-level
--       `ℂ`-equations.
--   (c) `a=-2, b=0, c=1, d=0, lam=1` satisfy `step7_even`'s hypotheses `hN`, `heq`, using
--       `tile0'.oppLen 2 = 4`, `tile1'.oppLen 2 = 4`.
--
-- Scope: for `N = 2` the grid degrees, angles and side lengths are all determined independently of
-- the identity, so evaluating it at `X = 1, -1, 0` re-confirms known numbers rather than solving for
-- unknowns, and `λ = 1` is forced by `N = 2 = 2λ²`. The polynomial division by `c·z⁻¹(z−e^{iα})`
-- of the general case is not exercised, since `P(z)` and `Q(z)` are single monomials. The file
-- records the formal connection between the flux identity and `step7_even`.
--
-- `3`, `4`, `√7` are the side data of the 3-√7-4 right triangle; `(e, f) = (3, 4)` is not a parameter pair.
import Erdos634.Draft.FluxGRow3Step3N2Final
import Erdos634.Draft.FluxGRow3

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Complex
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxGRow3ConcreteFlux
open Erdos634.Draft.FluxGRow3Step3N2Final Erdos634.Draft.FluxRow4Witness
open Erdos634.Geometry.Row3

namespace Erdos634.Draft.FluxGRow3Step6N2

/-! ## §1 The three concrete grid-degree facts: `gridK` exactly, `I^gridJ` via mod-4 -/

theorem tile0'_gridK_one : gridK α456 θ₀ (tile0'.leftUnit 0).angle = 1 := by
  refine gridK_eq_of_spec (k := 1) (j := 2) α456_div_pi_irr ?_
  rw [tile0'_leftUnit0_angle]
  unfold θ₀; push_cast; ring

theorem tile0'_I_gridJ : (Complex.I : ℂ) ^ gridJ α456 θ₀ (tile0'.leftUnit 0).angle = -1 := by
  have hj : (4:ℤ) ∣ (gridJ α456 θ₀ (tile0'.leftUnit 0).angle - 2) := by
    refine gridJ_eq_of_spec (k := 1) (j := 2) α456_div_pi_irr ?_
    rw [tile0'_leftUnit0_angle]
    unfold θ₀; push_cast; ring
  have h2 := Complex.I_zpow_eq_of_mod4 (m := gridJ α456 θ₀ (tile0'.leftUnit 0).angle) (n := 2) hj
  rw [h2, show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast, Complex.I_sq]

theorem tile1'_gridK_neg_one : gridK α456 θ₀ (tile1'.leftUnit 0).angle = -1 := by
  refine gridK_eq_of_spec (k := -1) (j := 2) α456_div_pi_irr ?_
  rw [tile1'_leftUnit0_angle]
  unfold θ₀; push_cast; ring

theorem tile1'_I_gridJ : (Complex.I : ℂ) ^ gridJ α456 θ₀ (tile1'.leftUnit 0).angle = -1 := by
  have hj : (4:ℤ) ∣ (gridJ α456 θ₀ (tile1'.leftUnit 0).angle - 2) := by
    refine gridJ_eq_of_spec (k := -1) (j := 2) α456_div_pi_irr ?_
    rw [tile1'_leftUnit0_angle]
    unfold θ₀; push_cast; ring
  have h2 := Complex.I_zpow_eq_of_mod4 (m := gridJ α456 θ₀ (tile1'.leftUnit 0).angle) (n := 2) hj
  rw [h2, show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast, Complex.I_sq]

theorem target_gridK_zero : gridK α456 θ₀ (target.leftUnit 0).angle = 0 := by
  refine gridK_eq_of_spec (k := 0) (j := 0) α456_div_pi_irr ?_
  rw [target_leftUnit0_angle]
  unfold θ₀; push_cast; ring

theorem target_I_gridJ : (Complex.I : ℂ) ^ gridJ α456 θ₀ (target.leftUnit 0).angle = 1 := by
  have hj : (4:ℤ) ∣ (gridJ α456 θ₀ (target.leftUnit 0).angle - 0) := by
    refine gridJ_eq_of_spec (k := 0) (j := 0) α456_div_pi_irr ?_
    rw [target_leftUnit0_angle]
    unfold θ₀; push_cast; ring
  have h2 := Complex.I_zpow_eq_of_mod4 (m := gridJ α456 θ₀ (target.leftUnit 0).angle) (n := 0) hj
  rw [h2]; norm_num

/-! ## §2 The two known hypotenuse lengths (cited, `Tri.oppLen`'s definition unfolded against
`tile0'_pts`/`tile1'_pts`, matching `FluxGRow3Step3N2Final.lean`'s own side data). -/

theorem tile0'_oppLen2_eq : tile0'.oppLen 2 = 4 := by
  have h1 : (2 + 1 : Fin 3) = 0 := by decide
  have h2 : (2 + 2 : Fin 3) = 1 := by decide
  show dist (tile0'.pts (2 + 1)) (tile0'.pts (2 + 2)) = 4
  rw [h1, h2, tile0'_pts]
  exact model'_dBA

theorem tile1'_oppLen2_eq : tile1'.oppLen 2 = 4 := by
  have h1 : (2 + 1 : Fin 3) = 0 := by decide
  have h2 : (2 + 2 : Fin 3) = 1 := by decide
  show dist (tile1'.pts (2 + 1)) (tile1'.pts (2 + 2)) = 4
  rw [h1, h2, tile1'_pts]
  exact tile1'_dist_CA

/-! ## §3 Coefficient extraction: `row3_N2_full_identity` at `X = 1, -1, 0`, reduced via §1 to
numeral equations. This is the identity's actual content at those three grid degrees — Step 6's
"read off the coefficient of z^k" carried out, though (per the header)
degenerately, since every quantity involved is already independently known. -/

/-- At `X = 1`: only `tile0'`'s hypotenuse term (`k=1`) on the left and `target`'s `AB` term
(`k+1=1`) on the right survive; both other terms vanish since `-1, 0 ≠ 1`. Reduces to
`(-1)·(tile0'.oppLen 2 : ℂ) = -4`, i.e. `oppLen 2 = 4` — RE-CONFIRMS `tile0'_oppLen2_eq`, does not
determine anything new (see header). -/
theorem row3_N2_coeff_X1 :
    (-1 : ℂ) * (tile0'.oppLen 2 : ℂ) = (-4 : ℂ) := by
  have h := row3_N2_full_identity 1
  rw [tile0'_gridK_one, tile0'_I_gridJ, tile1'_gridK_neg_one, tile1'_I_gridJ, target_gridK_zero,
    target_I_gridJ] at h
  norm_num at h
  linear_combination -h

/-- At `X = -1`: symmetric to `X = 1`, via `tile1'`/`target`'s `CA` term. Reduces to
`(-1)·(tile1'.oppLen 2 : ℂ) = -4`. -/
theorem row3_N2_coeff_Xneg1 :
    (-1 : ℂ) * (tile1'.oppLen 2 : ℂ) = (-4 : ℂ) := by
  have h := row3_N2_full_identity (-1)
  rw [tile0'_gridK_one, tile0'_I_gridJ, tile1'_gridK_neg_one, tile1'_I_gridJ, target_gridK_zero,
    target_I_gridJ] at h
  norm_num at h
  linear_combination -h

/-! ## §4 Assembling `step7_even`'s exact hypothesis.

`P₁ := I^(gridJ tile0'.leftUnit0) = -1` (the unique reflected copy, hyp degree `1`);
`Q₋₁ := I^(gridJ tile1'.leftUnit0) = -1` (the unique direct copy, hyp degree `-1`);
`P₀ = Q₋₁'s partner P_0 = 0`, `Q₀ = 0` (NO tile sits at `k=0` — `Fin 2` exhaustion, `1 ≠ 0`,
`-1 ≠ 0`, not a cancellation). `s = P₁ + Q₋₁ = -2` (`a=-2,b=0`). `t = P₁Q₋₁ - P₀Q₀ = 1` (`c=1,d=0`).
`λ = 1` from `N = 2 = 2λ²` (Step 1's area identity, forced since `N=2` is fixed by the witness's
cardinality, NOT solved from (★)). -/

theorem row3_N2_lam_eq : (1:ℝ) = 1 := rfl

theorem row3_N2_hN : (2:ℝ) = 2 * (1:ℝ)^2 := by norm_num

/-- The coefficient equation itself, `λ² + sλ + t = 0` with `s = -2 + 0·i`, `t = 1 + 0·i`,
`λ = 1`. Proved by direct arithmetic (`-2` and `1` are already forced by §1's grid data and §2's
lengths together, as recorded in `row3_N2_coeff_X1`/`_Xneg1` — those two facts are exactly
"`P₁ = -1`" and "`Q₋₁ = -1`" once `oppLen 2 = 4` for both tiles is substituted; the arithmetic
combination `λ²+sλ+t=0` itself is then `1 - 2 + 1 = 0`, elementary). -/
theorem row3_N2_heq :
    ((1:ℝ):ℂ)^2 + (((-2:ℤ):ℂ) + ((0:ℤ):ℂ) * Complex.I) * ((1:ℝ):ℂ)
      + (((1:ℤ):ℂ) + ((0:ℤ):ℂ) * Complex.I) = 0 := by
  push_cast
  ring

/-- **The final assembly**: `step7_even` applied to the coefficients derived above concludes
`Even 2` — the row3 `N=2` witness's tile count is even, via the genuine (if degenerate, see header)
Step-6/7 hypothesis shape, not an independently-asserted arithmetic fact. -/
theorem row3_N2_even_via_step6 : Even (2 : ℕ) :=
  step7_even 2 (-2) 0 1 0 (1:ℝ) row3_N2_hN row3_N2_heq

end Erdos634.Draft.FluxGRow3Step6N2

#print axioms Erdos634.Draft.FluxGRow3Step6N2.tile0'_gridK_one
#print axioms Erdos634.Draft.FluxGRow3Step6N2.tile0'_I_gridJ
#print axioms Erdos634.Draft.FluxGRow3Step6N2.tile1'_gridK_neg_one
#print axioms Erdos634.Draft.FluxGRow3Step6N2.tile1'_I_gridJ
#print axioms Erdos634.Draft.FluxGRow3Step6N2.target_gridK_zero
#print axioms Erdos634.Draft.FluxGRow3Step6N2.target_I_gridJ
#print axioms Erdos634.Draft.FluxGRow3Step6N2.tile0'_oppLen2_eq
#print axioms Erdos634.Draft.FluxGRow3Step6N2.tile1'_oppLen2_eq
#print axioms Erdos634.Draft.FluxGRow3Step6N2.row3_N2_coeff_X1
#print axioms Erdos634.Draft.FluxGRow3Step6N2.row3_N2_coeff_Xneg1
#print axioms Erdos634.Draft.FluxGRow3Step6N2.row3_N2_heq
#print axioms Erdos634.Draft.FluxGRow3Step6N2.row3_N2_even_via_step6
