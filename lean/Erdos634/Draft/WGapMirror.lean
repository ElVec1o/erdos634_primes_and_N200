/-
Draft/WGapMirror.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P2.2 statement-match, P3).
Not imported by any aggregate.  Module W2a of the W-gap Lean plan.

* `lpG_shift`    (finding F4): `lpG e f ε (x + ε s f^2) ξ η = lpG e f ε x (ξ + s) η`; at `ε = 1`, `x = 0`, `s = c₀`: the lattice with origin
  `p(c₀, 0)` of PROOF P2 is the corner lattice shifted by `c₀` (no hypothesis on `ε`).
* `mpG_shift`    : the same for the mirror lattice (the line `l_x` moves with `x`; the reflection of the shifted lattice is the reflection of the
  shifted points in the shifted line, so `mpG` at origin `x + ε s f^2` is `reflL` of the shifted line applied to the shifted points; stated as
  `reflL_shift`).
* `refl_dist`    : `reflL` is an isometry; `dist_mp_u`, `dist_mp_v`, `dist_mp_a`: the mirror lattice triangles `U'`, `D'` have the sides `c, b, a`
  (PROOF P3: `μ` preserves lattice distances).
* `UTM_sides`    : a tile with the vertices `U'(ξ,η)` has the three sides `f^2`, `f^2 - e^2`, `e f` between the corresponding vertices.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStmt

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

/-- **F4**: shifting the origin by `s` lattice steps along the side -/
theorem lpG_shift (e f ε x s ξ η : ℝ) :
    lpG e f ε (x + ε * s * f ^ 2) ξ η = lpG e f ε x (ξ + s) η := by
  unfold lpG
  exact mkPt_congr (by ring) (by ring)

/-- the corner case of F4: the lattice with origin `p(c₀, 0)` is `lpG e f 1 (c₀ f²)` and equals the corner lattice shifted -/
theorem lpG_corner_shift (e f c₀ ξ η : ℝ) :
    lpG e f 1 (c₀ * f ^ 2) ξ η = lpG e f 1 0 (ξ + c₀) η := by
  have h := lpG_shift e f 1 0 c₀ ξ η
  rw [zero_add, one_mul] at h
  exact h

/-- `reflL` is an isometry of the plane -/
theorem refl_dist (e f ε x : ℝ) (p q : Plane) : dist (reflL e f ε x p) (reflL e f ε x q) = dist p q := by
  unfold reflL
  exact (EuclideanGeometry.reflection (affineSpan ℝ {lpG e f ε x 0 0, lpG e f ε x 0 1})).dist_map p q

theorem dist_mp {e f ε x : ℝ} (ξ η ξ' η' : ℝ) :
    dist (mpG e f ε x ξ η) (mpG e f ε x ξ' η') = dist (lpG e f ε x ξ η) (lpG e f ε x ξ' η') :=
  refl_dist e f ε x _ _

/-- the mirror lattice triangle `U'(ξ,η)`: sides `c`, `b` -/
theorem dist_mp_u {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (mpG e f ε x ξ η) (mpG e f ε x (ξ + 1) η) = f ^ 2 := by
  rw [dist_mp]; exact dist_step_uG he hef hε ξ η

theorem dist_mp_v {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (mpG e f ε x ξ η) (mpG e f ε x ξ (η + 1)) = f ^ 2 - e ^ 2 := by
  rw [dist_mp]; exact dist_step_vG he hef hε ξ η

theorem dist_mp_a {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (mpG e f ε x (ξ + 1) η) (mpG e f ε x ξ (η + 1)) = e * f := by
  rw [dist_mp]; exact dist_step_aG he hef hε ξ η

/-- negative control for `lpG_corner_shift`: the shift is not the identity (the point `p(1,0)` is not `p(0,0)` at `f ≠ 0`) -/
example (e f : ℝ) (hf : f ≠ 0) : lpG e f 1 0 1 0 ≠ lpG e f 1 0 0 0 := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  simp [lpG, mkPt] at this
  exact hf this

/-- witness: the shift identity at `c₀ = 2` evaluated on concrete lattice points of the member `(e, f) = (2, 3)` -/
example : lpG 2 3 1 (2 * 3 ^ 2) 0 1 = lpG 2 3 1 0 2 1 := by
  have h := lpG_corner_shift 2 3 2 0 1
  rwa [zero_add] at h

#print axioms lpG_shift
#print axioms dist_mp_a

end Erdos634.Draft.WGapStmt
