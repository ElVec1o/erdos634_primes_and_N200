/-
Draft/WGapStmt.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P0.4, P3, P6.1, P7.1).
Not imported by any aggregate.  NO theorem with `sorry` here (those are in `WGapStmt_Scratch20261115.lean`, never imported).

Module W1b of the W-gap Lean plan: the DEFINITIONS of the statement layer, reusing the project's corner chart.

THE CHART (reuse, nothing new).  The hand proof's chart (PROOF 0.4: corner `P` at the origin, side `s` on the positive real axis, `Δ` above,
second side `s'` in the direction `e(2α)`) IS the normal form of `SideRunGA`: a `SetupG D e f α β γ L ax ay` (target `Q = (0,0)`, `B = (L,0)`,
`A = (ax, ay)`) with `CornersA e f L ax ay` (first form: the angle at the origin is `2α`), and the lattice `lpG e f 1 x ξ η`
(`ε = 1`).  `p(i, j)` of PROOF 0.4 is `lpG e f 1 0 i j`; the lattice with origin `p(c₀, 0)` of PROOF P2 is `lpG e f 1 (c₀ f²) · ·`
(`lpG x ξ η = P + ξ u + η v`, `P = (x,0)`, `u = (f²,0)`).  `H(k)` of PROOF 0.5 is exactly the hypothesis list of `corner_run_mirror`
(`ChainG` run of `k` tiles `C1` from the corner, `hsucc`) plus `MirrorAt D e f 1 0 0` (= (H2): the mirror tile `T_0`).

NEW DEFINITIONS.
* `reflL e f ε x`   : the reflection in the line `l_x = {p(0,0), p(0,1)}` of the lattice with origin `P = (x,0)` (PROOF 0.4: `μ(z) = ω² z̄`);
  `mpG e f ε x ξ η = μ (lpG e f ε x ξ η)`  (`p'(ξ, η)`).
* `UTM`, `DTM`     : the mirror lattice triangles `U'(ξ,η) = μ U(ξ,η)`, `D'(ξ,η) = μ D(ξ,η)` are tiles (PROOF P3).
  The STATION mirror lattice of PROOF 6.1 (`q'(i,j) = μ_O p(c₀+i, J+j)`) is `mpG e f 1 (c₀ f²) i (J + j)`; the strip tile `E_y = μ_O U(c₀, y)` is
  `UTM D e f 1 x 0 y`.
* `Corner2 e f ax ay`: the first form of `CornersA.hA` (angle exactly `2α` at the origin) and `H4`: `|s'| > (f − 1) c` in squared form.
* `St2 D e f x J`   : (St2) of PROOF 6.1: a tile `F_O` on the LEFT of `L_O = O + R e(2α)` with an edge of length `b` on `L_O` starting at `O`
  (`L_O` has the direction of the `c`-edge of `E_0`, i.e. `mpG x 1 J − mpG x 0 J`; `b = ν c`).
* `EdgeCover`       : the form of "a tile with the point `X` in the relative interior of an edge on a line, covering the open half-disk on a side"
  that the project already uses (conclusion of `CtxJ.phiJ`): a tile `φ` containing `X`, with `localAngle X = π`, containing every short push
  `X + ε' w` into the open side in its interior.
* `ZeroNoTile`: nothing.
Checks: `mpG` at `ξ = 0` is `lpG` (the line `l_x` is fixed by `μ`): `mpG_zero`; `St2`/`EdgeCover` are `Prop`s over the existing `HasV`, `cross`.
No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerRun
import Erdos634.Draft.SideRunGCornerMirror

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

variable {N : ℕ}

/-- the reflection `μ` in the line `l_x` through `p(0,0)` and `p(0,1)` of the lattice with origin `P = (x,0)` -/
noncomputable def reflL (e f ε x : ℝ) : Plane → Plane :=
  EuclideanGeometry.reflection (affineSpan ℝ {lpG e f ε x 0 0, lpG e f ε x 0 1})

/-- the mirror lattice point `p'(ξ, η) = μ p(ξ, η)` -/
noncomputable def mpG (e f ε x ξ η : ℝ) : Plane := reflL e f ε x (lpG e f ε x ξ η)

/-- `U'(ξ,η) = μ U(ξ,η)` is a tile (PROOF P3) -/
def UTM (D : CongruentDissection N) (e f ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (mpG e f ε x ξ η) (mpG e f ε x (ξ + 1) η) (mpG e f ε x ξ (η + 1))

/-- `D'(ξ,η) = μ D(ξ,η)` is a tile -/
def DTM (D : CongruentDissection N) (e f ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (mpG e f ε x (ξ + 1) η) (mpG e f ε x ξ (η + 1)) (mpG e f ε x (ξ + 1) (η + 1))

/-- the angle `2α` at the origin of the normal form: the first form of `CornersA.hA` -/
def Corner2 (e f : ℕ) (ax ay : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
    ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ))

/-- (H4) of PROOF P0.5/P11: the second side `s' = [Q, A]` is longer than `(f − 1) c` (squared form) -/
def H4 (f : ℕ) (ax ay : ℝ) : Prop :=
  (((f : ℝ) - 1) * (f : ℝ) ^ 2) ^ 2 < ax ^ 2 + ay ^ 2

/-- (St2) of PROOF 6.1 at the station `O = p(c₀, J)` (`x = c₀ f²`): a tile with the vertices `O`, `W = O + ν (V_E − O)` (the end of an edge of
length `b` on `L_O`, `V_E = q'(1,0)`, `ν = b/c`) and `R`, with `R` on the left of the directed line `L_O` (direction `V_E − O`). -/
def St2 (D : CongruentDissection N) (e f x : ℝ) (J : ℝ) : Prop :=
  ∃ (F : Fin N) (W R : Plane),
    HasV D F (mpG e f 1 x 0 J) W R ∧
    W = mpG e f 1 x 0 J + nuG e f • (mpG e f 1 x 1 J - mpG e f 1 x 0 J) ∧
    0 < cross (mpG e f 1 x 1 J - mpG e f 1 x 0 J) (R - mpG e f 1 x 0 J)

/-- **A tile straddles the point `X` along a line**: `X` lies in the relative interior of an edge, so the tile has the straight angle at `X` and
contains every short push from `X` into the open side `0 < cross d (w)` in its interior (the shape of the conclusion of `CtxJ.phiJ`). -/
def EdgeCover (D : CongruentDissection N) (X d : Plane) : Prop :=
  ∃ φ : Fin N, X ∈ (D.tile φ).carrier ∧ (D.tile φ).localAngle X = Real.pi ∧
    ∀ w : Plane, 0 < cross d w → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ → X + ε' • w ∈ interior (D.tile φ).carrier

/-- `μ` fixes the points of the line `l_x`: `p'(0, η) = p(0, η)` for `η = 0, 1` -/
theorem mpG_zero_zero (e f ε x : ℝ) : mpG e f ε x 0 0 = lpG e f ε x 0 0 := by
  unfold mpG reflL
  exact EuclideanGeometry.reflection_eq_self_iff _ |>.mpr (left_mem_affineSpan_pair ℝ _ _)

theorem mpG_zero_one (e f ε x : ℝ) : mpG e f ε x 0 1 = lpG e f ε x 0 1 := by
  unfold mpG reflL
  exact EuclideanGeometry.reflection_eq_self_iff _ |>.mpr (right_mem_affineSpan_pair ℝ _ _)

/-- `H4` is satisfiable together with `Corner2` (witness: scale `t` large) -/
theorem corner2_H4_witness (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ∃ ax ay : ℝ, Corner2 e f ax ay ∧ H4 f ax ay := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf1 : (1 : ℝ) ≤ f := by
    have : (1 : ℕ) ≤ f := by omega
    exact_mod_cast this
  have hrt := rtG_pos he0 hefR
  have h2f : (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hK : 0 < (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) :=
    mul_pos (mul_pos he0 h2f) hrt
  set K := (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) with hKdef
  set B := ((f : ℝ) - 1) * (f : ℝ) ^ 2 with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; exact mul_nonneg (by linarith) (by positivity)
  set t := (B + 1) / K with ht
  have htpos : 0 < t := div_pos (by linarith) hK
  have htK : t * K = B + 1 := by rw [ht]; field_simp
  refine ⟨t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4), t * K, ⟨t, htpos, rfl, rfl⟩, ?_⟩
  unfold H4
  rw [htK]
  nlinarith [sq_nonneg (t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4))]

end Erdos634.Draft.WGapStmt
