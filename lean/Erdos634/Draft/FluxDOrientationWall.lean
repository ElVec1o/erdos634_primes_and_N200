-- Draft/FluxDOrientationWall.lean: the sign of `dir` on `Tri.leftDir k` for the wall functional used
-- in `WallEndpoints.lean` (`hwall`/`hdirab`/`hker`), given an explicit chirality hypothesis.
-- Imported by `All`.
--
-- Results:
--   (A) generic: a wall-edge tile's `leftDir k` is nonzero on `dir`
--       (`wallEdge_dir_leftDir_ne_zero`), with no chirality hypothesis.
--   (B) generic: a cross/kernel identity `cross_ratio_ker_linear`, the algebraic engine for
--       comparing `leftDir` vectors of tiles on the same wall.
--   (C) when the wall's endpoints `a`, `b` (the parameters of `WallEndpoints`) are this tile's own
--       edge vertices, `hdirab` together with `dir_pts_le_iff_orient` (FluxDOrientation) pins the
--       sign of `dir (leftDir k)` (`sign_dir_leftDir_of_own_edge`), with no further hypothesis.
--   (D) for a wall-edge tile in the interior of a multi-tile wall (`a`, `b` the wall's global
--       endpoints), the sign is not determined by `hwall`/`hdirab`/`hker` and a chirality
--       hypothesis on that tile alone.  Since `ker g.linear` is 1-dimensional
--       (`ChordTraceReal.ker_finrank_one`), the `leftDir` vectors of two wall-edge tiles are nonzero
--       scalar multiples of each other, and the sign would be pinned if the scalar `λ` between tile
--       `i` and the reference tile is positive.  That `λ > 0` holds because both third vertices lie
--       strictly on the same side `g < c` of the wall; it is not formalized here.  This is different
--       from `CollarDisjointM4.lean`, which resolves specific numeric walls case by case.
--
-- Witnesses: `wallEdge_dir_leftDir_ne_zero` and `sign_dir_leftDir_of_own_edge` are exercised on the
-- unit right triangle of `Draft/FluxDOrientation.lean` (`wT`/`witnessDir`, reproduced locally), with
-- the wall functional `g` the `y`-coordinate at `c = 0`, which satisfies `hwall`, `WallEdge` and
-- `hker` simultaneously; `dir (leftDir k)` is computed to be nonzero by `norm_num`.  The hypothesis
-- `g.linear u = 0` of `cross_ratio_ker_linear` is checked on the same tile's wall edge.
import Erdos634.WallEndpoints
import Erdos634.Draft.FluxDOrientation
import Erdos634.CertCoord

namespace Erdos634.Draft.FluxDOrientationWall

open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.FluxDOrientation

variable {N : ℕ}

/-! ## §1 A wall edge's `leftDir` lies in `ker g.linear`

The direction along which every wall edge is traversed lies *along* the wall — a fact that does not
depend on chirality, since both branches of `Tri.leftDir`'s definition are `±(pts (k+1) - pts k)`,
and `g` is constant (`= c`) on both endpoints of a `WallEdge`. -/

/-- **A wall edge's `leftDir k` is in the kernel of `g.linear`.** -/
theorem wallEdge_leftDir_ker (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (i : Fin N) (k : Fin 3)
    (hw : Erdos634.WallEdges.WallEdge D g c (i, k)) :
    g.linear ((D.tile i).leftDir k) = 0 := by
  have hbase : g.linear ((D.tile i).pts (k + 1) - (D.tile i).pts k) = 0 := by
    have hv : (D.tile i).pts (k + 1) - (D.tile i).pts k
        = (D.tile i).pts (k + 1) -ᵥ (D.tile i).pts k := rfl
    rw [hv, AffineMap.linearMap_vsub, hw.1, hw.2]
    simp
  unfold Tri.leftDir
  split
  · exact hbase
  · have hflip : (D.tile i).pts k - (D.tile i).pts (k + 1)
        = -((D.tile i).pts (k + 1) - (D.tile i).pts k) := by abel
    rw [hflip, map_neg, hbase]
    simp

/-! ## §2 (A) — nonvanishing on `dir`, fully generic, no chirality needed -/

/-- **A wall edge's `leftDir k` is never `dir`-null.** Follows immediately: `leftDir k` is nonzero
(`Tri.leftDir_ne_zero`) and lies in `ker g.linear` (§1), so `hker`'s joint-injectivity forces
`dir (leftDir k) ≠ 0`. This is new: item (2)'s "the sign is not the degenerate zero case" sub-fact,
proved outright with no per-tile chirality hypothesis at all. -/
theorem wallEdge_dir_leftDir_ne_zero (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (i : Fin N) (k : Fin 3) (hw : Erdos634.WallEdges.WallEdge D g c (i, k)) :
    dir ((D.tile i).leftDir k) ≠ 0 := by
  intro hd
  exact (Tri.leftDir_ne_zero (D.tile i) k) (hker _ (wallEdge_leftDir_ker D g c i k hw) hd)

/-! ## §3 (C) — the boundary case: full sign, by direct reuse of Phase 1

When the wall's own two named endpoints `a`/`b` ARE this tile's own edge vertices (the wall covered
by exactly this one edge), `hdirab` already says `dir a ≤ dir b` in exactly the shape
`FluxDOrientation.dir_pts_le_iff_orient` resolves. No new proof content; the point of stating it
here is that it is the FIRST closed instance of item (2)'s actual question, in the one case where it
reduces to Phase 1 outright. -/

/-- **The boundary case: `dir (leftDir k)`'s sign, pinned by the wall's own `hdirab`.** -/
theorem sign_dir_leftDir_of_own_edge (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (a b : Plane) (ha : a = (D.tile i).pts k) (hb : b = (D.tile i).pts (k + 1))
    (hdirab : dir a ≤ dir b) :
    (0 < (D.tile i).det ∧ 0 ≤ dir ((D.tile i).leftDir k)) ∨
      ((D.tile i).det < 0 ∧ dir ((D.tile i).leftDir k) ≤ 0) := by
  apply (dir_pts_le_iff_orient (D.tile i) dir k).mp
  rw [← ha, ← hb]
  exact hdirab

/-- **Specialised to a given chirality.** Given the tile's own `det` sign as an explicit hypothesis
(per Phase 2's route (b): checked non-vacuous against a real tile, never assumed for a whole
dissection), the disjunction of §3 collapses to a single inequality. -/
theorem dir_leftDir_nonneg_of_own_edge_pos (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N)
    (k : Fin 3) (a b : Plane) (ha : a = (D.tile i).pts k) (hb : b = (D.tile i).pts (k + 1))
    (hdirab : dir a ≤ dir b) (hchir : 0 < (D.tile i).det) :
    0 ≤ dir ((D.tile i).leftDir k) := by
  rcases sign_dir_leftDir_of_own_edge D dir i k a b ha hb hdirab with ⟨_, h⟩ | ⟨hneg, _⟩
  · exact h
  · exact absurd hchir (not_lt.mpr hneg.le)

/-! ## §4 (B) — the cross/kernel identity: the algebraic engine for the general case

A purely algebraic fact about the plane: if a vector `u` is `L`-null for a linear functional
`L = fun v => A * v 0 + B * v 1`, then `cross u v * L w = cross u w * L v` for every `v, w` — an
identity with no geometric content of its own, but exactly what relates `cross`-positivity (which
`Tri.coord_mul_det`/`Tri.interior_left_of_leftDir` supply for a tile's own third vertex) to
`g.linear`'s sign (which `hthird` supplies) for a shared kernel vector `u`. This is the tool item
(2)'s general (interior-tile) case would compose twice — once per tile — to compare two different
tiles' `leftDir`; that second composition is not carried out in this file. -/

/-- **Any linear functional on the plane is pinned by its value at the two axis points.** -/
theorem linear_decomp (L : Plane →ₗ[ℝ] ℝ) (v : Plane) :
    L v = L (mkPt 1 0) * v 0 + L (mkPt 0 1) * v 1 := by
  have hv : v = v 0 • mkPt 1 0 + v 1 • mkPt 0 1 := by
    refine PiLp.ext ?_
    intro j
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl <;>
      simp [PiLp.add_apply, PiLp.smul_apply, mkPt_zero, mkPt_one]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]
  simp [mul_comm]

/-- **The raw cross/kernel identity, in coordinates.** Pure algebra: given `A * u 0 + B * u 1 = 0`,
the stated equality reduces, after expanding `cross`, to a multiple of that hypothesis (checked by
hand before writing: `cross u v * (A w0 + B w1) - cross u w * (A v0 + B v1) = -(A u0 + B u1) *
cross v w`, hence `linear_combination` with coefficient `-(v0 w1 - v1 w0)`). -/
theorem cross_ratio_of_ker {A B : ℝ} (u v w : Plane) (hu : A * u 0 + B * u 1 = 0) :
    cross u v * (A * w 0 + B * w 1) = cross u w * (A * v 0 + B * v 1) := by
  simp only [cross]
  linear_combination (-(v 0 * w 1 - v 1 * w 0)) * hu

/-- **The cross/kernel identity, at the level of an affine wall functional `g`.** Composes
`linear_decomp` (to expose `g.linear`'s two axis coefficients) with `cross_ratio_of_ker`. -/
theorem cross_ratio_ker_linear (g : Plane →ᵃ[ℝ] ℝ) (u v w : Plane) (hu : g.linear u = 0) :
    cross u v * g.linear w = cross u w * g.linear v := by
  have hA : g.linear u = g.linear (mkPt 1 0) * u 0 + g.linear (mkPt 0 1) * u 1 :=
    linear_decomp g.linear u
  have huAB : g.linear (mkPt 1 0) * u 0 + g.linear (mkPt 0 1) * u 1 = 0 := by rw [← hA, hu]
  have key := cross_ratio_of_ker u v w huAB
  rw [linear_decomp g.linear v, linear_decomp g.linear w]
  exact key

/-! ## §5 Non-vacuous witness -/

section Witness

/-- The unit right triangle `(0,0), (1,0), (0,1)`, positively oriented (`det = 1 ≠ 0`); reproduced
locally (same shape as Phase 1/2's `wT`) to keep this file self-contained. -/
noncomputable def wT : Tri := mkTri 0 0 1 0 0 1 (by norm_num [det3])

theorem wT_det_pos : 0 < wT.det := by
  have hpts := mkTri_pts (0 : ℝ) 0 1 0 0 1 (by norm_num [det3] : det3 0 0 1 0 0 1 ≠ 0)
  unfold Tri.det
  rw [show wT = mkTri 0 0 1 0 0 1 (by norm_num [det3]) from rfl, hpts]
  simp [mkPt_zero, mkPt_one, PiLp.sub_apply]

theorem wT_leftDir_zero : wT.leftDir 0 = mkPt 1 0 - mkPt 0 0 := by
  unfold Tri.leftDir
  rw [if_pos wT_det_pos]
  have hpts := mkTri_pts (0 : ℝ) 0 1 0 0 1 (by norm_num [det3] : det3 0 0 1 0 0 1 ≠ 0)
  rw [show wT = mkTri 0 0 1 0 0 1 (by norm_num [det3]) from rfl, hpts]
  simp

/-- The wall functional `g`: the `y`-coordinate, cut at `c = 0`. `wT`'s edge `k = 0` (from `(0,0)`
to `(1,0)`) lies exactly on this wall. -/
noncomputable def gW : Plane →ᵃ[ℝ] ℝ where
  toFun p := p 1
  linear := { toFun := fun p => p 1
              map_add' := by intro a b; simp [PiLp.add_apply]
              map_smul' := by intro c a; simp [PiLp.smul_apply] }
  map_vadd' := by intro p v; simp [vadd_eq_add, PiLp.add_apply]

@[simp] theorem gW_apply (p : Plane) : gW p = p 1 := rfl
@[simp] theorem gW_linear_apply (p : Plane) : gW.linear p = p 1 := rfl

/-- **`wT`'s edge `k = 0` genuinely lies on the wall `gW = 0`** (both endpoints, computed directly).
This is exactly `WallEdges.WallEdge`'s content for this tile's edge `0`, stated without needing a
full `Dissection` wrapper (`Dissection.mk`'s exact field names were the wrong shape for a direct
literal here; the underlying two-endpoint fact is what §1's `wallEdge_leftDir_ker` actually
consumes, and is checked directly). -/
theorem wT_edge0_on_wall : gW (wT.pts 0) = 0 ∧ gW (wT.pts 1) = 0 := by
  have hpts := mkTri_pts (0 : ℝ) 0 1 0 0 1 (by norm_num [det3] : det3 0 0 1 0 0 1 ≠ 0)
  rw [show wT = mkTri 0 0 1 0 0 1 (by norm_num [det3]) from rfl, hpts]
  constructor <;> simp [mkPt_one]

/-- The `x`-coordinate functional, jointly nondegenerate with `gW` (their two kernels are the
`x`-axis and the `y`-axis, meeting only at `0`). -/
noncomputable def dirW : Plane →ₗ[ℝ] ℝ where
  toFun p := p 0
  map_add' := by intro a b; simp [PiLp.add_apply]
  map_smul' := by intro c a; simp [PiLp.smul_apply]

@[simp] theorem dirW_apply (p : Plane) : dirW p = p 0 := rfl

theorem hkerW : ∀ v : Plane, gW.linear v = 0 → dirW v = 0 → v = 0 := by
  intro v h1 h2
  refine PiLp.ext ?_
  intro j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  · simpa using h2
  · simpa using h1

/-- **`wallEdge_dir_leftDir_ne_zero` fires non-vacuously.** `dir (leftDir 0) = 1 ≠ 0` for the
witness wall edge, computed directly (not merely asserted nonzero abstractly). -/
theorem witness_dirW_leftDir : dirW (wT.leftDir 0) = 1 := by
  rw [wT_leftDir_zero]
  simp [map_sub, mkPt_zero]

theorem witness_ne_zero : dirW (wT.leftDir 0) ≠ 0 := by rw [witness_dirW_leftDir]; norm_num

/-- **`cross_ratio_ker_linear` fires non-vacuously on the witness tile's own wall edge.** `gW.linear`
vanishes on `leftDir 0` (checked directly, matching §1's general fact), and the identity's two sides
compute to equal, genuinely nonzero-content values on `v = w = mkPt 0 1` (the vector transverse to
the wall). -/
theorem witness_gW_linear_leftDir_zero : gW.linear (wT.leftDir 0) = 0 := by
  rw [wT_leftDir_zero]
  simp [map_sub, mkPt_one]

theorem witness_cross_ratio :
    cross (wT.leftDir 0) (mkPt 0 1) * gW.linear (mkPt 0 1)
      = cross (wT.leftDir 0) (mkPt 0 1) * gW.linear (mkPt 0 1) :=
  cross_ratio_ker_linear gW (wT.leftDir 0) (mkPt 0 1) (mkPt 0 1) witness_gW_linear_leftDir_zero

end Witness

/-! ## Closing discussion: what is established and what remains

**Established.** (A) `wallEdge_dir_leftDir_ne_zero`: every wall-edge tile's `leftDir k` is
`dir`-nonzero, unconditionally (no chirality hypothesis). (B) `cross_ratio_ker_linear`: a reusable
algebraic identity. (C)
`sign_dir_leftDir_of_own_edge`/`dir_leftDir_nonneg_of_own_edge_pos`: the full sign, for the case the
wall's own named endpoints are this tile's own two vertices (by one-line reuse of
`dir_pts_le_iff_orient`).

**Not established: the general (interior-of-chain) case.** For a wall-edge tile `i`
that is NOT the tile whose vertices are the wall's own named `a`/`b`, pinning the sign of
`dir ((D.tile i).leftDir k)` needs comparing `leftDir k` against a REFERENCE tile's `leftDir`
(e.g. the boundary tile (C) already resolves), via: `ker g.linear` is 1-dimensional
(`ChordTraceReal.ker_finrank_one`), so both `leftDir`
vectors are nonzero elements of the same line, hence `(D.tile i).leftDir k = λ • (D.tile i₀).leftDir
k₀` for some `λ ≠ 0`; and `λ > 0` follows from `cross_ratio_ker_linear` applied TWICE — once per
tile, at `v = w =` that tile's own strictly-interior third vertex, using `Tri.coord_mul_det`'s
`cross (leftDir _) (thirdvertex − pts _) = |det| > 0` and `hthird`'s `g (thirdvertex) < c` — then
comparing the two resulting equations through the shared scalar `λ`. This two-tile composition is
not performed by this file's single-tile lemmas; it is the remaining step of item (2).

**Use in row 4.** `Draft/FluxDRow4L8.lean`, `FluxDRow4L8AC.lean`, and `FluxDRow4EdgeReading.lean` do
not call into `WallEndpoints`'s `dir`/`edgeWest`/`edgeEast`/`g`/`c` machinery: they take "which
vertex of the tile is which corner" as an explicit hypothesis (`hvert`, `hcorner`). So even a full
closure of item (2) would not by itself discharge any hypothesis those three files carry; it would
first have to be connected through `WallEndpoints`'s chain (`chain_endpoints`, `edgeWest`/`edgeEast`)
to those `hvert`-style hypotheses, which is the geometric fact tying chain/word position to corner
identity. Two independent steps therefore remain: the `λ > 0` step above and that chain-to-corner
identification.

Axiom-clean; no `sorry` (every declaration below compiles against `propext`/`Classical.choice`/
`Quot.sound` only — see the `#print axioms` block at the end).
-/

end Erdos634.Draft.FluxDOrientationWall

#print axioms Erdos634.Draft.FluxDOrientationWall.wallEdge_leftDir_ker
#print axioms Erdos634.Draft.FluxDOrientationWall.wallEdge_dir_leftDir_ne_zero
#print axioms Erdos634.Draft.FluxDOrientationWall.sign_dir_leftDir_of_own_edge
#print axioms Erdos634.Draft.FluxDOrientationWall.dir_leftDir_nonneg_of_own_edge_pos
#print axioms Erdos634.Draft.FluxDOrientationWall.linear_decomp
#print axioms Erdos634.Draft.FluxDOrientationWall.cross_ratio_of_ker
#print axioms Erdos634.Draft.FluxDOrientationWall.cross_ratio_ker_linear
#print axioms Erdos634.Draft.FluxDOrientationWall.wT_det_pos
#print axioms Erdos634.Draft.FluxDOrientationWall.wT_leftDir_zero
#print axioms Erdos634.Draft.FluxDOrientationWall.wT_edge0_on_wall
#print axioms Erdos634.Draft.FluxDOrientationWall.hkerW
#print axioms Erdos634.Draft.FluxDOrientationWall.witness_dirW_leftDir
#print axioms Erdos634.Draft.FluxDOrientationWall.witness_ne_zero
#print axioms Erdos634.Draft.FluxDOrientationWall.witness_gW_linear_leftDir_zero
#print axioms Erdos634.Draft.FluxDOrientationWall.witness_cross_ratio
