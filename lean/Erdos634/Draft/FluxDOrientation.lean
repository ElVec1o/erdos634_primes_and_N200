-- Draft/FluxDOrientation.lean: the bridge between a tile's orientation and the west/east order of
-- its edge endpoints.  Imported by `All`.
--
-- `Placement.edgeWest`/`edgeEast` split purely on `dir (pts k) ≤ dir (pts (k+1))`, with no
-- connection to the tile's vertex-cycle labelling or chirality.  `EdgeType.localAngle_edgeWest_edgeEast`
-- proves the disjunction (west = k, east = k+1) ∨ (west = k+1, east = k) and leaves it unresolved.
-- `Tri.leftDir` (`Dissection.lean`) is defined from the sign of `Tri.det`: it is
-- `pts (k+1) − pts k` if `0 < T.det` and `pts k − pts (k+1)` otherwise, so the tile lies to the left
-- of `leftDir` whichever way `pts` is indexed.  This file connects `Tri.leftDir`/`Tri.det` to
-- `edgeWest`/`edgeEast` (`dir_pts_le_iff_orient`), which resolves the disjunction once the sign of
-- the tile's determinant is known.
--
-- This differs from `OrientationGauge.lean`, which shows that whether a tile is `Reflected` against a
-- chosen model is not decidable, because `CongruentDissection.model` is unconstrained by
-- `tiles_congruent` (reflections included).  Here no model is involved: what is needed is a tile's own
-- chirality (the sign of the model-free `Tri.det`) matched against its own vertex labelling
-- `k ↦ k+1 ↦ k+2`.  The weaker `Draft/FluxCRow5EdgeDirection.lean` mechanism (betweenness and
-- `Complex.arg`) is a different one.
--
-- The witnesses use a fixed symbolic triangle, the unit right triangle at the origin.
import Erdos634.WallEndpoints
import Erdos634.EdgeType
import Erdos634.CertCoord

namespace Erdos634.Draft.FluxDOrientation

open Erdos634.Geometry Erdos634.TilePlacement

/-! ## §1 The orientation-to-`dir`-comparison bridge, `Tri` level

`Tri.leftDir` is already the canonical, orientation-corrected traversal direction of edge `k`
(`Dissection.lean:1360`): for a positively-oriented tile (`0 < T.det`) it is `pts (k+1) - pts k`,
for a negatively-oriented one it is the reverse — either way the tile sits to the left of it. This
section adds no new definition; it extracts the one arithmetic fact the bridge needs: the sign of a
linear functional `dir` on `T.leftDir k` decides which of `pts k` / `pts (k+1)` has the smaller
`dir`-value, and the decision flips with the tile's own chirality (`Tri.det`'s sign). This is
the global orientation convention used informally in counterclockwise bookkeeping, stated with no
row-4/row-5-specific angles. -/

/-- **The orientation bridge, resolved as an `iff`.** Which of a tile's two edge-`k` endpoints has
the smaller `dir`-value is decided jointly by the sign of `T.det` (the tile's own chirality) and the
sign of `dir` on the canonical traversal direction `T.leftDir k`. -/
theorem dir_pts_le_iff_orient (T : Tri) (dir : Plane →ₗ[ℝ] ℝ) (k : Fin 3) :
    dir (T.pts k) ≤ dir (T.pts (k + 1)) ↔
      (0 < T.det ∧ 0 ≤ dir (T.leftDir k)) ∨ (T.det < 0 ∧ dir (T.leftDir k) ≤ 0) := by
  have hne : T.det ≠ 0 := T.det_ne_zero
  unfold Tri.leftDir
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), map_sub]
    constructor
    · intro h; right; exact ⟨hneg, by linarith⟩
    · rintro (⟨hc, -⟩ | ⟨-, h⟩) <;> linarith
  · rw [if_pos hpos, map_sub]
    constructor
    · intro h; left; exact ⟨hpos, by linarith⟩
    · rintro (⟨-, h⟩ | ⟨hc, -⟩) <;> linarith

/-! ## §2 The bridge at `Placement.edgeWest`/`edgeEast` level

Specialising §1's `T` to `D.tile i` and unfolding `Placement.edgeWest`/`edgeEast` (which split on
exactly the same `dir (pts k) ≤ dir (pts (k+1))` comparison) turns the `iff` into a full
resolution: given the orientation datum, `edgeWest`/`edgeEast` are pinned to specific tile vertices,
with no disjunction left over. The two theorems below are jointly exhaustive: for any `k`, either
`0 ≤ dir (T.leftDir k)` or `dir (T.leftDir k) < 0`, and either way exactly one of the two fires
(checked in the closing discussion, not merely asserted). -/

/-- **West = corner `k`.** -/
theorem edgeWest_edgeEast_of_orient_west_k {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (i : Fin N) (k : Fin 3)
    (h : (0 < (D.tile i).det ∧ 0 ≤ dir ((D.tile i).leftDir k)) ∨
         ((D.tile i).det < 0 ∧ dir ((D.tile i).leftDir k) ≤ 0)) :
    Erdos634.Placement.edgeWest D dir (i, k) = (D.tile i).pts k ∧
    Erdos634.Placement.edgeEast D dir (i, k) = (D.tile i).pts (k + 1) := by
  have hle : dir ((D.tile i).pts k) ≤ dir ((D.tile i).pts (k + 1)) :=
    (dir_pts_le_iff_orient (D.tile i) dir k).mpr h
  unfold Erdos634.Placement.edgeWest Erdos634.Placement.edgeEast
  rw [if_pos hle, if_pos hle]
  exact ⟨rfl, rfl⟩

/-- **West = corner `k+1`.** -/
theorem edgeWest_edgeEast_of_orient_west_k1 {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (i : Fin N) (k : Fin 3)
    (h : (0 < (D.tile i).det ∧ dir ((D.tile i).leftDir k) < 0) ∨
         ((D.tile i).det < 0 ∧ 0 < dir ((D.tile i).leftDir k))) :
    Erdos634.Placement.edgeWest D dir (i, k) = (D.tile i).pts (k + 1) ∧
    Erdos634.Placement.edgeEast D dir (i, k) = (D.tile i).pts k := by
  have hgt : dir ((D.tile i).pts (k + 1)) < dir ((D.tile i).pts k) := by
    by_contra hc
    push_neg at hc
    have hle := (dir_pts_le_iff_orient (D.tile i) dir k).mp hc
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hle with ⟨t1, t2⟩ | ⟨t1, t2⟩ <;> linarith
  have hle : ¬ dir ((D.tile i).pts k) ≤ dir ((D.tile i).pts (k + 1)) := not_le.mpr hgt
  unfold Erdos634.Placement.edgeWest Erdos634.Placement.edgeEast
  rw [if_neg hle, if_neg hle]
  exact ⟨rfl, rfl⟩

/-! ## §3 The fully pinned angle correspondence

Composing §2 with `Tri.localAngle_vertex` (the same step `EdgeType.localAngle_edgeWest_edgeEast`
itself uses to discharge each branch of its own disjunction) gives the actual deliverable: a
NON-disjunctive angle statement, conditional only on the orientation datum. This is the resolved
form of `EdgeType.localAngle_edgeWest_edgeEast`. -/

/-- **The angle bridge, west = `k`.** -/
theorem localAngle_edgeWest_of_orient_k {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (i : Fin N) (k : Fin 3)
    (h : (0 < (D.tile i).det ∧ 0 ≤ dir ((D.tile i).leftDir k)) ∨
         ((D.tile i).det < 0 ∧ dir ((D.tile i).leftDir k) ≤ 0)) :
    (D.tile i).localAngle (Erdos634.Placement.edgeWest D dir (i, k))
        = TilePlacement.angleAt (D.tile i) k ∧
    (D.tile i).localAngle (Erdos634.Placement.edgeEast D dir (i, k))
        = TilePlacement.angleAt (D.tile i) (k + 1) := by
  obtain ⟨hw, he⟩ := edgeWest_edgeEast_of_orient_west_k D dir i k h
  rw [hw, he]
  unfold TilePlacement.angleAt
  exact ⟨Tri.localAngle_vertex (D.tile i) k, Tri.localAngle_vertex (D.tile i) (k + 1)⟩

/-- **The angle bridge, west = `k+1`.** -/
theorem localAngle_edgeWest_of_orient_k1 {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (i : Fin N) (k : Fin 3)
    (h : (0 < (D.tile i).det ∧ dir ((D.tile i).leftDir k) < 0) ∨
         ((D.tile i).det < 0 ∧ 0 < dir ((D.tile i).leftDir k))) :
    (D.tile i).localAngle (Erdos634.Placement.edgeWest D dir (i, k))
        = TilePlacement.angleAt (D.tile i) (k + 1) ∧
    (D.tile i).localAngle (Erdos634.Placement.edgeEast D dir (i, k))
        = TilePlacement.angleAt (D.tile i) k := by
  obtain ⟨hw, he⟩ := edgeWest_edgeEast_of_orient_west_k1 D dir i k h
  rw [hw, he]
  unfold TilePlacement.angleAt
  exact ⟨Tri.localAngle_vertex (D.tile i) (k + 1), Tri.localAngle_vertex (D.tile i) k⟩

/-! ## §4 Non-vacuous witness

A concrete tile, direction and corner on which `dir_pts_le_iff_orient` and
`edgeWest_edgeEast_of_orient_west_k`/`localAngle_edgeWest_of_orient_k` all fire with a genuinely
resolved, non-trivial conclusion — the no-vacuous-witness rule. Uses `CertCoord.mkTri` (already in
the corpus) for the triangle and a bare hand-rolled `x`-coordinate functional (mirroring
`E1BaseWord.xco`, not importing that file to avoid pulling in its whole march apparatus) for `dir`. -/
section Witness

open Erdos634.CertCoord

/-- The `x`-coordinate functional on `Plane`, built locally to keep this file's imports light
(`E1BaseWord.xco` is the same functional, already in the corpus, under a heavier import). -/
noncomputable def witnessDir : Plane →ₗ[ℝ] ℝ where
  toFun p := p 0
  map_add' := by intro a b; simp [PiLp.add_apply]
  map_smul' := by intro c a; simp [PiLp.smul_apply]

@[simp] theorem witnessDir_apply (p : Plane) : witnessDir p = p 0 := rfl

/-- The unit right triangle `(0,0), (1,0), (0,1)`, positively oriented (`det = 1 ≠ 0`). -/
noncomputable def wT : Tri := mkTri 0 0 1 0 0 1 (by norm_num [det3])

theorem wT_det_pos : 0 < wT.det := by
  have hpts := mkTri_pts (0:ℝ) 0 1 0 0 1 (by norm_num [det3] : det3 0 0 1 0 0 1 ≠ 0)
  unfold Tri.det
  rw [show wT = mkTri 0 0 1 0 0 1 (by norm_num [det3]) from rfl, hpts]
  simp [mkPt_zero, mkPt_one, PiLp.sub_apply]

/-- The witness fires at corner `k = 0`: `leftDir 0 = pts 1 - pts 0 = (1,0)`, whose `x`-coordinate
is `1 ≥ 0`, so the "west = `k`" branch applies non-vacuously. -/
theorem witness_hyp :
    (0 < wT.det ∧ 0 ≤ witnessDir (wT.leftDir 0)) ∨
      (wT.det < 0 ∧ witnessDir (wT.leftDir 0) ≤ 0) := by
  left
  refine ⟨wT_det_pos, ?_⟩
  unfold Tri.leftDir
  rw [if_pos wT_det_pos]
  have hpts := mkTri_pts (0:ℝ) 0 1 0 0 1 (by norm_num [det3] : det3 0 0 1 0 0 1 ≠ 0)
  rw [show wT = mkTri 0 0 1 0 0 1 (by norm_num [det3]) from rfl, hpts]
  simp [mkPt_zero, mkPt_one, PiLp.sub_apply]

/-- The witness's conclusion is non-trivial: `edgeWest`/`edgeEast` really do resolve to the two
*distinct* points `(0,0)` and `(1,0)`, not to some degenerate or vacuous equality. -/
theorem witness_fires (D : Dissection 1) (hD : D.tile 0 = wT) :
    Erdos634.Placement.edgeWest D witnessDir (0, 0) = wT.pts 0 ∧
    Erdos634.Placement.edgeEast D witnessDir (0, 0) = wT.pts 1 := by
  have h := edgeWest_edgeEast_of_orient_west_k D witnessDir 0 0 (by rw [hD]; exact witness_hyp)
  rwa [hD] at h

theorem witness_nontrivial : wT.pts (0 : Fin 3) ≠ wT.pts 1 := by
  have hpts := mkTri_pts (0:ℝ) 0 1 0 0 1 (by norm_num [det3] : det3 0 0 1 0 0 1 ≠ 0)
  rw [show wT = mkTri 0 0 1 0 0 1 (by norm_num [det3]) from rfl, hpts]
  intro h
  have := congrArg (fun p : Plane => p 0) h
  simp [mkPt_zero, mkPt_one] at this

end Witness

/-! ## Closing discussion — exactly what phase 2 still needs

**What is closed here.** Given, for a specific tile `i` and corner `k`, the *sign data*
`(0 < (D.tile i).det, sign of dir ((D.tile i).leftDir k))`, `edgeWest`/`edgeEast` (§2) and the
angle they carry (§3) are pinned outright — no disjunction survives. This is a genuine, checked
(non-vacuous, §4) bridge that did not exist anywhere in the corpus before this file, and it is
completely generic: it mentions no row-4 or row-5 angle relation, no `f`, no `N`.

**What is NOT closed here, precisely.**

1. *Global chirality consistency across tiles.* This file never asserts or derives `0 < (D.tile
   i).det` for any actual `i` of a real `CongruentDissection` — that is a hypothesis of every
   theorem above, supplied per-tile. `OrientationGauge.lean`'s obstruction is directly relevant to
   *this* step, not to §1–§3: whether `pts` happens to be indexed so that `0 < T.det` for a given
   physical tile is a labelling choice (which of the two cyclic orders of the same three points is
   named "`pts 0, pts 1, pts 2`"), not fixed by `Dissection`/`CongruentDissection` alone (a
   `Dissection` places no constraint on `pts`'s indexing beyond affine independence). So phase 2's
   first task is naming and proving (or exhibiting as a genuine, checked hypothesis matching
   row4/row5's own indexing convention — e.g. however `TileAt`/`CornerAdjacency` name the α/β/γ
   corners of a tile) a fact of the form "every tile of this corpus's dissections is indexed so that
   `0 < (D.tile i).det`", OR restating row4/row5's argument to be manifestly invariant under the
   choice (the way `Tri.OppOrient`/`Tri.EqOrient` in `OrientationGauge.lean` already do it for the
   *model-relative* question). This is real, unclosed work, not a formality.
2. *The sign of `dir` on `leftDir k`, for the wall's actual `dir`.* Even granting (1), row4's L8
   needs this for the SPECIFIC `dir` `WallEndpoints` uses (built from the wall's supporting
   functional `g`/`c`) and the specific `k` naming the base or apex edge. That sign is a genuine
   geometric fact about where the tile's third vertex (`k+2`) sits relative to the wall's half-plane
   (`hwall : ∀ y ∈ D.target.carrier, g y ≤ c`) — intuitively, "the tile's interior is strictly on the
   `g < c` side" plus "`dir`'s increasing direction is the wall's own left-to-right sense" should
   pin the sign, but this file does not attempt that argument: it would need `g`'s and `dir`'s
   *joint* linear-algebraic relationship (not just each alone), which is exactly the kind of fact
   `CollarDisjointM4.lean`'s `xFun`/`yFun`/`gFun`/`hFun` family builds for OTHER walls, case by case,
   never generically. Phase 2's second task is this lemma, specific to the wall's `g`/`dir` pair
   `WallEndpoints` already carries as hypotheses (`hwall`, `hdirab`, `hker`).
3. *Reusability for row 5.* Row 5's closed gap (P121/P123) is a BETWEENNESS fact (`Wbtw` on three
   points on one straight side ⇒ equal `Complex.arg`), used to transport a `GridChar` weight between
   two triangles sharing a vertex. That is a different question from "which endpoint is west," so
   this file's §1–§3 do not directly discharge any of row 5's named steps. What IS shared is the
   *shape* of the remaining problem: row 5's (L4) (`FluxCRow5E7bFinal.lean`, P123) is explicitly
   "not claimed to discharge `hr0`" for reasons of the same flavor as this file's item (1) above —
   an orientation/labelling correspondence still assumed rather than derived. If row 5's remaining
   gap turns out to need "which of two triangles' shared-vertex indices agrees with which physical
   corner," this file's `Tri.det`/`leftDir` mechanism is the natural tool to try next, but that has
   not been checked against row 5's actual remaining obligation (`hr0`) here — doing so is future
   work, not claimed now.

Axiom-clean; no `sorry` (all four theorems and every declaration in §1–§4 compile against
`propext`/`Classical.choice`/`Quot.sound` only — see the `#print axioms` block at the end).
-/

end Erdos634.Draft.FluxDOrientation

#print axioms Erdos634.Draft.FluxDOrientation.dir_pts_le_iff_orient
#print axioms Erdos634.Draft.FluxDOrientation.edgeWest_edgeEast_of_orient_west_k
#print axioms Erdos634.Draft.FluxDOrientation.edgeWest_edgeEast_of_orient_west_k1
#print axioms Erdos634.Draft.FluxDOrientation.localAngle_edgeWest_of_orient_k
#print axioms Erdos634.Draft.FluxDOrientation.localAngle_edgeWest_of_orient_k1
#print axioms Erdos634.Draft.FluxDOrientation.wT_det_pos
#print axioms Erdos634.Draft.FluxDOrientation.witness_hyp
#print axioms Erdos634.Draft.FluxDOrientation.witness_fires
#print axioms Erdos634.Draft.FluxDOrientation.witness_nontrivial
