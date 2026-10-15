-- Draft/FluxDOrientationChirality.lean: tile chirality need not be consistent across a
-- `CongruentDissection`.  The sign of `(D.tile i).det` is not determined by the dissection
-- structure, so a hypothesis `0 < (D.tile i).det` for all `i` is a genuine, non-vacuous assumption
-- and not a derivable fact.  Imported by `All`.
--
-- Construction: `Tri.det` is defined from `T.pts 0/1/2` as the signed area of the ordered triple,
-- whereas the fields `covers` and `interiors_disjoint` of `Dissection` constrain only `Tri.carrier`
-- (`convexHull ℝ (Set.range T.pts)`), which is invariant under relabelling the domain of `pts`
-- (`PlacementCompleteness.relabel_carrier`).  `Tri.Congruent` quantifies over all isometries,
-- reflections included, and over all vertex permutations, so relabelling one tile by a transposition
-- (`Tri.relabel`, `Tri.congruent_relabel`) keeps the same model and flips the sign of that one tile's
-- `det`.  This is a different mechanism from `OrientationGauge.lean`, where the model-relative
-- status `Tri.Reflected T model` is flipped by re-choosing the model.
--
-- The witness triangle is a fixed symbolic unit right triangle at the origin (the same shape as
-- `wT` in `FluxDOrientation.lean`, reproduced locally to keep the dependency graph small).
import Erdos634.Congruence
import Erdos634.PlacementCompleteness
import Erdos634.CertCoord

namespace Erdos634.Draft.FluxDOrientationChirality

open Erdos634.Geometry Erdos634.CertCoord

/-! ## §1 An absolute chirality flip, one tile at a time

`Tri.det` is defined directly from the ordered triple `(pts 0, pts 1, pts 2)`; relabelling by the
transposition `swap 1 2` swaps the second and third rows of the determinant, which negates it. This
is the exact absolute analogue of `Tri.Congruent`'s freedom to relabel vertices — but unlike
`OrientationGauge`'s model-relative question, it needs no model at all. -/

/-- **Relabelling by `swap 1 2` negates `det`.** The transposition swaps the two edge vectors that
`Tri.det` is built from, which flips the sign of the determinant. -/
theorem Tri.det_relabel_swap12 (T : Tri) :
    (T.relabel (Equiv.swap (1 : Fin 3) 2)).det = -T.det := by
  have h0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have h1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  have h2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
  unfold Tri.det
  rw [Tri.relabel_pts, Tri.relabel_pts, Tri.relabel_pts, h0, h1, h2]
  ring

/-! ## §2 The construction: relabelling one tile of a `CongruentDissection`

Given any `CongruentDissection` `D` and any index `i`, replacing tile `i`'s triangle by its
`swap 1 2`-relabelling — leaving every other tile, the target, and the model untouched — yields
another, equally valid `CongruentDissection`. `covers` and `interiors_disjoint` survive because
`relabel_carrier` says the carrier does not move; `tiles_congruent` survives because
`Tri.congruent_relabel` (composed with the original witness) supplies the new congruence proof
directly against the SAME, unchanged model. -/

/-- **The relabelled dissection.** Only tile `i`'s vertex labelling changes; its carrier, and hence
`covers`/`interiors_disjoint`, are untouched. -/
noncomputable def relabelOneTile {N : ℕ} (D : Dissection N) (i : Fin N) (τ : Equiv.Perm (Fin 3)) :
    Dissection N where
  target := D.target
  tile := Function.update D.tile i ((D.tile i).relabel τ)
  covers := by
    have hc : ∀ j, (Function.update D.tile i ((D.tile i).relabel τ) j).carrier
        = (D.tile j).carrier := by
      intro j
      by_cases hij : j = i
      · subst hij; rw [Function.update_self]
        exact Erdos634.PlacementCompleteness.relabel_carrier (D.tile j) τ
      · rw [Function.update_of_ne hij]
    simpa [hc] using D.covers
  interiors_disjoint := by
    have hc : ∀ j, (Function.update D.tile i ((D.tile i).relabel τ) j).carrier
        = (D.tile j).carrier := by
      intro j
      by_cases hij : j = i
      · subst hij; rw [Function.update_self]
        exact Erdos634.PlacementCompleteness.relabel_carrier (D.tile j) τ
      · rw [Function.update_of_ne hij]
    intro j k hjk
    have := D.interiors_disjoint hjk
    simpa [hc j, hc k] using this

@[simp] theorem relabelOneTile_tile_self {N : ℕ} (D : Dissection N) (i : Fin N)
    (τ : Equiv.Perm (Fin 3)) :
    (relabelOneTile D i τ).tile i = (D.tile i).relabel τ := by
  show Function.update D.tile i ((D.tile i).relabel τ) i = (D.tile i).relabel τ
  rw [Function.update_self]

@[simp] theorem relabelOneTile_tile_other {N : ℕ} (D : Dissection N) (i j : Fin N)
    (τ : Equiv.Perm (Fin 3)) (hij : j ≠ i) :
    (relabelOneTile D i τ).tile j = D.tile j := by
  show Function.update D.tile i ((D.tile i).relabel τ) j = D.tile j
  rw [Function.update_of_ne hij]

@[simp] theorem relabelOneTile_target {N : ℕ} (D : Dissection N) (i : Fin N)
    (τ : Equiv.Perm (Fin 3)) : (relabelOneTile D i τ).target = D.target := rfl

/-- **The relabelled `CongruentDissection`.** Same model, same target, same every-other-tile;
tile `i` is congruent to the model via `Tri.congruent_relabel` composed with the original witness.
Declared with the fully qualified name (rather than inside the current namespace) so that dot
notation `D.relabelOneTile i τ` resolves on a `CongruentDissection` value. -/
noncomputable def _root_.Erdos634.Geometry.CongruentDissection.relabelOneTile {N : ℕ}
    (D : CongruentDissection N) (i : Fin N) (τ : Equiv.Perm (Fin 3)) : CongruentDissection N where
  toDissection := Erdos634.Draft.FluxDOrientationChirality.relabelOneTile D.toDissection i τ
  model := D.model
  tiles_congruent := by
    intro j
    by_cases hij : j = i
    · subst hij
      rw [show (Erdos634.Draft.FluxDOrientationChirality.relabelOneTile D.toDissection j τ).tile j
          = (D.tile j).relabel τ from relabelOneTile_tile_self D.toDissection j τ]
      exact (Tri.congruent_relabel (D.tile j) τ).symm.trans (D.tiles_congruent j)
    · rw [show (Erdos634.Draft.FluxDOrientationChirality.relabelOneTile D.toDissection i τ).tile j
          = D.tile j from relabelOneTile_tile_other D.toDissection i j τ hij]
      exact D.tiles_congruent j

/-- **Projection lemma: the underlying `Dissection` of the relabelled `CongruentDissection`.** -/
theorem _root_.Erdos634.Geometry.CongruentDissection.relabelOneTile_toDissection {N : ℕ} (D : CongruentDissection N)
    (i : Fin N) (τ : Equiv.Perm (Fin 3)) :
    (D.relabelOneTile i τ).toDissection = relabelOneTile D.toDissection i τ := rfl

/-- **The relabelled `CongruentDissection` has the same target.** -/
@[simp] theorem _root_.Erdos634.Geometry.CongruentDissection.relabelOneTile_target {N : ℕ} (D : CongruentDissection N)
    (i : Fin N) (τ : Equiv.Perm (Fin 3)) : (D.relabelOneTile i τ).target = D.target := rfl

/-- **The relabelled `CongruentDissection` has the same model.** -/
@[simp] theorem _root_.Erdos634.Geometry.CongruentDissection.relabelOneTile_model {N : ℕ} (D : CongruentDissection N)
    (i : Fin N) (τ : Equiv.Perm (Fin 3)) : (D.relabelOneTile i τ).model = D.model := rfl

/-- **The relabelled `CongruentDissection`'s tile at the flipped index.** -/
@[simp] theorem _root_.Erdos634.Geometry.CongruentDissection.relabelOneTile_tile_self {N : ℕ} (D : CongruentDissection N)
    (i : Fin N) (τ : Equiv.Perm (Fin 3)) :
    (D.relabelOneTile i τ).tile i = (D.tile i).relabel τ :=
  Erdos634.Draft.FluxDOrientationChirality.relabelOneTile_tile_self D.toDissection i τ

/-- **The relabelled `CongruentDissection`'s tile everywhere else.** -/
@[simp] theorem _root_.Erdos634.Geometry.CongruentDissection.relabelOneTile_tile_other {N : ℕ} (D : CongruentDissection N)
    (i j : Fin N) (τ : Equiv.Perm (Fin 3)) (hij : j ≠ i) :
    (D.relabelOneTile i τ).tile j = D.tile j :=
  Erdos634.Draft.FluxDOrientationChirality.relabelOneTile_tile_other D.toDissection i j τ hij

/-! ## §3 A concrete witness: two valid `CongruentDissection`s differing only in one tile's
chirality

The simplest self-contained instance: `N = 1`, `target = model = tile 0 = wT` (a fixed unit right
triangle, reflexively congruent to itself). Relabelling its one tile by `swap 1 2` produces a
second, equally valid `CongruentDissection 1` — same target, same model, same tile CARRIER — whose
tile now has the OPPOSITE sign of `det`. This is the non-vacuous check that the flip is real, not
merely a possibility on paper. -/
section Witness

/-- The unit right triangle `(0,0), (1,0), (0,1)`, positively oriented (`det = 1 ≠ 0`); reproduced
locally (same shape as phase 1's `FluxDOrientation.wT`) to keep this file's import graph light. -/
noncomputable def wT : Tri := mkTri 0 0 1 0 0 1 (by norm_num [det3])

theorem wT_det_pos : 0 < wT.det := by
  have hpts := mkTri_pts (0:ℝ) 0 1 0 0 1 (by norm_num [det3] : det3 0 0 1 0 0 1 ≠ 0)
  unfold Tri.det
  rw [show wT = mkTri 0 0 1 0 0 1 (by norm_num [det3]) from rfl, hpts]
  simp [mkPt_zero, mkPt_one, PiLp.sub_apply]

/-- `wT` as a trivial `N = 1` `Dissection`: the single tile IS the target. -/
noncomputable def D0 : Dissection 1 where
  target := wT
  tile := fun _ => wT
  covers := by simp [Set.iUnion_const]
  interiors_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

/-- `D0` as a `CongruentDissection`, with model `wT` itself. -/
noncomputable def CD0 : CongruentDissection 1 where
  toDissection := D0
  model := wT
  tiles_congruent := fun _ => Tri.Congruent.refl wT

/-- **The relabelled witness.** -/
noncomputable def CD0' : CongruentDissection 1 :=
  CD0.relabelOneTile 0 (Equiv.swap (1 : Fin 3) 2)

/-- **`CD0`'s one tile is positively oriented.** -/
theorem CD0_tile_pos : 0 < (CD0.tile 0).det := wT_det_pos

/-- **`CD0'`'s one tile is negatively oriented — the SAME target, the SAME model, tiles that are
congruent to the same model both times, yet opposite signs of `det`.** This is the checked,
non-vacuous demonstration that chirality consistency is not derivable from `CongruentDissection`'s
definitions: it is a raw fact about how `pts` happens to be indexed, free to flip tile-by-tile
while everything the definitions constrain (carrier, congruence, target) stays fixed. -/
theorem CD0'_tile_neg : (CD0'.tile 0).det < 0 := by
  have hshow : CD0'.tile 0 = (CD0.tile 0).relabel (Equiv.swap (1 : Fin 3) 2) :=
    CongruentDissection.relabelOneTile_tile_self CD0 0 (Equiv.swap (1 : Fin 3) 2)
  rw [hshow, Tri.det_relabel_swap12]
  linarith [CD0_tile_pos]

/-- **Same target both times.** -/
theorem CD0'_target : CD0'.target = CD0.target :=
  CongruentDissection.relabelOneTile_target CD0 0 (Equiv.swap (1 : Fin 3) 2)

/-- **Same model both times.** -/
theorem CD0'_model : CD0'.model = CD0.model :=
  CongruentDissection.relabelOneTile_model CD0 0 (Equiv.swap (1 : Fin 3) 2)

/-- **Same tile CARRIER both times** (the two tiles are the same physical triangle, only their
vertex labelling differs) — so no geometric quantity that depends only on `carrier` (area,
covering, disjointness — everything `Dissection` itself constrains) can possibly distinguish `CD0`
from `CD0'`. -/
theorem CD0'_tile_carrier : (CD0'.tile 0).carrier = (CD0.tile 0).carrier := by
  have hshow : CD0'.tile 0 = (CD0.tile 0).relabel (Equiv.swap (1 : Fin 3) 2) :=
    CongruentDissection.relabelOneTile_tile_self CD0 0 (Equiv.swap (1 : Fin 3) 2)
  rw [hshow]
  exact Erdos634.PlacementCompleteness.relabel_carrier (CD0.tile 0) (Equiv.swap (1 : Fin 3) 2)

end Witness

/-! ## Closing discussion — the answer, and what it means for phase 3

**The answer is (c): genuinely false in general, proved (not argued) by construction.** For ANY
`CongruentDissection N` `D` and ANY index `i`, `D.relabelOneTile i (Equiv.swap 1 2)` is an equally
valid `CongruentDissection N` — same target, same model, same tile at every OTHER index, same
carrier at index `i` itself — whose `(tile i).det` has the opposite sign from `D`'s. §3 checks this
fires non-vacuously on a genuine (if minimal) `CongruentDissection`: `CD0`'s tile has `det = 1 > 0`
and `CD0'`'s has `det = -1 < 0` (`CD0_tile_pos`, `CD0'_tile_neg`), while target, model, and carrier
are all provably unchanged (`CD0'_target`, `CD0'_model`, `CD0'_tile_carrier`). So "tile chirality
consistency" (`0 < (D.tile i).det` for all `i`, or any other fixed-sign convention) is not a
consequence of `Dissection`/`CongruentDissection`'s fields — it is exactly as free as
`OrientationGauge`'s model-relative question, but by a different, simpler mechanism (no model
needed: one tile alone can be flipped in isolation).

**What this means for phase 2, item (1), precisely.** Route (a) (already provable) is closed off:
it is FALSE that chirality consistency follows from the existing definitions, because the
construction above produces genuine counterexamples from any starting dissection whatsoever,
including presumably-consistent ones. Route (b) is therefore the only live one: any argument that
needs `0 < (D.tile i).det` for all `i` of a REAL corpus dissection (row 4's or row 5's) must take
it as an explicit, named hypothesis — checked non-vacuous by testing it against that dissection's
OWN concrete tiles (the way row3/row4/row5's witnesses already do for their own hypotheses), never
derived from `CongruentDissection` alone. This matches `FluxGRow3Step1.lean`'s own honesty note
for its analogous "not derivable, take as hypothesis" wall (per the dispatch's framing) and is the
same posture `OrientationGauge.lean` settles on for the model-relative question (`atModel`/`step`
taken as a hypothesis, never proved absolutely).

**Consequence for phase 3.**
- Item (2) (the sign of `dir` on `leftDir k` for `WallEndpoints`'s actual `dir`) is UNAFFECTED in
  its own content — it was already independent of this question (`FluxDOrientation.lean`'s closing
  note item 2) — but now provably CANNOT be discharged by first proving item (1) as a theorem,
  since item (1) is false as a theorem. Item (2)'s argument must either (i) carry its own explicit
  chirality hypothesis for the specific tile(s) it needs, checked against the real dissection, or
  (ii) be restated to be manifestly invariant under the `swap 1 2` flip (the way `Tri.OppOrient`/
  `Tri.EqOrient` restate the model-relative question invariantly). This file does not attempt
  either — it only forecloses the route of proving consistency outright first.
- Item (3) (row 5's `hr0`) is likewise unaffected in its own content, but the same warning applies:
  whatever row 5's remaining gap needs from "which physical corner an index names" cannot be
  supplied by an unconditional chirality theorem either, for the identical reason. Still explicitly
  UNCHECKED here whether row 5's `hr0` needs this mechanism at all (per phase 1's own honesty note);
  this file adds no new information on that question either way.

Axiom-clean; no `sorry` (all declarations below compile against `propext`/`Classical.choice`/
`Quot.sound` only — see the `#print axioms` block at the end).
-/

end Erdos634.Draft.FluxDOrientationChirality

#print axioms Erdos634.Draft.FluxDOrientationChirality.Tri.det_relabel_swap12
#print axioms Erdos634.Draft.FluxDOrientationChirality.relabelOneTile
#print axioms Erdos634.Geometry.CongruentDissection.relabelOneTile
#print axioms Erdos634.Draft.FluxDOrientationChirality.wT_det_pos
#print axioms Erdos634.Draft.FluxDOrientationChirality.CD0_tile_pos
#print axioms Erdos634.Draft.FluxDOrientationChirality.CD0'_tile_neg
#print axioms Erdos634.Draft.FluxDOrientationChirality.CD0'_target
#print axioms Erdos634.Draft.FluxDOrientationChirality.CD0'_model
#print axioms Erdos634.Draft.FluxDOrientationChirality.CD0'_tile_carrier
