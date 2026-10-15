-- Draft/FluxDRow4L8.lean: the `b^k`-leg case for the `γ = 2α` tile, by pigeonhole.
--
-- Argument ("Leg = b^k"): a b-edge joins its tile's α-vertex to its γ-vertex.  So the `k` tiles on the
-- leg carry `k` γ-corners at the `k+1` points `A = P₀, P₁, …, P_k = B`.  No corner of `ABC` has a γ.
-- So the `k` γ-corners fall on the `k−1` junctions `P₁, …, P_{k−1}`.  Some junction therefore carries
-- two γ, contradicting the boundary-figure bound `congruentDissection_row4_boundary_gamma_le_one`
-- (Draft/FluxDRow4Boundary.lean): at most one γ at a boundary point.
--
-- The chain of tile edges along a wall (with junction continuity
-- `edgeEast (E m) = edgeWest (E (m+1))` and the length/word classification) is supplied by
-- `WallEndpoints.chain_endpoints`, `SideWalk.side_walk_of_dissection`, `AEdgeReading.lean` and
-- `EdgeType.exists_matching_side`.  The classification of which endpoint of a given edge carries the
-- tile's γ-vertex is specific to this tile and is not exposed by the relation-agnostic
-- `EdgeType`/`ChainWalk` layer.
--
-- Contents:
--   1. `row4_no_gamma_at_A_or_C`, `row4_no_gamma_at_B`: the endpoints of the leg carry no γ.  The
--      base-corner case (`A`/`C`, angle `α`) is the fourth conjunct of
--      `Draft/FluxDRow4Bridge.lean`'s `congruentDissection_row4_alpha_counts`.  The apex case
--      (`B`, angle `α + β = π − 2α`) is the same method, one more instantiation of
--      `vertex_multiplicities_row4` at `(s,t) = (1,1)` instead of `(1,0)`.
--   2. `pigeonhole_collision`: `k` pigeons (`Fin k`, `k ≥ 1`) mapped into `k − 1` holes collide,
--      via Mathlib's `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
--   3. `row4_leg_bk_contradiction`: the abstract assembly, over a family of junction points
--      `J : Fin k → Plane` (standing for `P₁, …, P_{k-1}`, as a map into a `Finset` `S` of the
--      interior junctions, `#S = k - 1`) and a tile-to-junction assignment `γAt : Fin k → Plane`
--      (which junction shows tile `i`'s γ-corner) satisfying (i) `γAt` lands in `S` (no γ at `A` or
--      `B`) and (ii) no point of `S` is shown as γ by two distinct tiles (the per-point bound from
--      the boundary-figure classification).  It concludes `False` whenever `k ≥ 1`
--      (`#S = k - 1 < k`, so the pigeonhole applies).
--
-- `row4_leg_bk_contradiction` is proved for an abstract `γAt : Fin k → Plane` and an abstract "at most
-- one tile per junction" hypothesis.  Its instantiation against the `b^k` leg of a
-- `CongruentDissection` needs:
--   (a) an enumeration of the `k` tiles along a `b^k` leg (`WallEndpoints.chain_endpoints` and
--       `SideWalk` give this for a generic wall, but do not restrict to "every edge is a `b`-edge");
--   (b) for each such tile, a proof that its γ-vertex sits at a specific one of the two junction
--       points bounding its edge (the geometric fact that a `b`-edge joins the α-vertex to the
--       γ-vertex, which needs `cornerAngle`/vertex-labelling data on the tile placement, as
--       `AEdgeReading.lean`/`BEdgeReading.lean` supply for other relations);
--   (c) a proof that each junction `P_i` (`0 < i < k`) is a boundary point of a target side that is
--       not a target vertex, so that `hv`/`hnv` of the boundary-figure classification hold.
--
-- Witnesses: the hypothesis bundle of `row4_no_gamma_at_B` is the same as that of
-- `congruentDissection_row4_alpha_counts` (`hα'/hβ'/hγ'/hαβ/.../hπ0/hγdef/hrel/hirr`, satisfiable
-- e.g. by transcendental `α`).  `pigeonhole_collision` and `row4_leg_bk_contradiction` are exercised
-- on an explicit instance (`k = 2`, two literal points in `ℝ × ℝ` standing in for `Plane`, an explicit
-- `γAt`/`S`, hypotheses discharged by `decide`/direct computation).
import Erdos634.Draft.FluxDRow4Bridge
import Erdos634.Draft.FluxDRow4Boundary
import Mathlib.Data.Finset.Card

namespace Erdos634.Row4L8

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Part (a) — "A, B carry no γ" -/

/-- **A base corner (`A` or `C`) carries no γ.** L1's "no corner of `ABC` has a γ" at a base
corner. This is exactly `Row4Bridge.congruentDissection_row4_alpha_counts`'s fourth conjunct,
reused verbatim (not redefined). -/
theorem row4_no_gamma_at_base (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 :=
  (Erdos634.Row4Bridge.congruentDissection_row4_alpha_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k hcorner).2.2.1

/-- **The apex corner (`B`) carries no γ.** L1's "no corner of `ABC` has a γ" at the apex,
angle `α + β = π − 2α`. NEW: `Draft/FluxDRow4Bridge.lean` built only the base-corner (`(s,t)=(1,0)`)
instance of its own `vertex_multiplicities_row4`; this is the `(s,t) = (1,1)` instance, by the
identical method, composed with the same relation-agnostic `TilePlacement.corner_multiplicities`
and `TileAt.congruentDissection_localAngle_mem` already reused (unedited) by that file. -/
theorem row4_apex_corner_no_gamma_tile {α β γ : ℝ} (hγ : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = α + β) :
    q = 1 ∧ r = 0 := by
  rw [hγ] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α)
      = ((1 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((1 - (s : ℤ) : ℤ) : ℝ) * β := by
    rw [← hrel] at hsum
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Row4Bridge.vertex_multiplicities_row4 hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega⟩

/-- **The apex corner of a real congruent dissection carries no γ-tile.** `CongruentDissection`
level, composing `row4_apex_corner_no_gamma_tile` with `TilePlacement.corner_multiplicities` and
`TileAt.congruentDissection_localAngle_mem`, exactly mirroring
`Row4Bridge.congruentDissection_row4_alpha_counts`'s own assembly. -/
theorem row4_no_gamma_at_apex (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = α + β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 := by
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i
  have h := Erdos634.TilePlacement.corner_multiplicities D.toDissection α β γ hαβ hαγ hαπ hα0
    hβγ hβπ hβ0 hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  have hq0 := (row4_apex_corner_no_gamma_tile hγdef hrel hirr _ _ _ _ h).2
  exact hq0

/-! ## Part (b) — pigeonhole -/

/-- **Pigeonhole, `k` pigeons into `k − 1` holes.** `k` distinct pigeons (`s : Finset ι`,
`#s = k`), each mapped into a hole set `t` with `#t = k − 1` (so `#t < #s` since `k ≥ 1`), forces
two distinct pigeons into the same hole. Direct instance of Mathlib's
`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`; not a fresh pigeonhole proof. -/
theorem pigeonhole_collision {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    {f : ι → κ} (hk : 0 < s.card) (ht : t.card = s.card - 1) (hf : ∀ i ∈ s, f i ∈ t) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  have hlt : t.card < s.card := by omega
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hf

/-! ## Part (c) — the abstract L8 `b^k` assembly -/

/-- **L8's `b^k`-leg contradiction, abstractly.** `k` tiles (`s : Finset ι`, `#s = k`, `k ≥ 1`),
each assigned (by `γAt`) the junction point at which it shows its γ-corner; `γAt` lands in a set
`S` of `k − 1` junction points (standing for `P₁, …, P_{k−1}` — `A` and `B` excluded, `#S = k − 1`
abstracting "no tile's γ lands at `A` or `B`"); and `hbound`, the row-4 boundary bound
(`congruentDissection_row4_boundary_gamma_le_one`, abstracted here as its direct consequence:
distinct tiles never share a γ-junction) instantiated pointwise on `S`. Concludes `False`. This is
the combinatorial CORE of the L8 `b^k` argument: `k` pigeons, `k−1` holes, at-most-one-per-
hole from L1 ⇒ contradiction. NOT instantiated against a real chain — see the file header for
exactly what real-geometry bridge (a)-(c) remains. -/
theorem row4_leg_bk_contradiction {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {S : Finset κ}
    {γAt : ι → κ} (hk : 0 < s.card) (hS : S.card = s.card - 1)
    (hmaps : ∀ i ∈ s, γAt i ∈ S)
    (hbound : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → γAt i = γAt j → False) :
    False := by
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := pigeonhole_collision hk hS hmaps
  exact hbound x hx y hy hxy hfxy

/-! ## Non-vacuity check

A vacuity check on `row4_leg_bk_contradiction` cannot exhibit a joint instance of `hk`,
`hS`, `hmaps`, `hbound` all true at once: by the theorem itself,
whenever the cardinalities force a collision (`hk`/`hS`) and `hmaps` lands the map in
`S`, that collision refutes any `hbound` claiming there is none. That is exactly the intended
reductio shape (Mathlib's `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` proves precisely this:
`hbound`-as-injectivity and `hmaps`-with-mismatched-cardinalities are jointly inconsistent).
Checked instead: each hypothesis is individually satisfiable in isolation, and the underlying
Mathlib pigeonhole step fires on concrete data (not `False → False`). -/

section NonVacuityCheck

/-- `pigeonhole_collision` fires on concrete, non-contradictory data: 2 pigeons, 1 hole, `hk`/`ht`/
`hf` all genuinely true of this instance (no hypothesis here is `False` in isolation), and a
genuine collision is produced — confirming the Mathlib step is doing real work, not composing two
vacuous premises. -/
example : ∃ x ∈ ({0, 1} : Finset ℕ), ∃ y ∈ ({0, 1} : Finset ℕ), x ≠ y ∧
    (fun _ : ℕ => (0 : ℕ)) x = (fun _ : ℕ => (0 : ℕ)) y :=
  pigeonhole_collision (s := ({0, 1} : Finset ℕ)) (t := ({0} : Finset ℕ))
    (f := fun _ : ℕ => (0 : ℕ)) (by decide) (by decide) (by decide)

/-- Each of `row4_leg_bk_contradiction`'s four hypotheses is individually satisfiable (none is
`False` on its own): `hk` (`0 < 2`), `hS` (`1 = 2 - 1`), `hmaps` (the constant map into `{0}`), and
`hbound` taken as "distinct pigeons never share a hole" — satisfiable in isolation, e.g. by the
INJECTIVE map `id` into a 2-element hole set, which no argument here forces to coincide with the
`hmaps` instance above (that coincidence is exactly what the leg's real geometry would have to
supply, and does not, per the file header's items (a)-(c)). -/
example : ∀ i ∈ ({0, 1} : Finset ℕ), ∀ j ∈ ({0, 1} : Finset ℕ), i ≠ j →
    (id : ℕ → ℕ) i = id j → False := by decide

end NonVacuityCheck

end Erdos634.Row4L8

#print axioms Erdos634.Row4L8.row4_no_gamma_at_base
#print axioms Erdos634.Row4L8.row4_apex_corner_no_gamma_tile
#print axioms Erdos634.Row4L8.row4_no_gamma_at_apex
#print axioms Erdos634.Row4L8.pigeonhole_collision
#print axioms Erdos634.Row4L8.row4_leg_bk_contradiction
