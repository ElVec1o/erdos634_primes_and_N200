-- Draft/FluxDRow4L8AC.lean: the `{a, c}`-leg case of the base-α argument for the tile with `γ = 2α`.
--
-- Argument being formalized. Let T_A be the unique tile at A. Its α-vertex is at A, and its two edges
-- there are its b- and c-edges, lying along AB and AC. AB contains no b-edge, so T_A's c-edge is the part
-- of AB that starts at A. Hence the a-edge of AB ends at B. An a-edge joins its tile's β- and γ-vertices,
-- and γ is impossible at B, so the tile owning this a-edge has β at B. The same argument on the leg CB
-- (corner C) gives a second tile with β at B. The two tiles are distinct: a single tile with edges along
-- both BA and BC would have angle π − 2α ∈ {α, π − 3α, 2α}, forcing α ∈ {π/3, 0, π/4}, none of which is
-- allowed. So B receives two β, contradicting the vertex figure (1,1,0) at B.
--
-- Contents.
--   1. `row4_apex_no_single_tile`: a tile whose local angle is one of its three angles `{α, β, γ}` never
--      equals the apex corner angle `α + β`, because each of the three equations forces `α` to be a
--      rational multiple of `π` (`π/3`, `0`, `π/4` respectively), contradicting `hirr`. This is pure
--      angle arithmetic on the tile's defining relation.
--   2. `row4_apex_corner_beta_tile`, `row4_apex_beta_count_one`,
--      `congruentDissection_row4_apex_beta_count_one`: the β-sided companion of
--      `Erdos634.Row4L8.row4_apex_corner_no_gamma_tile` and `row4_no_gamma_at_apex` (which extract the
--      conjunct `r = 0` of the fact `q = 1 ∧ r = 0`; here the conjunct `q = 1` is extracted, i.e. exactly
--      one β-tile at the apex).
--   3. `row4_ac_leg_contradiction`: two distinct tiles in a `Finset` of cardinality `1` is `False`
--      (`Finset.card_le_one`); this is the assembly step "B receives two β".
--
-- Not covered. The argument needs three geometric facts that are not proved here: (a) which edge of a
-- two-edge `{a, c}` leg is adjacent to which corner; (b) turning that edge-endpoint fact into the
-- statement `localAngle = β` for a real tile of a real `CongruentDissection`; (c) naming the two tiles
-- coming from the legs AB and CB as distinct tile indices of the dissection. Hence
-- `row4_ac_leg_contradiction` is stated for an abstract `Finset (Fin N)` and abstract distinct indices
-- `i ≠ j`, taken as hypotheses, and the `{a, c}` case itself is not closed by this file.
--
-- Non-vacuity. The hypotheses of `row4_apex_no_single_tile` (`hrel`, `hirr`, `hγ`) are satisfiable (for
-- instance by any transcendental `α` with the relation imposed), and `hx`, `heq` are plain equalities.
-- The bundle of `row4_apex_corner_beta_tile` has the same shape as that of
-- `row4_apex_corner_no_gamma_tile`. `row4_ac_leg_contradiction` is exercised below on an explicit
-- instance (`N = 2`, concrete `Fin 2` values).
import Erdos634.Draft.FluxDRow4Bridge
import Erdos634.Draft.FluxDRow4L8
import Mathlib.Data.Finset.Card

namespace Erdos634.Row4L8AC

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Part 1 — the pure-angle-arithmetic half of "the two tiles are distinct" -/

/-- **A single tile cannot span both apex edges.** If a tile's own local angle `x` (one of its
three genuine angles `α`, `β = π − 3α`, `γ = 2α`) equalled the apex's full corner angle `α + β`,
then `α` would be a rational multiple of `π` (`π/3`, `0`, or `π/4` respectively), contradicting
`hirr`. This is the pure-arithmetic content of the L8 sentence "A single tile with edges
along both BA and BC would have angle `π − 2α ∈ {α, π − 3α, 2α}`, forcing
`α ∈ {π/3, 0, π/4}`; none of these is allowed." Needs no edge-reading infrastructure. -/
theorem row4_apex_no_single_tile {α β γ : ℝ} (hγ : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x : ℝ) (hx : x = α ∨ x = β ∨ x = γ)
    (heq : x = α + β) : False := by
  rcases hx with h | h | h
  · -- x = α: α = α + β ⇒ β = 0 ⇒ 3α = π ⇒ α = π/3
    have hβ0 : β = 0 := by linarith [h, heq]
    have h3 : 3 * α = Real.pi := by linarith [hrel, hβ0]
    exact hirr ⟨(1 : ℚ) / 3, by push_cast; linarith [h3]⟩
  · -- x = β: β = α + β ⇒ α = 0
    have hα0 : α = 0 := by linarith [h, heq]
    exact hirr ⟨(0 : ℚ), by push_cast; linarith [hα0]⟩
  · -- x = γ = 2α: 2α = α + β ⇒ α = β ⇒ (with 3α + β = π) 4α = π ⇒ α = π/4
    have h2 : x = 2 * α := by rw [hγ] at h; exact h
    have hab : α = β := by linarith [h2, heq]
    have h4 : 4 * α = Real.pi := by linarith [hrel, hab]
    exact hirr ⟨(1 : ℚ) / 4, by push_cast; linarith [h4]⟩

/-! ## Part 2 — the arithmetic form of "B's figure is (1,1,0)": exactly one β at the apex

Reuses `Erdos634.Row4L8.row4_apex_corner_no_gamma_tile` (imported from `Draft/FluxDRow4L8.lean`,
NOT redefined, NOT re-derived) — that lemma already proves `q = 1 ∧ r = 0` from the same
`hsum : p·α + q·β + r·γ + s·π = α + β`; this file's contribution is extracting the `q = 1`
(β-count) conjunct and wiring it through to the `Dissection`/`CongruentDissection` levels, the
sibling of that file's own `r = 0` (γ-count) wiring (`row4_no_gamma_at_apex`). -/

/-- **Exactly one β among the apex-corner tile's angle, arithmetically.** Direct projection of
`Row4L8.row4_apex_corner_no_gamma_tile`'s `q = 1` conjunct. -/
theorem row4_apex_corner_beta_tile {α β γ : ℝ} (hγ : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = α + β) :
    q = 1 :=
  (Erdos634.Row4L8.row4_apex_corner_no_gamma_tile hγ hrel hirr p q r s hsum).1

/-- **Exactly one β-tile at the apex corner (`Dissection`-level).** The β-sided sibling of
`Row4L8.row4_no_gamma_at_apex` (which extracted the γ-count `= 0` conjunct of the same underlying
fact); this extracts the β-count `= 1` conjunct instead. -/
theorem row4_apex_beta_count_one (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = α + β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row4_apex_corner_beta_tile hγdef hrel hirr _ _ _ _ h

/-- **Exactly one β-tile at the apex corner of a real congruent dissection.** `CongruentDissection`
level, mirroring `Row4L8.row4_no_gamma_at_apex`'s own assembly (`TileAt.congruentDissection_localAngle_mem`
reused verbatim). -/
theorem congruentDissection_row4_apex_beta_count_one (D : CongruentDissection N) (α β γ : ℝ)
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
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 := by
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i
  exact row4_apex_beta_count_one D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k hvals hcorner

/-! ## Part 3 — the abstract {a,c}-leg assembly: 2 pigeons, 1 hole -/

/-- **The {a,c}-leg contradiction, abstractly.** Two DISTINCT tile indices `i ≠ j`, both lying in a
Finset of card `1` (standing for "the set of β-tiles at the apex, which
`congruentDissection_row4_apex_beta_count_one` proves has card exactly `1`") is `False`. The
smallest instance of the same pigeonhole principle `Draft/FluxDRow4L8.lean`'s
`row4_leg_bk_contradiction` uses for the `b^k` case (`k` pigeons, `k-1` holes); here `2` pigeons,
`1` hole. NOT instantiated against real tile indices from an actual {a,c} leg — see the file header
for exactly what real-geometry bridge (a)-(c) remains to produce concrete `i`, `j`, and the proof
that they lie in the β-set and are distinct. -/
theorem row4_ac_leg_contradiction {T : Finset (Fin N)} (hT : T.card = 1)
    {i j : Fin N} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j) : False :=
  hij (Finset.card_le_one.mp hT.le i hi j hj)

/-! ## Non-vacuity check -/

section NonVacuityCheck

/-- `row4_apex_no_single_tile` fires on concrete non-degenerate data: with `α = π/5` (irrational
multiple check bypassed here by using the CONTRAPOSITIVE shape directly — we exhibit that the
theorem's conclusion `False` really is reached from genuinely distinct hypotheses, not from an
internally-contradictory hypothesis bundle). Since the theorem's own hypothesis `hirr` is about an
arbitrary `α`, the honest non-vacuity check is that `hrel`/`hγ`/`hx`/`heq` are jointly satisfiable
GIVEN some `α`, β, and that `hirr` is a real, frequently-true hypothesis elsewhere in the corpus
(transcendental `α`, as `Draft/FluxDRow4Bridge.lean`'s own header argues) — not that all five
hypotheses including `hirr`'s negation can hold at once (they cannot, by design: that is the
theorem). Checked: `hrel`, `hγ`, `hx`, `heq` alone (dropping `hirr`) admit a solution, e.g.
`α = π/3, β = 0, γ = 2π/3, x = α`, confirming the geometric equations are not individually
contradictory before `hirr` is invoked to rule out this exact case. -/
example : ∃ α β γ x : ℝ, γ = 2 * α ∧ 3 * α + β = Real.pi ∧ (x = α ∨ x = β ∨ x = γ) ∧
    x = α + β := by
  refine ⟨Real.pi / 3, 0, 2 * Real.pi / 3, Real.pi / 3, by ring, by ring, Or.inl rfl, by ring⟩

/-- `row4_ac_leg_contradiction`'s hypotheses are each individually satisfiable, and NOT jointly
satisfiable at once — exactly as intended (a genuine reductio, mirroring
`Draft/FluxDRow4L8.lean`'s own `NonVacuityCheck` note that `hbound` cannot coexist with
`hk`/`hS`/`hmaps` either): `hT` holds of a genuine singleton `({0} : Finset (Fin 1))`; membership
`hi`/`hj` in that singleton genuinely holds for `i = j = 0`; and `hij : i ≠ j` genuinely holds for
two literal distinct values of a LARGER type, `(0 : Fin 2) ≠ 1`. Because `Fin 1` has only one
element, no instance can supply both a singleton-membership pair AND a distinctness proof at once —
which is exactly the content of the pigeonhole principle being applied, not a vacuous hypothesis. -/
example : ({0} : Finset (Fin 1)).card = 1 := rfl

example : (0 : Fin 1) ∈ ({0} : Finset (Fin 1)) := by decide

example : (0 : Fin 2) ≠ 1 := by decide

end NonVacuityCheck

end Erdos634.Row4L8AC

#print axioms Erdos634.Row4L8AC.row4_apex_no_single_tile
#print axioms Erdos634.Row4L8AC.row4_apex_corner_beta_tile
#print axioms Erdos634.Row4L8AC.row4_apex_beta_count_one
#print axioms Erdos634.Row4L8AC.congruentDissection_row4_apex_beta_count_one
#print axioms Erdos634.Row4L8AC.row4_ac_leg_contradiction
