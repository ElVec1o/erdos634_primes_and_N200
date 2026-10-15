/-
Draft/ChordCut.lean  In `AllThreshold`.

Restriction of a congruent dissection to the tiles on one side of a line that no tile crosses (the lemma "R" of the
survey for `prop:reframe` (b), (c)): the library had `SubDissection.restrictCongruent` with the covering equality as a
hypothesis, and `ChordTraceReal.straddlers`, but nothing connecting the two.

    theorem restrict_below    -- `straddlers D g c = ∅`, `T'.carrier = D.target.carrier ∩ {g ≤ c}`  ⟹  a congruent
                              --   dissection `D'` of `T'` with the model of `D` (its tiles are the tiles of `D` on that side)
    theorem restrict_above    -- the same for `{c ≤ g}` (apply the above to `-g`, `-c`; `straddlers D (-g) (-c) = straddlers D g c`)
    theorem straddlers_eq_empty_of_wall
                              -- a chord `[P, Q]` of the target on the line `{g = c}` whose open segment meets no tile
                              --   interior is crossed by no tile
    theorem straddlers_neg, not_straddles_of_empty, midpoint_mem_openSegment    -- the small lemmas

Proof of `restrict_below` (as planned): by `Tri.sign_trichotomy` and `straddlers = ∅` a tile containing a point with
`g < c` has `g ≤ c` on all of it; the set `S` of such tiles has a closed union `U` (finite union of compact tiles);
`interior T' ⊆ {g < c}` (else `interior_on_line_straddles` makes `T'` straddle its own line, but all its vertices have
`g ≤ c`), and a point of `interior T'` lies in some tile of the cover of the target, hence in `U`; a `Tri` is the closure of
its interior (`Convex.closure_interior_eq_closure_of_nonempty_interior`, `Tri.interior_nonempty`, compactness), so
`T' ⊆ closure (interior T') ⊆ U`; the other inclusion is containment of each tile of `S` in the target and in `{g ≤ c}`.

Hypotheses of `straddlers_eq_empty_of_wall` (all of them used): `hline` (every point of the target on the line `{g = c}` lies
on `[P, Q]`) and `hwall` (no point of the open segment is interior to a tile).  NOT needed, and not assumed: `P ≠ Q`, that the
open segment is interior to the target, `g ≠ 0`, `g P = c`, `g Q = c` (a straddler contributes two distinct points of the
target on the line, which `hline` puts on `[P, Q]`, and the midpoint of two distinct points of `[P, Q]` is in the open
segment).

Non-vacuity: the witnesses are in `Draft/ChordCutWitness.lean` (the median wall of `TPErdos.wallCongruentDissection`).
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.SubDissection
import Erdos634.ChordStraddleTotal
import Erdos634.ChordEndpointsDistinct
import Erdos634.ChordInteriorStraddle

open scoped Classical
set_option linter.unusedVariables false
open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.Draft.ChordCut

/-- `straddlers = ∅` says that no tile has vertices strictly on both sides. -/
theorem not_straddles_of_empty {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (h0 : straddlers D g c = ∅) (i : Fin N) :
    ¬ ((∃ a, g ((D.tile i).pts a) < c) ∧ (∃ b, c < g ((D.tile i).pts b))) := by
  intro h
  have hi : i ∈ straddlers D g c := by
    simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  rw [h0] at hi
  simp at hi

/-- the set of straddlers of the line `{-g = -c}` is the set of straddlers of `{g = c}` -/
theorem straddlers_neg {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    straddlers D (-g) (-c) = straddlers D g c := by
  ext i
  simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.neg_apply,
    neg_lt_neg_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩

/-- **Restriction to the side `{g ≤ c}` of a line that no tile crosses.**  If `T'` is a triangle whose carrier is the
part of the target on the side `{g ≤ c}`, the tiles of `D` lying in `{g ≤ c}` form a congruent dissection of `T'` with the
same model. -/
theorem restrict_below {N : ℕ} (D : CongruentDissection N) (g : Plane →ₗ[ℝ] ℝ) (hg : g ≠ 0) (c : ℝ)
    (h0 : straddlers D.toDissection g c = ∅) (T' : Erdos634.Geometry.Tri)
    (hT' : T'.carrier = D.target.carrier ∩ {y | g y ≤ c}) :
    ∃ (N' : ℕ) (D' : CongruentDissection N'), D'.target = T' ∧ D'.model = D.model := by
  obtain ⟨S, hmemS⟩ : ∃ S : Finset (Fin N), ∀ i, i ∈ S ↔ ∀ x ∈ (D.tile i).carrier, g x ≤ c :=
    ⟨Finset.univ.filter (fun i => ∀ x ∈ (D.tile i).carrier, g x ≤ c), fun i => by simp⟩
  have hUclosed : IsClosed (⋃ i ∈ S, (D.tile i).carrier) :=
    isClosed_biUnion_finset (fun i _ => (D.tile i).isCompact.isClosed)
  have hbelow : ∀ i x, x ∈ (D.tile i).carrier → g x < c → i ∈ S := by
    intro i x hx hgx
    rcases Erdos634.ChordTraceReal.Tri.sign_trichotomy (D.tile i) g c with h | h | h
    · exact (hmemS i).mpr h
    · exact absurd (h x hx) (not_le.mpr hgx)
    · exact absurd h (not_straddles_of_empty D.toDissection g c h0 i)
  have hlt : ∀ y ∈ interior T'.carrier, g y < c := by
    intro y hy
    have hy' : y ∈ T'.carrier := interior_subset hy
    have hle : g y ≤ c := by
      rw [hT'] at hy'
      exact hy'.2
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hv : ∀ j, g (T'.pts j) ≤ c := by
        intro j
        have hj : T'.pts j ∈ T'.carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
        rw [hT'] at hj
        exact hj.2
      obtain ⟨_, ⟨i, hi⟩⟩ := interior_on_line_straddles T' g hg c hy h
      exact absurd (hv i) (not_le.mpr hi)
  have hint_sub : interior T'.carrier ⊆ ⋃ i ∈ S, (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ T'.carrier := interior_subset hy
    have hyt : y ∈ D.target.carrier := by
      rw [hT'] at hy'
      exact hy'.1
    rw [← D.covers] at hyt
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyt
    exact Set.mem_iUnion₂.mpr ⟨i, hbelow i y hi (hlt y hy), hi⟩
  have hcl : T'.carrier ⊆ closure (interior T'.carrier) := by
    have h := T'.convex.closure_interior_eq_closure_of_nonempty_interior T'.interior_nonempty
    rw [h, T'.isCompact.isClosed.closure_eq]
  have hcov : (⋃ i ∈ S, (D.tile i).carrier) = T'.carrier := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hx
      rw [hT']
      exact ⟨tile_subset_target D.toDissection i hxi, (hmemS i).mp hiS x hxi⟩
    · intro x hx
      exact hUclosed.closure_subset_iff.mpr hint_sub (hcl hx)
  exact ⟨S.card, Erdos634.SubDissection.restrictCongruent D S T' hcov, rfl, rfl⟩

/-- **Restriction to the side `{c ≤ g}`** (the mirror of `restrict_below`). -/
theorem restrict_above {N : ℕ} (D : CongruentDissection N) (g : Plane →ₗ[ℝ] ℝ) (hg : g ≠ 0) (c : ℝ)
    (h0 : straddlers D.toDissection g c = ∅) (T' : Erdos634.Geometry.Tri)
    (hT' : T'.carrier = D.target.carrier ∩ {y | c ≤ g y}) :
    ∃ (N' : ℕ) (D' : CongruentDissection N'), D'.target = T' ∧ D'.model = D.model := by
  refine restrict_below D (-g) (neg_ne_zero.mpr hg) (-c) ?_ T' ?_
  · rw [straddlers_neg]
    exact h0
  · rw [hT']
    ext y
    simp

/-- the midpoint of two distinct points of a segment is in its open segment -/
theorem midpoint_mem_openSegment {P Q p q : Plane} (hp : p ∈ segment ℝ P Q) (hq : q ∈ segment ℝ P Q)
    (hpq : p ≠ q) : midpoint ℝ p q ∈ openSegment ℝ P Q := by
  rw [segment_eq_image_lineMap] at hp hq
  rw [openSegment_eq_image_lineMap]
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hst : s ≠ t := fun h => hpq (by rw [h])
  refine ⟨(s + t) / 2, ⟨?_, ?_⟩, ?_⟩
  · rcases lt_or_gt_of_ne hst with h | h <;> linarith [hs.1, ht.1]
  · rcases lt_or_gt_of_ne hst with h | h <;> linarith [hs.2, ht.2]
  · simp only [midpoint_eq_smul_add, AffineMap.lineMap_apply_module, invOf_eq_inv]
    module

/-- **A wall gives `straddlers = ∅`.**  If every point of the target on the line `{g = c}` lies on the segment `[P, Q]`
(the chord) and no point of the open segment `(P, Q)` is interior to a tile, then no tile crosses the line. -/
theorem straddlers_eq_empty_of_wall {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hline : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ P Q)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) :
    straddlers D g c = ∅ := by
  by_contra hne
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hi
  obtain ⟨p, q, hp, hq, hpq⟩ := straddle_two_distinct_points (D.tile i) g c ha hb
  have hm := Erdos634.ChordTraceReal.Tri.straddle_midpoint_interior (D.tile i) g c ⟨a, ha⟩ ⟨b, hb⟩
    hp.1 hp.2 hq.1 hq.2 hpq
  have hpP := hline p (tile_subset_target D i hp.1) hp.2
  have hqP := hline q (tile_subset_target D i hq.1) hq.2
  exact hwall _ (midpoint_mem_openSegment hpP hqP hpq) i hm

end Erdos634.Draft.ChordCut

#print axioms Erdos634.Draft.ChordCut.straddlers_neg
#print axioms Erdos634.Draft.ChordCut.restrict_below
#print axioms Erdos634.Draft.ChordCut.restrict_above
#print axioms Erdos634.Draft.ChordCut.midpoint_mem_openSegment
#print axioms Erdos634.Draft.ChordCut.straddlers_eq_empty_of_wall
