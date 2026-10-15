/-
The tile across the corner `b`-chord, part 1 of 2.  Adapts `GLCReflect`/`GLCG1` (γ = 2α) and `T30LPi3F6*` (π/3) to the
base-β tile.  The architecture and proof skeleton are redone for the base-β tile; the files below are not imported, to
keep the import cone small.

Adapted from:
  Draft/GLCReflect.lean:142-166      corner_chord_reflection_2a, first half (the far chain of the chord is a single edge
                                     `e2`; that edge is the chord (`seg_endpoints`); the far tile lies strictly above the line
                                     (`third_strict`) and differs from the corner tile)  -> corner_chord_partner_data
  Draft/T30LPi3F6.lean:184-210       Pi3F6.corner_chord_reflection (same first half, pi/3)
New here (those files only produce the far tile, they never prove that it is the only
tile with an edge equal to the chord):
  the uniqueness clause ("matched by exactly one tile": a trichotomy on the third vertex of a competing tile, the
  near chain being the corner tile's own edge) -> corner_chord_partner_data (last conjunct), corner_chord_partner
Imported and applied:
  Draft/CornerParaCornerAux.lean     corner_chord_clamps (the packaged clamp data)
  Draft/CornerParaClamp.lean         far_chain_single_b, far_edge_eq_segment, seg_endpoints, third_strict, fin3_cover
  Draft/ChordFar.lean                chord_far_sum, chain_sum_real, far_chain_single_of_length_eq, segment_sub_level
-/
import Erdos634.Draft.CornerParaCornerAux

/-!
# The tile across the corner `b`-chord, and its uniqueness, part 1 of 2

Part 2 is `Draft/CornerParaHalfTurn.lean` (the angle interchange and the half-turn).  Adapts `GLCReflect`/`GLCG1`
(γ = 2α) and `T30LPi3F6*` (π/3) to the base-β tile.

Contents.
* `corner_chord_partner_data`: from a `CornerChord` on a base-β model, there are a line `φ = c0` through the
  chord (`T_A ⊆ {φ ≤ c0}`, `A` strictly below), a tile `i3 ≠ iA` and an edge `k3` of it with
  `(D.tile i3).edge k3 = segment P Q`, whose length is `b`, whose endpoints are `{P, Q}` (in either order), which lies
  in `{φ ≥ c0}` with its third vertex strictly above the line, and **every** tile `i' ≠ iA` with an edge equal to the
  chord is this one (`i' = i3`, `k' = k3`).
* `corner_chord_partner`: "matched by exactly one tile" read as edge equality:
  `∃! i3, i3 ≠ iA ∧ ∃ k3, (D.tile i3).edge k3 = segment ℝ P Q` (the tiling need not be edge-to-edge, so this is not a
  point-uniqueness statement).
* `corner_chord_matching_tiles` (the set of tiles with an edge equal to the chord is exactly `{iA, i3}`: the clause
  `i3 ≠ iA` is needed) and `corner_chord_partner_edge` (the length `b` and the endpoints `{P, Q}` of the edge of
  any tile `i3 ≠ iA` matching the chord).

The proof: the corner chord is clamped by the two target sides, so the whole-edge partition (`chord_far_sum`)
makes the near chain of the chord line `{φ = c0}` the single edge `(iA, eA)` of the corner tile (its length is the
whole chord), and the word lemma `hword_b` (`b` is unsplittable) makes the far chain a single edge `e₀` of length
`b`, which is the chord (`seg_endpoints`).  A competing tile `i' ≠ iA` with an edge equal to the chord has the
chord's endpoints on the line, its third vertex off the line (`third_strict`), hence on the near side (then its edge is
in the near chain `{(iA, eA)}`, so `i' = iA`: excluded) or on the far side (then its edge is in the far chain `{e₀}`).
No identification of the endpoints with `{P, Q}` is needed for uniqueness.

The hypotheses are those of `corner_chord_data` (witnessed at the N = 44 tiling `D44`, `(e, f, s) = (1, 2, 8)`) plus a
`CornerChord`, which `corner_chord_data` produces at the base corners `0, 1` of `D44`.  The instantiation at `D44` is carried by
`Draft/CornerParaWitness` (`D44_corner0_pinned`, `D44_corner1_pinned`, `D44_partner_needs_ne`: the partner is
`tiles[2]` resp. `tiles[14]`).
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.ChordFar

/-! ## 1. The partner tile of the corner chord -/

/-- **The tile across the corner `b`-chord, with everything the half-turn stage needs, and its uniqueness.**
Let `hC : CornerChord D α β γ k iA P Q` (so `[P, Q]` is the `b`-edge of the corner tile `T_A`, clamped by the two
target sides).  Then there are a nonzero functional `φ` and `c0` with `T_A ⊆ {φ ≤ c0}`, `φ P = φ Q = c0`, `φ A < c0`,
and a tile `i3 ≠ iA` with an edge `k3` such that
* `(D.tile i3).edge k3 = segment ℝ P Q` (as sets);
* `dist (pts k3) (pts (k3+1)) = sideOpp D.model 1` (it is a `b`-edge: the far chain of `b` is a single whole edge),
  and its endpoints are `P` and `Q`, in either order;
* `T_3 = D.tile i3 ⊆ {φ ≥ c0}`, with its third vertex `pts (k3+2)` strictly above the line;
* every tile `i' ≠ iA` with an edge `k'` equal to `segment ℝ P Q` is this one: `i' = i3` and `k' = k3`. -/
theorem corner_chord_partner_data {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    ∃ (φ : Plane →ₗ[ℝ] ℝ) (c0 : ℝ) (i3 : Fin N) (k3 : Fin 3),
      φ ≠ 0 ∧ (∀ x ∈ (D.tile iA).carrier, φ x ≤ c0) ∧ φ P = c0 ∧ φ Q = c0 ∧
      φ (D.target.pts k) < c0 ∧
      i3 ≠ iA ∧ (D.tile i3).edge k3 = segment ℝ P Q ∧
      dist ((D.tile i3).pts k3) ((D.tile i3).pts (k3 + 1)) = sideOpp D.model 1 ∧
      (((D.tile i3).pts k3 = P ∧ (D.tile i3).pts (k3 + 1) = Q) ∨
        ((D.tile i3).pts k3 = Q ∧ (D.tile i3).pts (k3 + 1) = P)) ∧
      (∀ x ∈ (D.tile i3).carrier, c0 ≤ φ x) ∧ c0 < φ ((D.tile i3).pts (k3 + 2)) ∧
      ∀ (i' : Fin N) (k' : Fin 3), i' ≠ iA → (D.tile i').edge k' = segment ℝ P Q →
        i' = i3 ∧ k' = k3 := by
  obtain ⟨hPQ, φ, c0, eA, g, cg, h, ch, hφ, hle, hφP, hφQ, hφA, hedge, hmem, hlen, hg, hgP, hgQ, hh, hhQ, hhP,
    hint, hwall⟩ := corner_chord_clamps hC
  -- the NEAR chain of the chord line is the single edge `(iA, eA)` of the corner tile
  have hnear : D.lineChain φ c0 = {(iA, eA)} := by
    have h1 := (chord_far_sum D.toDissection φ hφ c0 hPQ hφP hφQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall).1
    have h2 := chain_sum_real D.toDissection _ _ dist_nonneg h1
    exact far_chain_single_of_length_eq D.toDissection _ _ h2 hmem hlen
  -- the FAR chain is a single edge `e₀` of length `b`, and it is the chord
  obtain ⟨e₀, he₀, hfar, hlen₀⟩ := far_chain_single_b hM hco he hef φ hφ c0 hPQ hφP hφQ g cg hg hgP hgQ h ch hh
    hhQ hhP hint hwall hC.lenPQ
  have hedge₀ : (D.tile e₀.1).edge e₀.2 = segment ℝ P Q :=
    far_edge_eq_segment D.toDissection φ hφ c0 hPQ hφP hφQ g cg hg hgP hgQ h ch hh hhQ hhP he₀
      (hlen₀.trans hC.lenPQ.symm)
  obtain ⟨hf2P, hf2Q, hle2⟩ := Dissection.mem_lineChain.mp he₀
  -- the far tile is not the corner tile: `A` is a vertex of `T_A` with `φ A < c0`
  have hne₀ : e₀.1 ≠ iA := by
    intro hi
    obtain ⟨j, hjA, -⟩ := hC.vertex
    have h1 := hle2 j
    rw [hi, ← hjA] at h1
    simp only [LinearMap.neg_apply] at h1
    linarith
  -- its endpoints are `P` and `Q`
  have hend : ((D.tile e₀.1).pts e₀.2 = P ∧ (D.tile e₀.1).pts (e₀.2 + 1) = Q) ∨
      ((D.tile e₀.1).pts e₀.2 = Q ∧ (D.tile e₀.1).pts (e₀.2 + 1) = P) := by
    have hX : (D.tile e₀.1).pts e₀.2 ∈ segment ℝ P Q := by
      rw [← hedge₀]; exact left_mem_segment ℝ _ _
    have hY : (D.tile e₀.1).pts (e₀.2 + 1) ∈ segment ℝ P Q := by
      rw [← hedge₀]; exact right_mem_segment ℝ _ _
    exact seg_endpoints hPQ hX hY (hlen₀.trans hC.lenPQ.symm)
  -- its third vertex is strictly above the line
  have hthird : c0 < φ ((D.tile e₀.1).pts (e₀.2 + 2)) := by
    have := third_strict (D.tile e₀.1) (-φ) (neg_ne_zero.mpr hφ) (-c0) hle2 e₀.2 hf2P hf2Q
    simp only [LinearMap.neg_apply] at this
    linarith
  refine ⟨φ, c0, e₀.1, e₀.2, hφ, hle, hφP, hφQ, hφA, hne₀, hedge₀, hlen₀, hend, ?_, hthird, ?_⟩
  · intro x hx
    have := Tri.carrier_subset_halfplane (D.tile e₀.1) (-φ) (-c0) hle2 x hx
    simp only [LinearMap.neg_apply] at this
    linarith
  · -- UNIQUENESS: a competitor's edge is in the near chain (impossible) or in the far chain `{e₀}`
    intro i' k' hne' hk'
    have hsub := segment_sub_level φ c0 hφP hφQ
    have hX : φ ((D.tile i').pts k') = c0 := by
      have : (D.tile i').pts k' ∈ segment ℝ P Q := by
        rw [← hk']; exact left_mem_segment ℝ _ _
      exact hsub this
    have hY : φ ((D.tile i').pts (k' + 1)) = c0 := by
      have : (D.tile i').pts (k' + 1) ∈ segment ℝ P Q := by
        rw [← hk']; exact right_mem_segment ℝ _ _
      exact hsub this
    rcases lt_trichotomy (φ ((D.tile i').pts (k' + 2))) c0 with hlt | heq | hgt
    · -- near side: the whole tile is in `{φ ≤ c0}`, so its edge is in the near chain `{(iA, eA)}`
      exfalso
      have hle' : ∀ i, φ ((D.tile i').pts i) ≤ c0 := by
        intro i
        rcases fin3_cover k' i with rfl | rfl | rfl
        · exact hX.le
        · exact hY.le
        · exact hlt.le
      have hmem' : (i', k') ∈ D.lineChain φ c0 := Dissection.mem_lineChain.mpr ⟨hX, hY, hle'⟩
      rw [hnear] at hmem'
      exact hne' (congrArg Prod.fst (Finset.mem_singleton.mp hmem'))
    · -- the third vertex cannot lie on the line
      exfalso
      have hle' : ∀ i, φ ((D.tile i').pts i) ≤ c0 := by
        intro i
        rcases fin3_cover k' i with rfl | rfl | rfl
        · exact hX.le
        · exact hY.le
        · exact heq.le
      have := third_strict (D.tile i') φ hφ c0 hle' k' hX hY
      linarith
    · -- far side: the whole tile is in `{φ ≥ c0}`, so its edge is in the far chain `{e₀}`
      have hle' : ∀ i, (-φ) ((D.tile i').pts i) ≤ -c0 := by
        intro i
        simp only [LinearMap.neg_apply, neg_le_neg_iff]
        rcases fin3_cover k' i with rfl | rfl | rfl
        · exact hX.ge
        · exact hY.ge
        · exact hgt.le
      have hmem' : (i', k') ∈ D.lineChain (-φ) (-c0) :=
        Dissection.mem_lineChain.mpr ⟨by simp [hX], by simp [hY], hle'⟩
      rw [hfar] at hmem'
      have hp := Finset.mem_singleton.mp hmem'
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- **`prop:cornerpara`, "the tile across the corner tile's `b`-edge": matched by exactly one tile** (plan §2.3).
For the corner chord `[P, Q]` (the `b`-edge of the corner tile `T_A`) there is exactly one tile `i3 ≠ iA` having an edge
equal, as a set, to `segment ℝ P Q`.  (EDGE equality, not point-uniqueness: the tiling need not be edge-to-edge.) -/
theorem corner_chord_partner {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    ∃! i3 : Fin N, i3 ≠ iA ∧ ∃ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q := by
  obtain ⟨φ, c0, i3, k3, -, -, -, -, -, hne, hedge, -, -, -, -, huniq⟩ :=
    corner_chord_partner_data hM hco he hef hC
  exact ⟨i3, ⟨hne, k3, hedge⟩, fun i' ⟨hne', k', hk'⟩ => (huniq i' k' hne' hk').1⟩

/-- **Exactly two tiles have an edge equal to the corner chord: `T_A` and its partner** (the chord is a chord, not a
boundary edge: it is matched on both sides, and by nothing else).  This also records that the clause `i3 ≠ iA` of
`corner_chord_partner` is load-bearing: the corner tile `T_A` itself has an edge equal to `segment ℝ P Q`
(`CornerChord.chordEdge`), so "matched by exactly one tile" can only mean one tile OTHER than `T_A`. -/
theorem corner_chord_matching_tiles {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    ∃ i3 : Fin N, i3 ≠ iA ∧
      {i : Fin N | ∃ k' : Fin 3, (D.tile i).edge k' = segment ℝ P Q} = {iA, i3} := by
  obtain ⟨i3, ⟨hne, k3, h3⟩, huniq⟩ := corner_chord_partner hM hco he hef hC
  refine ⟨i3, hne, ?_⟩
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k', hk'⟩
    by_cases hi : i = iA
    · exact Or.inl hi
    · exact Or.inr (huniq i ⟨hi, k', hk'⟩)
  · rintro (rfl | rfl)
    · exact hC.chordEdge
    · exact ⟨k3, h3⟩

/-- **The partner is a `b`-edge tile with endpoints `{P, Q}`** (plan §2.3, "export `dist` of that edge `= sideOpp D.model 1`"):
for ANY tile `i3 ≠ iA` having an edge `k3` equal to the chord, the edge has length `b` and its endpoints are `P` and
`Q` in one order or the other. -/
theorem corner_chord_partner_edge {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q)
    {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3} (h3 : (D.tile i3).edge k3 = segment ℝ P Q) :
    dist ((D.tile i3).pts k3) ((D.tile i3).pts (k3 + 1)) = sideOpp D.model 1 ∧
    (((D.tile i3).pts k3 = P ∧ (D.tile i3).pts (k3 + 1) = Q) ∨
      ((D.tile i3).pts k3 = Q ∧ (D.tile i3).pts (k3 + 1) = P)) := by
  obtain ⟨φ, c0, i3', k3', -, -, -, -, -, -, -, hlen, hend, -, -, huniq⟩ :=
    corner_chord_partner_data hM hco he hef hC
  obtain ⟨rfl, rfl⟩ := huniq i3 k3 hne h3
  exact ⟨hlen, hend⟩

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.corner_chord_partner_data
#print axioms Erdos634.CornerPara.corner_chord_partner
#print axioms Erdos634.CornerPara.corner_chord_matching_tiles
#print axioms Erdos634.CornerPara.corner_chord_partner_edge
