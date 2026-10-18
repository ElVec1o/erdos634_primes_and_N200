import Erdos634.Draft.ThmDApex

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', module R9a: the alpha-apex leg and the exact form of what (D1) must supply  

* `alpha_apex_leg` : at an apex of corner `π - 2α` between two base corners of angle `α`, one of the two legs along the
  adjacent sides has `α` at both ends, a `b`-edge, and the word `P a + Q b + R c = L` of its own edge list
  (`apex_leg_word_of_legs'` forgets the leg; this keeps it).
* `D1Hyp` : the geometric statement (D1) of `conjV2.md` §2 *for the legs of a given dissection*: a leg with `α` at both ends
  carries at least `u` edges `c` (the both-stopped run of length `≥ u`).  **NOT PROVED**; it is the hypothesis of
  `thmD_of_D1` and the named remaining obligation (Lemma K + Lemma 34' over a real dissection).
* `thmD_of_D1` : (D2) + `D1Hyp` + the word bound `leg_word_bound_D` give `False`.  This is `ThmDLeaf.thmD_skeleton`
  fed by the real leg, with all corner hypotheses explicit.
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg
  Erdos634.Draft.APrimeLegBuild

/-- (D1) for the legs of the dissection `D`: every leg with `α` at both ends has at least `u` edges `c`. -/
def D1Hyp {N : ℕ} (D : Dissection N) (model : Tri) (α : ℝ) (u : ℕ) : Prop :=
  ∀ (i : Fin 3) (t0 : Fin N) (e0 : OE) (r : List (LegStep N)), LegFacts D model α i t0 e0 r →
    e0.l = .al → ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r = .al →
    u ≤ cntLetter isC (legEdges e0 r)

/-- **The alpha-apex leg, kept.** -/
theorem alpha_apex_leg {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) (i : Fin 3)
    (hcA : cornerAngle (D.target.pts (i + 1)) (D.target.pts i) (D.target.pts (i + 2)) = α)
    (hcApex : cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1))
      (D.target.pts (i + 1 + 2)) = Real.pi - 2 * α)
    (hcB : cornerAngle (D.target.pts (i + 1 + 1 + 1)) (D.target.pts (i + 1 + 1))
      (D.target.pts (i + 1 + 1 + 2)) = α)
    (a b c L : ℕ) (hs0 : sideOpp model 0 = (a : ℝ)) (hs1 : sideOpp model 1 = (b : ℝ))
    (hs2 : sideOpp model 2 = (c : ℝ))
    (hL1 : dist (D.target.pts i) (D.target.pts (i + 1)) = (L : ℝ))
    (hL2 : dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) = (L : ℝ)) :
    ∃ (j : Fin 3) (t0 : Fin N) (e0 : OE) (r : List (LegStep N)), LegFacts D model α j t0 e0 r ∧
      e0.l = .al ∧ ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r = .al ∧
      cntLetter isA (legEdges e0 r) * a + cntLetter isB (legEdges e0 r) * b +
        cntLetter isC (legEdges e0 r) * c = L ∧ 1 ≤ cntLetter isB (legEdges e0 r) := by
  obtain ⟨t0, e0, r, h1⟩ := side_leg_gen D model hcong α hirr hA0 hA1 hA2 hα h3α i α (Real.pi - 2 * α) hcA hcApex
    (Or.inl rfl) (Or.inr (Or.inr rfl))
  obtain ⟨t0', e0', r', h2⟩ := side_leg_gen D model hcong α hirr hA0 hA1 hA2 hα h3α (i + 1) (Real.pi - 2 * α) α
    hcApex hcB (Or.inr (Or.inr rfl)) (Or.inl rfl)
  have hne := apex_tiles_distinct D model α h3α hα i hcApex h1 h2
  have h1c := h1
  have h2c := h2
  obtain ⟨hleg1, hf1, hl1, hfirst1, hlast1, hcnt1, hsum1, -, -⟩ := h1
  obtain ⟨hleg2, hf2, hl2, hfirst2, hlast2, hcnt2, hsum2, -, -⟩ := h2
  have e0al : e0.l = .al := corner_first D model hcong α hirr hA0 hA1 hA2 hα h3α i hcA t0 e0.l hf1
  have lastal : ((legEdges e0' r').getLast (List.cons_ne_nil _ _)).r = .al :=
    corner_first D model hcong α hirr hA0 hA1 hA2 hα h3α (i + 1 + 1) hcB (lastTile t0' r') _ hl2
  have hpair := apex_pair D model hcong α hirr hA0 hA1 hA2 hα (i + 1) hcApex (lastTile t0 r) t0' hne
    _ _ hl1 hf2
  rcases hpair with ⟨hx1, -⟩ | ⟨-, hx2⟩
  · exact ⟨i, t0, e0, r, h1c, e0al, hx1,
      word_of_sum model _ a b c L hs0 hs1 hs2 (hsum1.trans hL1), legFacts_q_pos h1c e0al hx1⟩
  · exact ⟨i + 1, t0', e0', r', h2c, hx2, lastal,
      word_of_sum model _ a b c L hs0 hs1 hs2 (hsum2.trans hL2), legFacts_q_pos h2c hx2 lastal⟩

/-- **(D2) + (D1) ⇒ False**, with the real leg: if `D1Hyp` holds for `D`, the pair `(u, d, g)` with `(g - 1) d < u`
and tile sides `(u², d(2u+d), u(u+d))`, base-leg length `L = g u (d (2u+d))` admits no such `D`. -/
theorem thmD_of_D1 {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) (i : Fin 3)
    (hcA : cornerAngle (D.target.pts (i + 1)) (D.target.pts i) (D.target.pts (i + 2)) = α)
    (hcApex : cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1))
      (D.target.pts (i + 1 + 2)) = Real.pi - 2 * α)
    (hcB : cornerAngle (D.target.pts (i + 1 + 1 + 1)) (D.target.pts (i + 1 + 1))
      (D.target.pts (i + 1 + 1 + 2)) = α)
    {u d g : ℕ} (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d)) (hcond : (g - 1) * d < u)
    (hs0 : sideOpp model 0 = ((u * u : ℕ) : ℝ))
    (hs1 : sideOpp model 1 = ((d * (u + (u + d)) : ℕ) : ℝ))
    (hs2 : sideOpp model 2 = ((u * (u + d) : ℕ) : ℝ))
    (hL1 : dist (D.target.pts i) (D.target.pts (i + 1)) = ((g * u * (d * (u + (u + d))) : ℕ) : ℝ))
    (hL2 : dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) = ((g * u * (d * (u + (u + d))) : ℕ) : ℝ))
    (hD1 : D1Hyp D model α u) : False := by
  obtain ⟨j, t0, e0, r, hlf, hf, hl, hw, hq⟩ := alpha_apex_leg D model hcong α hirr hA0 hA1 hA2 hα h3α i
    hcA hcApex hcB (u * u) (d * (u + (u + d))) (u * (u + d)) (g * u * (d * (u + (u + d)))) hs0 hs1 hs2 hL1 hL2
  have hc := hD1 j t0 e0 r hlf hf hl
  have hb := alpha_leg_word_bound hd hu hcop hcond hq hw
  omega

end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.thmD_of_D1
#print axioms Erdos634.Draft.ThmD.alpha_apex_leg
