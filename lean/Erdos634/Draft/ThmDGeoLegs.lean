import Mathlib.Tactic
import Erdos634.Draft.ThmDStmt
import Erdos634.Draft.ThmDLegPos
import Erdos634.Draft.ThmDGeoLegRun

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (3)): the positioned α-apex leg  

`side_leg_pos` is `ThmDCount.side_leg_gen` with the position of the leg on its side; `alpha_apex_leg_pos` is `ThmDStmt.alpha_apex_leg_scaled` (unit
scale) for the positioned legs: one of the two legs meeting at the apex has `α` at both ends, with its word, `q ≥ 1`, its position and its end angle.
-/

open scoped Classical

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg
  Erdos634.Draft.APrimeLegBuild Erdos634.Draft.ThmC

theorem side_leg_pos {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) (i : Fin 3) (c1 c2 : ℝ)
    (hc1 : cornerAngle (D.target.pts (i + 1)) (D.target.pts i) (D.target.pts (i + 2)) = c1)
    (hc2 : cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1)) (D.target.pts (i + 1 + 2)) = c2)
    (hcc1 : c1 = α ∨ c1 = Real.pi - 3 * α ∨ c1 = Real.pi - 2 * α)
    (hcc2 : c2 = α ∨ c2 = Real.pi - 3 * α ∨ c2 = Real.pi - 2 * α) :
    ∃ (t0 : Fin N) (e0 : OE) (r : List (LegStep N)), LegFacts D model α i t0 e0 r ∧
      LegPos D model (D.target.pts i) (D.target.pts (i + 1)) t0 e0 0 r := by
  obtain ⟨t0, e0, r, hleg, hfirst, hlast, -, hsum, hfo, hlo, hpos⟩ :=
    exists_chain_leg_pos D model hcong α hirr hα hA0 hA1 hA2 i
  have h1 := corner_last D model hcong α hirr hA0 hA1 hA2 hα h3α i c1 hc1 hcc1 t0 e0.l hfirst
  have h2 := corner_last D model hcong α hirr hA0 hA1 hA2 hα h3α (i + 1) c2 hc2 hcc2
    (lastTile t0 r) _ hlast
  obtain ⟨steps, hmap, hval, hid⟩ := realLeg_counting_gen D model hcong α hirr hA0 hA1 hA2 hα h3α
    r t0 e0 hleg
  exact ⟨t0, e0, r, ⟨hleg, hfirst, hlast, h1, h2, ⟨steps, hmap, hval, hid⟩, hsum, hfo, hlo⟩, hpos⟩

/-- **The positioned α-apex leg (unit scale).** -/
theorem alpha_apex_leg_pos {N : ℕ} (D : Dissection N) (model : Erdos634.Geometry.Tri)
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
    ∃ (t0 : Fin N) (e0 : OE) (r : List (LegStep N)),
      ((LegFacts D model α i t0 e0 r ∧ LegPos D model (D.target.pts i) (D.target.pts (i + 1)) t0 e0 0 r ∧
        LegEnd D α (D.target.pts (i + 1)) t0 e0 r) ∨
       (LegFacts D model α (i + 1) t0 e0 r ∧
        LegPos D model (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) t0 e0 0 r ∧
        LegEnd D α (D.target.pts (i + 1 + 1)) t0 e0 r)) ∧
      e0.l = .al ∧ ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r = .al ∧
      cntLetter isA (legEdges e0 r) * a + cntLetter isB (legEdges e0 r) * b +
        cntLetter isC (legEdges e0 r) * c = L ∧ 1 ≤ cntLetter isB (legEdges e0 r) := by
  obtain ⟨t0, e0, r, h1, p1⟩ := side_leg_pos D model hcong α hirr hA0 hA1 hA2 hα h3α i α (Real.pi - 2 * α) hcA hcApex
    (Or.inl rfl) (Or.inr (Or.inr rfl))
  obtain ⟨t0', e0', r', h2, p2⟩ := side_leg_pos D model hcong α hirr hA0 hA1 hA2 hα h3α (i + 1) (Real.pi - 2 * α) α
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
  have hw : ∀ (es : List OE) (L' : ℕ), (es.map (wlen model)).sum = (L' : ℝ) →
      cntLetter isA es * a + cntLetter isB es * b + cntLetter isC es * c = L' := fun es L' h =>
    word_of_sum model es a b c L' hs0 hs1 hs2 h
  rcases hpair with ⟨hx1, -⟩ | ⟨-, hx2⟩
  · refine ⟨t0, e0, r, Or.inl ⟨h1c, p1, legEnd_of_last _ _ _ r t0 e0 hl1⟩, e0al, hx1,
      hw _ L (hsum1.trans hL1), legFacts_q_pos h1c e0al hx1⟩
  · refine ⟨t0', e0', r', Or.inr ⟨h2c, p2, legEnd_of_last _ _ _ r' t0' e0' hl2⟩, hx2, lastal,
      hw _ L (hsum2.trans hL2), legFacts_q_pos h2c hx2 lastal⟩

#print axioms side_leg_pos
#print axioms alpha_apex_leg_pos
end Erdos634.Draft.ThmD
