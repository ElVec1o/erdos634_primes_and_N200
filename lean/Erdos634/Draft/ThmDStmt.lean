import Erdos634.Draft.ThmDGeom
import Erdos634.Draft.ThmDPair
import Erdos634.Draft.FluxDRow4
import Erdos634.SssCongruent

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', R9b: from a `GPair` dissection to the normal form `T(g)`; `ThmDStatement` from the geometric statement `D1Spec`  

* `word_of_sum_scaled`, `alpha_apex_leg_scaled`, `thmD_of_D1_scaled` : `ThmDGeom` for a model scaled by a real `s > 0`
  (model sides `s u^2, s d(2u+d), s u(u+d)`, legs `s g u d (2u+d)`).
* `D1Spec` : **the exact remaining geometric statement** of Theorem D' (Lemma K + Lemma 34' over a real dissection of `T(g)`):
  for a dissection with target corners `(alpha, pi-2alpha, alpha)` at `(i, i+1, i+2)`, a model congruent to the tiles with angles
  `(alpha, pi-3alpha, 2alpha)` and sides `s(u^2, d(2u+d), u(u+d))`, legs `s g u d (2u+d)`, `(g-1) d < u`, every leg with `alpha` at both
  ends carries at least `u` edges `c` (`D1Hyp`).
* `thmDStatement_of_D1 : D1Spec -> ThmDStatement` : the reduction `GPair` data -> `(u,d,g,s)` (law of sines `Row4.sides`, the two
  boundary identities `M(a+c) = X = M'(c-a)`, `pair_param`) and the relabelling of the model that puts `alpha` at vertex 0.
-/

open scoped Classical

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg
  Erdos634.Draft.APrimeLegBuild Erdos634.Draft.ThmC

/-- `word_of_sum` for a model scaled by `s > 0`. -/
theorem word_of_sum_scaled (model : Erdos634.Geometry.Tri) (es : List OE) (a b c L : ℕ) (s : ℝ) (hs : 0 < s)
    (hs0 : sideOpp model 0 = s * (a : ℝ)) (hs1 : sideOpp model 1 = s * (b : ℝ))
    (hs2 : sideOpp model 2 = s * (c : ℝ)) (hsum : (es.map (wlen model)).sum = s * (L : ℝ)) :
    cntLetter isA es * a + cntLetter isB es * b + cntLetter isC es * c = L := by
  rw [sum_wlen, hs0, hs1, hs2] at hsum
  have h : s * ((cntLetter isA es * a + cntLetter isB es * b + cntLetter isC es * c : ℕ) : ℝ) = s * (L : ℝ) := by
    push_cast; linarith
  exact_mod_cast mul_left_cancel₀ hs.ne' h

/-- **The alpha-apex leg, kept (scaled model).** -/
theorem alpha_apex_leg_scaled {N : ℕ} (D : Dissection N) (model : Erdos634.Geometry.Tri)
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
    (a b c L : ℕ) (s : ℝ) (hs : 0 < s) (hs0 : sideOpp model 0 = s * (a : ℝ)) (hs1 : sideOpp model 1 = s * (b : ℝ))
    (hs2 : sideOpp model 2 = s * (c : ℝ))
    (hL1 : dist (D.target.pts i) (D.target.pts (i + 1)) = s * (L : ℝ))
    (hL2 : dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) = s * (L : ℝ)) :
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
      word_of_sum_scaled model _ a b c L s hs hs0 hs1 hs2 (hsum1.trans hL1), legFacts_q_pos h1c e0al hx1⟩
  · exact ⟨i + 1, t0', e0', r', h2c, hx2, lastal,
      word_of_sum_scaled model _ a b c L s hs hs0 hs1 hs2 (hsum2.trans hL2), legFacts_q_pos h2c hx2 lastal⟩

/-- **(D2) + (D1) ⇒ False, scaled model.** -/
theorem thmD_of_D1_scaled {N : ℕ} (D : Dissection N) (model : Erdos634.Geometry.Tri)
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
    (s : ℝ) (hs : 0 < s)
    (hs0 : sideOpp model 0 = s * ((u * u : ℕ) : ℝ))
    (hs1 : sideOpp model 1 = s * ((d * (u + (u + d)) : ℕ) : ℝ))
    (hs2 : sideOpp model 2 = s * ((u * (u + d) : ℕ) : ℝ))
    (hL1 : dist (D.target.pts i) (D.target.pts (i + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ))
    (hL2 : dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ))
    (hD1 : D1Hyp D model α u) : False := by
  obtain ⟨j, t0, e0, r, hlf, hf, hl, hw, hq⟩ := alpha_apex_leg_scaled D model hcong α hirr hA0 hA1 hA2 hα h3α i
    hcA hcApex hcB (u * u) (d * (u + (u + d))) (u * (u + d)) (g * u * (d * (u + (u + d)))) s hs hs0 hs1 hs2 hL1 hL2
  have hc := hD1 j t0 e0 r hlf hf hl
  have hb := alpha_leg_word_bound hd hu hcop hcond hq hw
  omega

/-- **The exact remaining geometric statement of Theorem D'** (Lemma K (K2) + Lemma 34' over a real dissection): in every
dissection of `T(g)` by the `gamma = 2 alpha` tile `(u,v)` with `(g-1)(v-u) < u`, every leg with `alpha` at both ends carries
at least `u` edges `c`. -/
def D1Spec : Prop :=
  ∀ {N : ℕ} (D : Dissection N) (model : Erdos634.Geometry.Tri) (α : ℝ) (i : Fin 3) (u d g : ℕ) (s : ℝ),
    (∀ j, model.Congruent (D.tile j)) → Irrational (α / Real.pi) →
    cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α →
    cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α →
    cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α → 0 < α → 3 * α < Real.pi →
    cornerAngle (D.target.pts (i + 1)) (D.target.pts i) (D.target.pts (i + 2)) = α →
    cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1)) (D.target.pts (i + 1 + 2)) = Real.pi - 2 * α →
    cornerAngle (D.target.pts (i + 1 + 1 + 1)) (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1 + 1 + 2)) = α →
    0 < d → 0 < u → Nat.Coprime u (u + d) → 2 ≤ g → (g - 1) * d < u → 0 < s →
    sideOpp model 0 = s * ((u * u : ℕ) : ℝ) → sideOpp model 1 = s * ((d * (u + (u + d)) : ℕ) : ℝ) →
    sideOpp model 2 = s * ((u * (u + d) : ℕ) : ℝ) →
    dist (D.target.pts i) (D.target.pts (i + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) →
    dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) →
    D1Hyp D model α u

#print axioms thmD_of_D1_scaled
end Erdos634.Draft.ThmD
