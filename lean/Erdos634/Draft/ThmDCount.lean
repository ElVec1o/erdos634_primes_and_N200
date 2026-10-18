import Erdos634.Draft.ThmDLegLen
import Erdos634.Draft.ThmDWords

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', D2 module C: counting identity at both ends, apex pair, the alpha-apex leg word  (DRAFT, NOT COMPILED, )

Written 2026-10-18 while the Lean slot was busy; never run through `lake`/`lean`.  Not in `All`.

Finishes the three counting items of the formalization plan:

1. **edge list <-> side_partition** : `ThmDLegLen.exists_chain_leg_len` gives `Σ wlen (legEdges e0 r) = |side|`, hence
   (`ThmDEdgeLen.sum_wlen`, `word_of_sum`) `#A·a + #B·b + #C·c = L` for the leg's own edge list.
2. **mirrored counting identity** : `counting_identity_gen` (no hypothesis on the first/last angle):
   `μ_β + 1 = q + [first.l = β] + [last.r = β]`.  The old `APrimeSeat1.counting_identity` is the case `first.l = α`.
   Same for a real leg (`realLeg_counting_gen`).  A leg with `α` at BOTH ends has `q = μ_β + 1 ≥ 1` (`q_pos_of_ends`).
3. **apex alpha count** : `corner_total2` / `apex_pair` : at a target vertex of corner angle `π - 2α` two DISTINCT tiles
   present `{α, β}` (one each).  `apex_leg_word_of_legs` combines them with the two legs meeting at the apex.

**(Now PROVED in `ThmDApex.apex_tiles_distinct`; `ThmDApex.apex_leg_word_of_legs'` has no `hne`.)  The hypothesis was:** `hne : lastTile t0 r ≠ t0'`, i.e. the last tile of the leg ending at the
apex and the first tile of the leg leaving it are different tiles.  Hand argument: a tile with edges along BOTH sides
at the apex would have the whole corner angle `π - 2α = α + β` as its angle there, but a tile angle is `α`, `β` or
`2α`.  Formal obstruction: `localAngle` at a vertex = the angle between its two incident edges, and these edges lie on
the two side rays (a `Tri.localAngle` / `cornerAngle` comparison under positive scaling).  Statement to prove:

    lemma apex_tiles_distinct (hcorner : cornerAngle (pts (i+1+1)) (pts (i+1)) (pts (i+1+2)) = π - 2α) ...
      : lastTile t0 r ≠ t0'          -- for legs produced by `side_leg_gen` at sides `i` and `i+1`

Also not in this file: the corner hypotheses are literal Fin-index forms (`i + 1 + 1`, ...).  To be instantiated for
`T(g)` after a relabelling of the target (`CongruentDissection.relabelTarget'`).
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg
  Erdos634.Draft.APrimeLegBuild

/-! ### 1. The counting identity without hypotheses on the end angles -/

/-- `μ_β + 1 = q + β(first.l) + β(last.r)`. -/
theorem counting_identity_gen (e : OE) (t : List (Cnt × OE)) (hv : Valid e t) :
    muB t + 1 = cntLetter isB (edges e t) + e.l.cnt.2.1 + (lastE e t).r.cnt.2.1 := by
  have h1 := valid_beta e t hv
  rw [sumBeta_eq] at h1
  have hl := length_eq (edges e t)
  have hlen : (edges e t).length = t.length + 1 := by simp [edges]
  omega

/-- `μ_{α+2γ} + 3 = p + 2r + (α+2γ)(first.l) + (α+2γ)(last.r)`. -/
theorem counting_identity_ag_gen (e : OE) (t : List (Cnt × OE)) (hv : Valid e t) :
    muAG t + 3 = cntLetter isA (edges e t) + 2 * cntLetter isC (edges e t) +
      (e.l.cnt.1 + 2 * e.l.cnt.2.2) + ((lastE e t).r.cnt.1 + 2 * (lastE e t).r.cnt.2.2) := by
  have h2 := valid_ag e t hv
  rw [sumAG_eq] at h2
  have hl := length_eq (edges e t)
  have hlen : (edges e t).length = t.length + 1 := by simp [edges]
  omega

/-- A leg with `α` at both ends (no `β` at either) has at least one `b`-edge. -/
theorem q_pos_of_ends (e : OE) (t : List (Cnt × OE)) (hv : Valid e t)
    (h1 : e.l.cnt.2.1 = 0) (h2 : (lastE e t).r.cnt.2.1 = 0) : 1 ≤ cntLetter isB (edges e t) := by
  have := counting_identity_gen e t hv
  omega

theorem realLeg_counting_gen {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi)
    (r : List (LegStep N)) (t : Fin N) (e : OE) (hleg : RealLeg D α t e r) :
    ∃ steps : List (Cnt × OE), steps.map Prod.snd = r.map LegStep.e ∧ Valid e steps ∧
      muB steps + 1 = cntLetter isB (legEdges e r) + e.l.cnt.2.1 +
        ((legEdges e r).getLast (List.cons_ne_nil _ _)).r.cnt.2.1 := by
  obtain ⟨steps, hmap, hval⟩ := RealLeg.toValid D model hcong α hirr hA0 hA1 hA2 hα h3α r t e hleg
  have hedges : edges e steps = legEdges e r := by simp [edges, legEdges, hmap]
  have hgl : ∀ (l : List OE) (h : l = legEdges e r) (h1 : l ≠ []) (h2 : legEdges e r ≠ []),
      l.getLast h1 = (legEdges e r).getLast h2 := by
    intro l h; subst h; intros; rfl
  have hl : lastE e steps = (legEdges e r).getLast (List.cons_ne_nil _ _) := by
    rw [lastE_eq]; exact hgl _ hedges _ _
  have key := counting_identity_gen e steps hval
  rw [hedges, hl] at key
  exact ⟨steps, hmap, hval, key⟩

/-! ### 2. The leg along one side, with word and counting data -/

/-- everything the D2 argument needs to know about a leg along the side `i` of the target -/
abbrev LegFacts {N : ℕ} (D : Dissection N) (model : Tri) (α : ℝ) (i : Fin 3)
    (t0 : Fin N) (e0 : OE) (r : List (LegStep N)) : Prop :=
  RealLeg D α t0 e0 r ∧
  (D.tile t0).localAngle (D.target.pts i) = angVal α e0.l ∧
  (D.tile (lastTile t0 r)).localAngle (D.target.pts (i + 1)) =
    angVal α ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r ∧
  (e0.l = .al ∨ e0.l = .be) ∧
  (((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r = .al ∨
    ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r = .be) ∧
  (∃ steps : List (Cnt × OE), steps.map Prod.snd = r.map LegStep.e ∧ Valid e0 steps ∧
    muB steps + 1 = cntLetter isB (legEdges e0 r) + e0.l.cnt.2.1 +
      ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r.cnt.2.1) ∧
  ((legEdges e0 r).map (wlen model)).sum = dist (D.target.pts i) (D.target.pts (i + 1)) ∧
  (∃ j k : Fin 3, j ≠ k ∧ (D.tile t0).pts j = D.target.pts i ∧
    (D.tile t0).pts k ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
    (D.tile t0).pts k ≠ D.target.pts i) ∧
  (∃ j k : Fin 3, j ≠ k ∧ (D.tile (lastTile t0 r)).pts j = D.target.pts (i + 1) ∧
    (D.tile (lastTile t0 r)).pts k ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
    (D.tile (lastTile t0 r)).pts k ≠ D.target.pts (i + 1))

theorem side_leg_gen {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) (i : Fin 3) (c1 c2 : ℝ)
    (hc1 : cornerAngle (D.target.pts (i + 1)) (D.target.pts i) (D.target.pts (i + 2)) = c1)
    (hc2 : cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1)) (D.target.pts (i + 1 + 2)) = c2)
    (hcc1 : c1 = α ∨ c1 = Real.pi - 3 * α ∨ c1 = Real.pi - 2 * α)
    (hcc2 : c2 = α ∨ c2 = Real.pi - 3 * α ∨ c2 = Real.pi - 2 * α) :
    ∃ (t0 : Fin N) (e0 : OE) (r : List (LegStep N)), LegFacts D model α i t0 e0 r := by
  obtain ⟨t0, e0, r, hleg, hfirst, hlast, -, hsum, hfo, hlo⟩ :=
    exists_chain_leg_len D model hcong α hirr hα hA0 hA1 hA2 i
  have h1 := corner_last D model hcong α hirr hA0 hA1 hA2 hα h3α i c1 hc1 hcc1 t0 e0.l hfirst
  have h2 := corner_last D model hcong α hirr hA0 hA1 hA2 hα h3α (i + 1) c2 hc2 hcc2
    (lastTile t0 r) _ hlast
  obtain ⟨steps, hmap, hval, hid⟩ := realLeg_counting_gen D model hcong α hirr hA0 hA1 hA2 hα h3α
    r t0 e0 hleg
  exact ⟨t0, e0, r, hleg, hfirst, hlast, h1, h2, ⟨steps, hmap, hval, hid⟩, hsum, hfo, hlo⟩

/-- the word of a leg: `P a + Q b + R c = L` with `P, Q, R` its letter counts -/
theorem word_of_sum (model : Tri) (es : List OE) (a b c L : ℕ)
    (hs0 : sideOpp model 0 = (a : ℝ)) (hs1 : sideOpp model 1 = (b : ℝ))
    (hs2 : sideOpp model 2 = (c : ℝ)) (hsum : (es.map (wlen model)).sum = (L : ℝ)) :
    cntLetter isA es * a + cntLetter isB es * b + cntLetter isC es * c = L := by
  rw [sum_wlen, hs0, hs1, hs2] at hsum
  exact_mod_cast hsum

/-! ### 3. Two distinct tiles at an apex of corner angle `π - 2α` carry `{α, β}` -/

theorem corner_total2 {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (k : Fin 3) (c : ℝ)
    (hc : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = c)
    (hcpi : c < Real.pi) (t1 t2 : Fin N) (hne : t1 ≠ t2) (a1 a2 : Ang)
    (h1 : (D.tile t1).localAngle (D.target.pts k) = angVal α a1)
    (h2 : (D.tile t2).localAngle (D.target.pts k) = angVal α a2) :
    ∃ X Y Z : ℕ, angVal α a1 + angVal α a2 +
      ((X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α)) = c := by
  classical
  let CD : CongruentDissection N := ⟨D, model, fun i => (hcong i).symm⟩
  have hmem : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈
      ({α, Real.pi - 3 * α, 2 * α, Real.pi, 0} : Finset ℝ) :=
    fun i => Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem CD α (Real.pi - 3 * α)
      (2 * α) hA0 hA1 hA2 k i
  have hsum : ∑ i, (D.tile i).localAngle (D.target.pts k) = c := by
    rw [Erdos634.VertexFigureReal.corner_angle_sum D k, hc]
  have hle : ∀ i, (D.tile i).localAngle (D.target.pts k) ≤ c := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (f := fun i => (D.tile i).localAngle (D.target.pts k))
      (fun j _ => (D.tile j).localAngle_nonneg _) (Finset.mem_univ i)
  have hform : ∀ i ∈ (Finset.univ.erase t1).erase t2, (D.tile i).localAngle (D.target.pts k) = 0 ∨
      ∃ a : Ang, (D.tile i).localAngle (D.target.pts k) = angVal α a := by
    intro i _
    have hm := hmem i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h1' | h1' | h1' | h1' | h1'
    · exact Or.inr ⟨.al, h1'⟩
    · exact Or.inr ⟨.be, h1'⟩
    · exact Or.inr ⟨.ga, h1'⟩
    · have := hle i; rw [h1'] at this; linarith
    · exact Or.inl h1'
  obtain ⟨X, Y, Z, hXYZ⟩ := sum_of_values α ((Finset.univ.erase t1).erase t2)
    (fun i => (D.tile i).localAngle (D.target.pts k)) hform
  refine ⟨X, Y, Z, ?_⟩
  have e1 : ∑ i ∈ Finset.univ.erase t1, (D.tile i).localAngle (D.target.pts k) =
      (D.tile t2).localAngle (D.target.pts k) +
        ∑ i ∈ (Finset.univ.erase t1).erase t2, (D.tile i).localAngle (D.target.pts k) :=
    (Finset.add_sum_erase _ (fun i => (D.tile i).localAngle (D.target.pts k))
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ t2⟩)).symm
  have e2 : ∑ i, (D.tile i).localAngle (D.target.pts k) =
      (D.tile t1).localAngle (D.target.pts k) +
        ∑ i ∈ Finset.univ.erase t1, (D.tile i).localAngle (D.target.pts k) :=
    (Finset.add_sum_erase _ (fun i => (D.tile i).localAngle (D.target.pts k))
      (Finset.mem_univ t1)).symm
  rw [← hXYZ]
  linarith [e1, e2, hsum, h1, h2]

/-- **Apex pair.**  At a target vertex of corner angle `π - 2α`, two distinct tiles with positive angle there present
exactly `α` and `β`, in one order or the other. -/
theorem apex_pair {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (k : Fin 3)
    (hc : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = Real.pi - 2 * α)
    (t1 t2 : Fin N) (hne : t1 ≠ t2) (a1 a2 : Ang)
    (h1 : (D.tile t1).localAngle (D.target.pts k) = angVal α a1)
    (h2 : (D.tile t2).localAngle (D.target.pts k) = angVal α a2) :
    (a1 = Ang.al ∧ a2 = Ang.be) ∨ (a1 = Ang.be ∧ a2 = Ang.al) := by
  obtain ⟨X, Y, Z, hs⟩ := corner_total2 D model hcong α hA0 hA1 hA2 k _ hc (by linarith) t1 t2 hne
    a1 a2 h1 h2
  cases a1 <;> cases a2
  · exfalso
    have := cnt_eq α hirr (X + 2) Y Z (-2) 1
      (by simp only [angVal] at hs; push_cast; linarith)
    omega
  · exact Or.inl ⟨rfl, rfl⟩
  · exfalso
    have := cnt_eq α hirr (X + 1) Y (Z + 1) (-2) 1
      (by simp only [angVal] at hs; push_cast; linarith)
    omega
  · exact Or.inr ⟨rfl, rfl⟩
  · exfalso
    have := cnt_eq α hirr X (Y + 2) Z (-2) 1
      (by simp only [angVal] at hs; push_cast; linarith)
    omega
  · exfalso
    have := cnt_eq α hirr X (Y + 1) (Z + 1) (-2) 1
      (by simp only [angVal] at hs; push_cast; linarith)
    omega
  · exfalso
    have := cnt_eq α hirr (X + 1) Y (Z + 1) (-2) 1
      (by simp only [angVal] at hs; push_cast; linarith)
    omega
  · exfalso
    have := cnt_eq α hirr X (Y + 1) (Z + 1) (-2) 1
      (by simp only [angVal] at hs; push_cast; linarith)
    omega
  · exfalso
    have := cnt_eq α hirr X Y (Z + 2) (-2) 1
      (by simp only [angVal] at hs; push_cast; linarith)
    omega

/-! ### 4. The alpha-apex leg has a `b`-edge and carries the word of its side -/

/-- A leg with `α` at both ends has a `b`-edge. -/
theorem legFacts_q_pos {N : ℕ} {D : Dissection N} {model : Tri} {α : ℝ} {i : Fin 3}
    {t0 : Fin N} {e0 : OE} {r : List (LegStep N)} (h : LegFacts D model α i t0 e0 r)
    (hf : e0.l = .al) (hl : ((legEdges e0 r).getLast (List.cons_ne_nil _ _)).r = .al) :
    1 ≤ cntLetter isB (legEdges e0 r) := by
  obtain ⟨-, -, -, -, -, ⟨steps, -, -, hid⟩, -, -, -⟩ := h
  rw [hf, hl] at hid
  have h0 : (Ang.al).cnt.2.1 = 0 := rfl
  rw [h0] at hid
  omega

/-- **D2, assembled.**  Two legs meeting at an apex of corner angle `π - 2α` (the first ends at the apex and starts at a
base corner of angle `α`; the second starts at the apex and ends at a base corner of angle `α`), whose apex tiles are
distinct (`hne`).  Then one of the two legs has `α` at both ends, so its word `(P, Q, R)` with
`P a + Q b + R c = L` has `Q ≥ 1`. -/
theorem apex_leg_word_of_legs {N : ℕ} (D : Dissection N) (model : Tri)
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
    (hL2 : dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) = (L : ℝ))
    {t0 t0' : Fin N} {e0 e0' : OE} {r r' : List (LegStep N)}
    (h1 : LegFacts D model α i t0 e0 r) (h2 : LegFacts D model α (i + 1) t0' e0' r')
    (hne : lastTile t0 r ≠ t0') :
    ∃ P Q R : ℕ, P * a + Q * b + R * c = L ∧ 1 ≤ Q := by
  have h1c := h1
  have h2c := h2
  obtain ⟨hleg1, hf1, hl1, hfirst1, hlast1, hcnt1, hsum1, -, -⟩ := h1
  obtain ⟨hleg2, hf2, hl2, hfirst2, hlast2, hcnt2, hsum2, -, -⟩ := h2
  -- the base-corner ends are alpha
  have e0al : e0.l = .al := corner_first D model hcong α hirr hA0 hA1 hA2 hα h3α i hcA t0 e0.l hf1
  have lastal : ((legEdges e0' r').getLast (List.cons_ne_nil _ _)).r = .al :=
    corner_first D model hcong α hirr hA0 hA1 hA2 hα h3α (i + 1 + 1) hcB (lastTile t0' r') _ hl2
  -- the two apex tiles carry {alpha, beta}
  have hpair := apex_pair D model hcong α hirr hA0 hA1 hA2 hα (i + 1) hcApex (lastTile t0 r) t0' hne
    _ _ hl1 hf2
  rcases hpair with ⟨hx1, -⟩ | ⟨-, hx2⟩
  · -- leg 1 has alpha at both ends
    refine ⟨cntLetter isA (legEdges e0 r), cntLetter isB (legEdges e0 r), cntLetter isC (legEdges e0 r),
      word_of_sum model _ a b c L hs0 hs1 hs2 (hsum1.trans hL1), ?_⟩
    exact legFacts_q_pos h1c e0al hx1
  · -- leg 2 has alpha at both ends
    refine ⟨cntLetter isA (legEdges e0' r'), cntLetter isB (legEdges e0' r'), cntLetter isC (legEdges e0' r'),
      word_of_sum model _ a b c L hs0 hs1 hs2 (hsum2.trans hL2), ?_⟩
    exact legFacts_q_pos h2c hx2 lastal

/-- the arithmetic wiring, `ThmD.leg_word_bound_D` applied to the word of the alpha-apex leg (module `ThmDWords`) -/
theorem alpha_leg_word_bound {u d g P Q R : ℕ} (hd : 0 < d) (hu : 0 < u)
    (hcop : Nat.Coprime u (u + d)) (hcond : (g - 1) * d < u) (hQ : 1 ≤ Q)
    (h : P * (u * u) + Q * (d * (u + (u + d))) + R * (u * (u + d)) = g * u * (d * (u + (u + d)))) :
    R < u :=
  leg_word_bound_D_lt hd hu hcop hcond hQ h

end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.apex_leg_word_of_legs
#print axioms Erdos634.Draft.ThmD.realLeg_counting_gen
#print axioms Erdos634.Draft.ThmD.alpha_leg_word_bound
