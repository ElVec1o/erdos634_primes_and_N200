import Erdos634.Draft.APrimeSeat1
import Erdos634.PinPlumbing
import Erdos634.CongruentAngles

/-!
# APRIME: the leg layer over a real `Dissection`, and the bridge to `APrimeSeat1.Valid`  

Discharges (the junction part of) the named blocker of `APrimeSeat1` / `APrimeLadder`.

**What is proved.**  For a real `Dissection D` whose tiles are all congruent to a model tile `M` with
corner angles `α, π − 3α, 2α` (`α/π` irrational):

* `junction_fan` : at a boundary point `p` of the target which is not a target vertex, if two distinct
  tiles `tW, tE` present at `p` the angles `angVal e.r` and `angVal e'.l` (an oriented-edge pair), then
  the remaining tiles present a multiplicity triple `m` with `Fan (e.r + e'.l + m)` -- exactly the
  step of `APrimeSeat1.Valid`.  (`PinPlumbing.junction_equation` + `straight_vertex`.)
* `RealLeg` : the leg layer.  A real leg is the ordered list of tiles having an edge on a straight
  boundary segment, with their oriented-edge types `OE`, and the junction points between consecutive
  ones; each junction is a frontier non-vertex of the target, the two flanking tiles are distinct and
  present the angles prescribed by their `OE`s.
* `RealLeg.toValid` : **the bridge** -- a real leg yields middle triples `m_k` with `Valid e steps`
  (and `steps.map snd` the leg's own edge list).
* `RealLeg.counting_identity` : `APrimeSeat1.counting_identity` for real legs.
* `exists_OE` : the `OE` of a tile edge is *determined by the tile*: for a tile congruent to the model
  and any edge `(pts k, pts (k+1))`, the local angles at the two ends are `angVal e.l, angVal e.r` for
  a (unique) `OE e`.  (`three_angles_distinct`: the three corner angles are `α, β, γ` once each.)

**Named remaining (not proved here).**  The *construction* of a `RealLeg` from a target side:
(i) ordering `Dissection.side_partition`'s edges along the side (`IntervalChain.chain_of_cover` gives
the order-theoretic chain on the traces; the geometric transfer of `Fin n`-indexed interval data to the
plane is not written), (ii) identifying the shared endpoint of consecutive edges as the junction `p`
and that it is a frontier non-vertex of the target (interior points of a side other than corners),
(iii) the first/last-angle hypotheses `e.l = al`, `(last).r ∈ {al, be}` come from the target's corner
(`base_corner_figure`).  Items (i)-(iii) are bookkeeping, no new angle arithmetic.
-/

namespace Erdos634.Draft.APrimeLeg

open Erdos634.Geometry Erdos634.Draft.APrimeSeat1

/-! ### Angle values and counts -/

/-- The real value of each abstract angle for the tile `(α, π − 3α, 2α)`. -/
noncomputable def angVal (α : ℝ) : Ang → ℝ
  | .al => α | .be => Real.pi - 3 * α | .ga => 2 * α

/-- Real value of a count triple. -/
noncomputable def cval (α : ℝ) (c : Cnt) : ℝ :=
  (c.1 : ℝ) * α + (c.2.1 : ℝ) * (Real.pi - 3 * α) + (c.2.2 : ℝ) * (2 * α)

theorem cval_add (α : ℝ) (a b : Cnt) : cval α (Cnt.add a b) = cval α a + cval α b := by
  simp only [cval, Cnt.add]; push_cast; ring

theorem cval_ang (α : ℝ) (a : Ang) : cval α a.cnt = angVal α a := by
  cases a <;> simp [cval, angVal, Ang.cnt]

/-- A count triple whose value is `π` is a fan. -/
theorem fan_of_cval (α : ℝ) (hirr : Irrational (α / Real.pi)) (c : Cnt)
    (h : cval α c = Real.pi) : Fan c := by
  obtain ⟨x, y, z⟩ := c
  have := straight_vertex α hirr x y z (by simpa [cval] using h)
  exact ⟨this.1, this.2⟩

/-! ### The vertex step for a real dissection -/

/-- **Junction fan.**  At a frontier non-vertex `p` of a dissection whose tiles are all congruent to a
model with corner angles `α, π − 3α, 2α`, two distinct tiles presenting `angVal e.r` and `angVal e'.l`
leave a residue `m` of multiplicities with `Fan (e.r + e'.l + m)`. -/
theorem junction_fan {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi)
    {p : Plane} (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (tW tE : Fin N) (hWE : tW ≠ tE) (e e' : OE)
    (hW : (D.tile tW).localAngle p = angVal α e.r)
    (hE : (D.tile tE).localAngle p = angVal α e'.l) :
    ∃ m : Cnt, Fan (Cnt.add (Cnt.add e.r.cnt e'.l.cnt) m) := by
  have hpos : ∀ a : Ang, 0 < angVal α a := by
    intro a; cases a <;> simp only [angVal] <;> linarith
  obtain ⟨x, y, z, hxyz⟩ := Erdos634.PinPlumbing.junction_equation D model hcong hp hv tW tE hWE
    (by rw [hW]; exact hpos _) (by rw [hE]; exact hpos _)
  rw [hA0, hA1, hA2, hW, hE] at hxyz
  refine ⟨(x, y, z), fan_of_cval α hirr _ ?_⟩
  rw [cval_add, cval_add, cval_ang, cval_ang]
  simp only [cval]
  linarith

/-! ### The leg layer -/

/-- One step of a leg: the junction point `p` reached, the next tile `t`, and its oriented edge `e`. -/
structure LegStep (N : ℕ) where
  p : Plane
  t : Fin N
  e : OE

/-- The real-leg predicate: starting from tile `t` with oriented edge `e`, each step is a junction
that is a frontier non-vertex of the target, between two distinct tiles presenting the angles that
their `OE`s prescribe. -/
def RealLeg {N : ℕ} (D : Dissection N) (α : ℝ) : Fin N → OE → List (LegStep N) → Prop
  | _, _, [] => True
  | t, e, s :: r =>
      s.p ∈ frontier D.target.carrier ∧ s.p ∉ Set.range D.target.pts ∧ t ≠ s.t ∧
      (D.tile t).localAngle s.p = angVal α e.r ∧ (D.tile s.t).localAngle s.p = angVal α s.e.l ∧
      RealLeg D α s.t s.e r

/-- The edge list of a leg. -/
def legEdges {N : ℕ} (e : OE) (r : List (LegStep N)) : List OE := e :: r.map LegStep.e

/-- **The bridge.**  A real leg satisfies the combinatorial model `Valid`, with the leg's own edge list. -/
theorem RealLeg.toValid {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) :
    ∀ (r : List (LegStep N)) (t : Fin N) (e : OE), RealLeg D α t e r →
      ∃ steps : List (Cnt × OE), steps.map Prod.snd = r.map LegStep.e ∧ Valid e steps := by
  intro r
  induction r with
  | nil => intro t e _; exact ⟨[], rfl, trivial⟩
  | cons s r ih =>
    intro t e ⟨hp, hv, hne, hW, hE, hrest⟩
    obtain ⟨m, hm⟩ := junction_fan D model hcong α hirr hA0 hA1 hA2 hα h3α hp hv t s.t hne e s.e hW hE
    obtain ⟨steps, hmap, hval⟩ := ih s.t s.e hrest
    refine ⟨(m, s.e) :: steps, ?_, hm, ?_⟩
    · simp [hmap]
    · simpa [Valid] using hval

/-- `lastE` of the steps is the last edge of the leg. -/
theorem lastE_eq (e : OE) (steps : List (Cnt × OE)) :
    lastE e steps = (e :: steps.map Prod.snd).getLast (List.cons_ne_nil _ _) := by
  induction steps generalizing e with
  | nil => simp [lastE]
  | cons p t ih =>
    obtain ⟨m, e'⟩ := p
    simp only [lastE, List.map_cons]
    rw [ih e']
    rw [List.getLast_cons (List.cons_ne_nil _ _)]

/-- **The counting identity for a real leg.**  With first left angle `α` and last right angle `α` or `β`
(both read off the target's corner), the leg's edge letters and its middle multiplicities satisfy
`μ_β + 1 = q + ε`, `μ_α + 2 μ_γ + 1 + ε = p + 2r`. -/
theorem RealLeg.counting_identity {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi)
    (r : List (LegStep N)) (t : Fin N) (e : OE) (hleg : RealLeg D α t e r)
    (hfirst : e.l = .al) (hlast : ((legEdges e r).getLast (List.cons_ne_nil _ _)).r = .al ∨
      ((legEdges e r).getLast (List.cons_ne_nil _ _)).r = .be) (ε : ℕ)
    (hε : ε = ((legEdges e r).getLast (List.cons_ne_nil _ _)).r.cnt.2.1) :
    ∃ steps : List (Cnt × OE), steps.map Prod.snd = r.map LegStep.e ∧ Valid e steps ∧
      muB steps + 1 = cntLetter isB (legEdges e r) + ε ∧
      muAG steps + 1 + ε = cntLetter isA (legEdges e r) + 2 * cntLetter isC (legEdges e r) := by
  obtain ⟨steps, hmap, hval⟩ := RealLeg.toValid D model hcong α hirr hA0 hA1 hA2 hα h3α r t e hleg
  have hedges : edges e steps = legEdges e r := by simp [edges, legEdges, hmap]
  have hgl : ∀ (l : List OE) (h : l = legEdges e r) (h1 : l ≠ []) (h2 : legEdges e r ≠ []),
      l.getLast h1 = (legEdges e r).getLast h2 := by
    intro l h; subst h; intros; rfl
  have hl : lastE e steps = (legEdges e r).getLast (List.cons_ne_nil _ _) := by
    rw [lastE_eq]; exact hgl _ hedges _ _
  have key := APrimeSeat1.counting_identity e steps hval hfirst (by rw [hl]; exact hlast) ε
    (by rw [hl]; exact hε)
  rw [hedges] at key
  exact ⟨steps, hmap, hval, key⟩

/-! ### The oriented edge of a tile is determined by the tile -/

/-- Abstract angle named by a real value of the form `angVal`. -/
theorem three_angles_distinct (α : ℝ) (hirr : Irrational (α / Real.pi)) (a b c : Ang)
    (h : angVal α a + angVal α b + angVal α c = Real.pi) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hf := fan_of_cval α hirr (Cnt.add (Cnt.add a.cnt b.cnt) c.cnt) (by
    rw [cval_add, cval_add, cval_ang, cval_ang, cval_ang]; exact h)
  revert hf
  cases a <;> cases b <;> cases c <;> simp [Fan, Cnt.add, Ang.cnt]

/-- Every ordered pair of distinct angles is the `(l, r)` of a unique oriented edge. -/
theorem exists_OE_of_ne (l r : Ang) (h : l ≠ r) : ∃ e : OE, e.l = l ∧ e.r = r := by
  cases l <;> cases r <;> first
    | exact absurd rfl h
    | exact ⟨.ap, rfl, rfl⟩ | exact ⟨.am, rfl, rfl⟩ | exact ⟨.bp, rfl, rfl⟩
    | exact ⟨.bm, rfl, rfl⟩ | exact ⟨.cp, rfl, rfl⟩ | exact ⟨.cm, rfl, rfl⟩

/-- Each corner angle of a tile congruent to the model is `angVal` of some abstract angle. -/
theorem corner_ang (model T : Tri) (hc : model.Congruent T) (α : ℝ)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α) (j : Fin 3) :
    ∃ a : Ang, cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = angVal α a := by
  obtain ⟨k, hk⟩ := congruent_corner_angles hc j
  rw [hk]
  fin_cases k
  · exact ⟨.al, hA0⟩
  · exact ⟨.be, hA1⟩
  · exact ⟨.ga, hA2⟩

/-- **The `OE` of a tile edge.**  For a tile `T` congruent to the model and the edge from `pts k` to
`pts (k+1)`, the local angles at its two ends are `angVal e.l`, `angVal e.r` for an oriented edge `e`. -/
theorem exists_OE (model T : Tri) (hc : model.Congruent T) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α) (k : Fin 3) :
    ∃ e : OE, T.localAngle (T.pts k) = angVal α e.l ∧ T.localAngle (T.pts (k + 1)) = angVal α e.r := by
  obtain ⟨a0, h0⟩ := corner_ang model T hc α hA0 hA1 hA2 k
  obtain ⟨a1, h1⟩ := corner_ang model T hc α hA0 hA1 hA2 (k + 1)
  obtain ⟨a2, h2⟩ := corner_ang model T hc α hA0 hA1 hA2 (k + 2)
  have hsum : angVal α a0 + angVal α a1 + angVal α a2 = Real.pi := by
    rw [← h0, ← h1, ← h2]
    have hs := cornerAngle_sum T
    fin_cases k <;> simp <;> linarith
  have hd := three_angles_distinct α hirr a0 a1 a2 hsum
  obtain ⟨e, hl, hr⟩ := exists_OE_of_ne a0 a1 hd.1
  refine ⟨e, ?_, ?_⟩
  · rw [Tri.localAngle_vertex, h0, hl]
  · rw [Tri.localAngle_vertex, h1, hr]

end Erdos634.Draft.APrimeLeg
