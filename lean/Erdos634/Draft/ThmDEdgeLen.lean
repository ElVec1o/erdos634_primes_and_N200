import Erdos634.Draft.APrimeLegBuild
import Erdos634.CornerBaseEdgesReal
import Erdos634.CornerAnglePermTarget

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', D2 module A: the letter of an oriented edge is its length  (DRAFT, NOT COMPILED, )

Written 2026-10-18 while the Lean slot was busy; never run through `lake`/`lean`.  Not in `All`.

Setting (as `APrimeLeg`, `APrimeLegBuild`): a model `Tri` with corner angles `α, π - 3α, 2α` at its vertices
`0, 1, 2` (so the sides opposite are `a = sideOpp model 0`, `b = sideOpp model 1`, `c = sideOpp model 2`), tiles
congruent to it.  An oriented edge `o : OE` of a tile edge records the pair of angles `(o.l, o.r)` at its two ends;
the third angle sits at the opposite vertex, and the edge is the side OPPOSITE that third angle.

* `ang_ne`, `angVal_inj` : the three values `α, π - 3α, 2α` are pairwise distinct (irrationality of `α/π`).
* `third`, `lenOpp`, `wlen` : the third angle of a pair, the length opposite an angle, the length of an `OE`
  (`wlen model .ap = a`, `.bp = b`, `.cp = c`, same for the mirrored letters).
* `opp_len` : a tile vertex with corner angle `angVal a` has opposite side `lenOpp model a`
  (from `CornerBaseEdgesReal.congruent_opposite_side`).
* `edge_len_eq` : for a tile edge `[pts k, pts (k+1)]` with local angles `angVal x`, `angVal y` at its ends,
  `dist (pts k) (pts (k+1)) = lenOpp model (third x y)`.
* `sum_wlen` : `Σ wlen over a list of OE = #A·a + #B·b + #C·c`.

This is the missing "edge list <-> side_partition" half of `thmD_lean.md` (D2): `side_walk_abc_nat` could not be tied
to `cntLetter isA/isB/isC (legEdges e0 r)` because a `RealLeg` records angles, not lengths.  See `ThmDLegLen.lean`
for the version of `exists_chain_leg` that also records the length sum.
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

/-! ### 1. The three angle values are distinct -/

theorem ang_ne (α : ℝ) (hirr : Irrational (α / Real.pi)) (hα : 0 < α) :
    α ≠ Real.pi - 3 * α ∧ α ≠ 2 * α ∧ Real.pi - 3 * α ≠ 2 * α := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hirr
    refine ⟨(1 / 4 : ℚ), ?_⟩
    push_cast
    rw [eq_div_iff hpi]
    linarith
  · intro h
    linarith
  · intro h
    apply hirr
    refine ⟨(1 / 5 : ℚ), ?_⟩
    push_cast
    rw [eq_div_iff hpi]
    linarith

theorem angVal_inj (α : ℝ) (hirr : Irrational (α / Real.pi)) (hα : 0 < α) {a b : Ang}
    (h : angVal α a = angVal α b) : a = b := by
  obtain ⟨h1, h2, h3⟩ := ang_ne α hirr hα
  cases a <;> cases b <;> simp only [angVal] at h <;>
    first
    | rfl
    | (exfalso
       first
       | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm | exact h3 h | exact h3 h.symm)

/-! ### 2. Third angle, opposite length, length of an oriented edge -/

/-- the angle that completes `x, y` to `{α, β, γ}` (arbitrary on equal arguments) -/
def third : Ang → Ang → Ang
  | .al, .be => .ga
  | .be, .al => .ga
  | .be, .ga => .al
  | .ga, .be => .al
  | .al, .ga => .be
  | .ga, .al => .be
  | _, _ => .al

theorem third_comm (x y : Ang) : third x y = third y x := by
  cases x <;> cases y <;> rfl

/-- the length of the side of the model opposite the angle `a` -/
noncomputable def lenOpp (model : Tri) : Ang → ℝ
  | .al => sideOpp model 0
  | .be => sideOpp model 1
  | .ga => sideOpp model 2

/-- the length of an oriented edge (the side opposite the third angle) -/
noncomputable def wlen (model : Tri) (o : OE) : ℝ := lenOpp model (third o.l o.r)

theorem wlen_a (model : Tri) (o : OE) (h : isA o = true) : wlen model o = sideOpp model 0 := by
  cases o <;> simp_all [wlen, lenOpp, third, OE.l, OE.r, isA]

theorem wlen_b (model : Tri) (o : OE) (h : isB o = true) : wlen model o = sideOpp model 1 := by
  cases o <;> simp_all [wlen, lenOpp, third, OE.l, OE.r, isB]

theorem wlen_c (model : Tri) (o : OE) (h : isC o = true) : wlen model o = sideOpp model 2 := by
  cases o <;> simp_all [wlen, lenOpp, third, OE.l, OE.r, isC]

/-- **Sum of lengths along an edge list** -/
theorem sum_wlen (model : Tri) (es : List OE) :
    (es.map (wlen model)).sum =
      (cntLetter isA es : ℝ) * sideOpp model 0 + (cntLetter isB es : ℝ) * sideOpp model 1 +
        (cntLetter isC es : ℝ) * sideOpp model 2 := by
  induction es with
  | nil => simp [cntLetter]
  | cons e t ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [cntLetter, List.filter_cons]
    cases e <;> simp [wlen, lenOpp, third, OE.l, OE.r, isA, isB, isC] <;> ring

/-! ### 3. Opposite side of a corner of a tile -/

theorem fin3_add2_add1 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
theorem fin3_add2_add2 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide

/-- A vertex `j` of a tile congruent to the model with corner angle `angVal a` has opposite side
`lenOpp model a`. -/
theorem opp_len (model T : Tri) (hc : model.Congruent T) (α : ℝ)
    (hirr : Irrational (α / Real.pi)) (hα : 0 < α)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (j : Fin 3) (a : Ang)
    (h : cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = angVal α a) :
    dist (T.pts (j + 1)) (T.pts (j + 2)) = lenOpp model a := by
  obtain ⟨k', hk', hside⟩ := Erdos634.CornerBaseEdgesReal.congruent_opposite_side hc j
  have hmod : cornerAngle (model.pts (k' + 1)) (model.pts k') (model.pts (k' + 2)) = angVal α a :=
    hk'.symm.trans h
  rw [← hside]
  have hall : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hall k' with rfl | rfl | rfl
  · simp only [show ((0 : Fin 3) + 1) = 1 from rfl, show ((0 : Fin 3) + 2) = 2 from rfl] at hmod ⊢
    rw [hA0] at hmod
    have ha : Ang.al = a := angVal_inj α hirr hα hmod
    subst ha
    rfl
  · simp only [show ((1 : Fin 3) + 1) = 2 from rfl, show ((1 : Fin 3) + 2) = 0 from rfl] at hmod ⊢
    rw [hA1] at hmod
    have ha : Ang.be = a := angVal_inj α hirr hα hmod
    subst ha
    rfl
  · simp only [show ((2 : Fin 3) + 1) = 0 from rfl, show ((2 : Fin 3) + 2) = 1 from rfl] at hmod ⊢
    rw [hA2] at hmod
    have ha : Ang.ga = a := angVal_inj α hirr hα hmod
    subst ha
    rfl

/-- **The length of a tile edge from the angles at its two ends.** -/
theorem edge_len_eq (model T : Tri) (hc : model.Congruent T) (α : ℝ)
    (hirr : Irrational (α / Real.pi)) (hα : 0 < α)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (k : Fin 3) (x y : Ang)
    (hx : T.localAngle (T.pts k) = angVal α x) (hy : T.localAngle (T.pts (k + 1)) = angVal α y) :
    dist (T.pts k) (T.pts (k + 1)) = lenOpp model (third x y) := by
  obtain ⟨a0, h0⟩ := corner_ang model T hc α hA0 hA1 hA2 k
  obtain ⟨a1, h1⟩ := corner_ang model T hc α hA0 hA1 hA2 (k + 1)
  obtain ⟨a2, h2⟩ := corner_ang model T hc α hA0 hA1 hA2 (k + 2)
  have hx' : cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = angVal α x :=
    (Tri.localAngle_vertex T k).symm.trans hx
  have hy' : cornerAngle (T.pts (k + 1 + 1)) (T.pts (k + 1)) (T.pts (k + 1 + 2)) = angVal α y :=
    (Tri.localAngle_vertex T (k + 1)).symm.trans hy
  have ex : a0 = x := angVal_inj α hirr hα (h0.symm.trans hx')
  have ey : a1 = y := angVal_inj α hirr hα (h1.symm.trans hy')
  have hsum : angVal α a0 + angVal α a1 + angVal α a2 = Real.pi := by
    have hs := Erdos634.Geometry.cornerAngle_sum_indexed T k
    rw [h0, h1, h2] at hs
    exact hs
  have hd := three_angles_distinct α hirr a0 a1 a2 hsum
  obtain ⟨hd01, hd02, hd12⟩ := hd
  have h3 : a2 = third a0 a1 := by
    cases a0 <;> cases a1 <;> cases a2 <;>
      first
      | rfl
      | exact absurd rfl hd01
      | exact absurd rfl hd02
      | exact absurd rfl hd12
  have hlen := opp_len model T hc α hirr hα hA0 hA1 hA2 (k + 2) a2 h2
  rw [fin3_add2_add1 k, fin3_add2_add2 k] at hlen
  rw [hlen, h3, ex, ey]

/-- The reversed reading (`OE` of a reversed edge): `edge_len_eq` with the roles of the two ends exchanged and
`third_comm`.  Used in `ThmDLegLen` for the case where the edge is traversed against its stored orientation. -/
theorem edge_len_eq_rev (model T : Tri) (hc : model.Congruent T) (α : ℝ)
    (hirr : Irrational (α / Real.pi)) (hα : 0 < α)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (k : Fin 3) (o : OE)
    (hx : T.localAngle (T.pts (k + 1)) = angVal α o.l) (hy : T.localAngle (T.pts k) = angVal α o.r) :
    dist (T.pts k) (T.pts (k + 1)) = wlen model o := by
  have h := edge_len_eq model T hc α hirr hα hA0 hA1 hA2 k o.r o.l hy hx
  rw [h, wlen, third_comm]

theorem edge_len_eq_fwd (model T : Tri) (hc : model.Congruent T) (α : ℝ)
    (hirr : Irrational (α / Real.pi)) (hα : 0 < α)
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (k : Fin 3) (o : OE)
    (hx : T.localAngle (T.pts k) = angVal α o.l) (hy : T.localAngle (T.pts (k + 1)) = angVal α o.r) :
    dist (T.pts k) (T.pts (k + 1)) = wlen model o :=
  edge_len_eq model T hc α hirr hα hA0 hA1 hA2 k o.l o.r hx hy

end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.edge_len_eq_fwd
#print axioms Erdos634.Draft.ThmD.sum_wlen
