import Erdos634.Draft.ThmDCount

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', D2 module D: `apex_tiles_distinct`, proved  

Closes the one geometric hypothesis `hne : lastTile t0 r ≠ t0'` of `ThmDCount.apex_leg_word_of_legs`.
A tile with a non-degenerate edge along each of the two sides at the apex `B = pts (i+1)` has its three vertices
`B`, `P ∈ [A,B)`, `Q ∈ (B,C]`, so its angle at `B` is the corner angle `π - 2α` of the target (scaling of the arms);
but a tile angle is `α` or `π - 3α` (the ends of a leg), contradiction for `0 < α`, `3α < π`.
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.Draft.APrimeLegBuild

theorem fin3_p1p1 : ∀ i : Fin 3, i + 1 + 1 = i + 2 := by decide
theorem fin3_p1p2 : ∀ i : Fin 3, i + 1 + 2 = i := by decide

/-- a point of both sides at the vertex `pts (i+1)` is that vertex -/
theorem eq_apex_of_two_sides (Tg : Tri) (i : Fin 3) {P : Plane}
    (h1 : P ∈ segment ℝ (Tg.pts i) (Tg.pts (i + 1)))
    (h2 : P ∈ segment ℝ (Tg.pts (i + 1)) (Tg.pts (i + 1 + 1))) : P = Tg.pts (i + 1) := by
  have c1 : Tg.basis.coord (i + 2) P = 0 := Tg.coord_eq_zero_of_mem_edge i h1
  have c2 : Tg.basis.coord (i + 1 + 2) P = 0 := Tg.coord_eq_zero_of_mem_edge (i + 1) h2
  rw [fin3_p1p2] at c2
  have hne : i + 2 ≠ i := (by decide : ∀ i : Fin 3, i + 2 ≠ i) i
  obtain ⟨m, hm⟩ := Tg.eq_vertex_of_two_coords_zero hne c1 c2
  have hb : ∀ j : Fin 3, Tg.basis.coord j (Tg.pts m) = if j = m then 1 else 0 := by
    intro j
    have : Tg.pts m = (Tg.basis : Fin 3 → Plane) m := rfl
    rw [this, AffineBasis.coord_apply]
  have e1 := hb (i + 2); have e2 := hb i
  rw [← hm, c1] at e1
  rw [← hm, c2] at e2
  have n1 : m ≠ i + 2 := fun h => by rw [if_pos h.symm] at e1; exact one_ne_zero e1.symm
  have n2 : m ≠ i := fun h => by rw [if_pos h.symm] at e2; exact one_ne_zero e2.symm
  have : m = i + 1 := (by decide : ∀ i m : Fin 3, m ≠ i + 2 → m ≠ i → m = i + 1) i m n1 n2
  rw [hm, this]

/-- a point of `[A,B]` other than `B` is `B + t (A - B)`, `t > 0` -/
theorem seg_left_dir {A B P : Plane} (h : P ∈ segment ℝ A B) (hP : P ≠ B) :
    ∃ t : ℝ, 0 < t ∧ P - B = t • (A - B) := by
  obtain ⟨a, b, ha, hb, hab, hP'⟩ := h
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine ⟨a, ?_, ?_⟩
  · rcases ha.lt_or_eq with h0 | h0
    · exact h0
    · exfalso; apply hP; rw [← hP', ← h0]; simp
  · rw [← hP']; module

/-- a point of `[B,C]` other than `B` is `B + t (C - B)`, `t > 0` -/
theorem seg_right_dir {B C Q : Plane} (h : Q ∈ segment ℝ B C) (hQ : Q ≠ B) :
    ∃ t : ℝ, 0 < t ∧ Q - B = t • (C - B) := by
  obtain ⟨a, b, ha, hb, hab, hQ'⟩ := h
  have ha' : a = 1 - b := by linarith
  subst ha'
  refine ⟨b, ?_, ?_⟩
  · rcases hb.lt_or_eq with h0 | h0
    · exact h0
    · exfalso; apply hQ; rw [← hQ', ← h0]; simp
  · rw [← hQ']; module

/-- **A tile with an edge along each side at the apex has the corner angle there.** -/
theorem apex_tile_angle (Tg T : Tri) (i : Fin 3) (j k k' : Fin 3)
    (hj : T.pts j = Tg.pts (i + 1))
    (hk : T.pts k ∈ segment ℝ (Tg.pts i) (Tg.pts (i + 1))) (hkB : T.pts k ≠ Tg.pts (i + 1))
    (hk' : T.pts k' ∈ segment ℝ (Tg.pts (i + 1)) (Tg.pts (i + 1 + 1)))
    (hk'B : T.pts k' ≠ Tg.pts (i + 1)) :
    T.localAngle (Tg.pts (i + 1)) = cornerAngle (Tg.pts (i + 1 + 1)) (Tg.pts (i + 1)) (Tg.pts (i + 1 + 2)) := by
  have kj : k ≠ j := fun h => hkB (h ▸ hj)
  have k'j : k' ≠ j := fun h => hk'B (h ▸ hj)
  have kk' : k ≠ k' := by
    intro h
    subst h
    exact hkB (eq_apex_of_two_sides Tg i hk hk')
  obtain ⟨t, ht, hPt⟩ := seg_left_dir hk hkB
  obtain ⟨s, hs, hQs⟩ := seg_right_dir hk' hk'B
  have hang : InnerProductGeometry.angle (T.pts k - Tg.pts (i + 1)) (T.pts k' - Tg.pts (i + 1)) =
      InnerProductGeometry.angle (Tg.pts i - Tg.pts (i + 1)) (Tg.pts (i + 1 + 1) - Tg.pts (i + 1)) := by
    rw [hPt, hQs, InnerProductGeometry.angle_smul_left_of_pos _ _ ht,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hs]
  have ho : (j + 1 = k ∧ j + 2 = k') ∨ (j + 1 = k' ∧ j + 2 = k) :=
    (by decide : ∀ j k k' : Fin 3, k ≠ j → k' ≠ j → k ≠ k' →
      (j + 1 = k ∧ j + 2 = k') ∨ (j + 1 = k' ∧ j + 2 = k)) j k k' kj k'j kk'
  rw [← hj, Tri.localAngle_vertex, hj, fin3_p1p2]
  simp only [cornerAngle, EuclideanGeometry.angle, vsub_eq_sub]
  rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, ← hj, hj, hang, InnerProductGeometry.angle_comm]
  · rw [h1, h2, ← hj, hj, InnerProductGeometry.angle_comm (T.pts k' - _), hang, InnerProductGeometry.angle_comm]

/-- **`apex_tiles_distinct`.**  The last tile of the leg along side `i` and the first tile of the leg along side `i+1`
are different tiles when the target corner between them is `π - 2α` (`0 < α`, `3α < π`). -/
theorem apex_tiles_distinct {N : ℕ} (D : Dissection N) (model : Tri) (α : ℝ)
    (h3α : 3 * α < Real.pi) (hα : 0 < α) (i : Fin 3)
    (hcApex : cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1))
      (D.target.pts (i + 1 + 2)) = Real.pi - 2 * α)
    {t0 t0' : Fin N} {e0 e0' : OE} {r r' : List (LegStep N)}
    (h1 : LegFacts D model α i t0 e0 r) (h2 : LegFacts D model α (i + 1) t0' e0' r') :
    lastTile t0 r ≠ t0' := by
  intro heq
  obtain ⟨-, -, hl1, -, hlast1, -, -, -, hlo1⟩ := h1
  obtain ⟨-, -, -, -, -, -, -, hfo2, -⟩ := h2
  obtain ⟨j, k, hjk, hj, hk, hkB⟩ := hlo1
  obtain ⟨j', k', hjk', hj', hk', hk'B⟩ := hfo2
  rw [heq] at hl1 hj hk hkB
  have hang := apex_tile_angle D.target (D.tile t0') i j k k' hj hk hkB hk' hk'B
  rw [hcApex, hl1] at hang
  rcases hlast1 with h | h <;> rw [h] at hang <;> simp only [angVal] at hang
  · linarith
  · linarith

/-- **D2, assembled, without the `hne` hypothesis**: the alpha-apex leg has a `b`-edge and carries the word of its side. -/
theorem apex_leg_word_of_legs' {N : ℕ} (D : Dissection N) (model : Tri)
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
    (h1 : LegFacts D model α i t0 e0 r) (h2 : LegFacts D model α (i + 1) t0' e0' r') :
    ∃ P Q R : ℕ, P * a + Q * b + R * c = L ∧ 1 ≤ Q :=
  apex_leg_word_of_legs D model hcong α hirr hA0 hA1 hA2 hα h3α i hcA hcApex hcB a b c L hs0 hs1 hs2 hL1 hL2
    h1 h2 (apex_tiles_distinct D model α h3α hα i hcApex h1 h2)

end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.apex_tiles_distinct
#print axioms Erdos634.Draft.ThmD.apex_leg_word_of_legs'
