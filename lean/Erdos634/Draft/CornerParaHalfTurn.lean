/-
The half-turn at the corner chord, part 2 of 2.  Adapts `GLCReflect`/`GLCG1` (γ = 2α) and `T30LPi3F6*` (π/3) to the base-β
tile.  The architecture and proof skeleton are redone for the base-β tile; the files below are not imported, to keep the
import cone small.

Adapted from:
  Draft/GLCReflect.lean:90-114     third_vertex_a   (third vertex over an `a`-edge)       -> third_vertex_b
                                   (third vertex over the `b`-edge; derived here from `beta_vertex_flanks`
                                   and `localAngle_of_oppSide` instead of GLC's `tri_orient_a` case analysis)
  Draft/GLCReflect.lean:167-224    corner_chord_reflection_2a, second half (the legs of the two tiles are swapped, hence
                                   `reflect_of_swapped` puts the third vertex of the far tile at `P + Q - X`; the
                                   vertex set and the hulls)                                -> corner_chord_parallelogram
  Draft/T30LPi3F6.lean:211-259     Pi3F6.corner_chord_reflection, second half (same, pi/3)
  Draft/GLCFan.lean `angles_differ_2alpha` -> replaced by `TileAt.congruentDissection_no_double_gamma` (`T_A` already
                                   presents `gamma` at `P`)
Imported and applied:
  Draft/T30LPi3F6Geom.lean:87      Pi3F6.reflect_of_swapped (imports only Mathlib.Tactic and Erdos634.Dissection)
  Draft/CornerParaPartner.lean     corner_chord_partner_data
  Draft/CornerParaCornerAux.lean, CornerParaClamp.lean, CornerParaBase.lean
  TileAt.lean:623                  congruentDissection_no_double_gamma
-/
import Erdos634.Draft.CornerParaPartner
import Erdos634.Draft.T30LPi3F6Geom
import Mathlib.Analysis.Convex.Join

/-!
# The angle interchange and the half-turn at the corner chord, part 2 of 2

Part 1 is `Draft/CornerParaPartner.lean` (the partner tile and its uniqueness).  Adapts `GLCReflect`/`GLCG1` (γ = 2α) and
`T30LPi3F6*` (π/3) to the base-β tile.

Contents.
* `third_vertex_b`: a tile with a `b`-edge `[pts k, pts (k+1)]` has `α, γ` at its ends (one each) and, accordingly,
  legs `|pts(k+1) pts(k+2)|, |pts k pts(k+2)| = (a, c)` or `(c, a)`; the third vertex carries `β`.
* `partner_angles`: the partner `T_3` presents `α` at `P` and `γ` at `Q` (it cannot present `γ` at `P`, where
  `T_A` already does: `no_double_gamma`), with legs `|P R'| = c`, `|Q R'| = a` to its third vertex `R'`.
* `corner_chord_parallelogram`: `Q` is not a target vertex; the third vertex
  of `T_3` is `R = P + Q - A` (point reflection: `Pi3F6.reflect_of_swapped`, the legs being swapped); the vertex set of
  `T_3` is `{P, Q, R}`; `T_3` presents `β` at `R`; `|PR| = c`, `|QR| = a`; and `T_A ∪ T_3` is the hull of the four
  points `A, P, R, Q`, i.e. the parallelogram `A P R Q` with sides `a` and `c`.
* `corner_chord_Q_not_vertex`, `corner_chord_sides_strict`: `Q ∉ range target.pts`, hence `r < 1` in the barycentric data of
  `hC.sides` (the forward range at `Q` stays inside its side).
* `parallelogram_hull_union` (pure convex geometry): for any `A, P, Q`,
  `hull{A,P,Q} ∪ hull{P,Q,P+Q-A} = hull{A,P,P+Q-A,Q}`.

The hypotheses are those of `corner_chord_partner_data` plus a partner `(i3, k3)`, which that theorem produces; at the N = 44
tiling `D44` (`(e, f, s) = (1, 2, 8)`, base corners `0, 1`) they are instantiated in `Draft/CornerParaWitness`
(`D44_corner0_pinned`, `D44_corner1_pinned`: `R = P + Q - A` and `T_A ∪ T_3 = hull {A, P, R, Q}`).
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

/-! ## 1. M10: the third vertex over a `b`-edge -/

/-- **M10 (analogue of `GLCReflect.third_vertex_a`).**  Let `[pts k, pts (k+1)]` be a `b`-edge of the tile `i` (its length is
`sideOpp D.model 1`).  Then `pts (k+2)` carries `β` (its opposite side is the `b`-edge), and the ends of the `b`-edge
carry `α` and `γ` in one of the two orders, with the legs to the third vertex determined by the opposite-side rule
(`a` is opposite `α`, `c` opposite `γ`): `α` at `pts k` gives `|pts(k+1) pts(k+2)| = a`, `|pts k pts(k+2)| = c`;
`γ` at `pts k` gives `|pts(k+1) pts(k+2)| = c`, `|pts k pts(k+2)| = a`. -/
theorem third_vertex_b {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) (hco : Nat.Coprime e f)
    (he : 1 ≤ e) (hef : e < f) (i : Fin N) (k : Fin 3)
    (hk : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1) :
    (((D.tile i).localAngle ((D.tile i).pts k) = α ∧ (D.tile i).localAngle ((D.tile i).pts (k + 1)) = γ ∧
        dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) = sideOpp D.model 0 ∧
        dist ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = sideOpp D.model 2) ∨
      ((D.tile i).localAngle ((D.tile i).pts k) = γ ∧ (D.tile i).localAngle ((D.tile i).pts (k + 1)) = α ∧
        dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = sideOpp D.model 0)) ∧
    (D.tile i).localAngle ((D.tile i).pts (k + 2)) = β := by
  have e1 : k + 2 + 1 = k := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) k
  have e2 : k + 2 + 2 = k + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) k
  have e3 : k + 1 + 1 = k + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) k
  have e4 : k + 1 + 2 = k := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) k
  -- the side opposite `pts (k+2)` is the `b`-edge, so `β` sits at `pts (k+2)`
  have hopp : dist ((D.tile i).pts (k + 2 + 1)) ((D.tile i).pts (k + 2 + 2)) = sideOpp D.model 1 := by
    rw [e1, e2]; exact hk
  have hbeta : (D.tile i).localAngle ((D.tile i).pts (k + 2)) = β :=
    (hM.localAngle_of_oppSide hco he hef i (k + 2)).2.1 hopp
  have hc : cornerAngle ((D.tile i).pts (k + 2 + 1)) ((D.tile i).pts (k + 2)) ((D.tile i).pts (k + 2 + 2)) = β := by
    rw [← Tri.localAngle_vertex]; exact hbeta
  -- the two edges at the `β`-vertex are `{a, c}`
  obtain ⟨hfl, -⟩ := beta_vertex_flanks hM hA i (k + 2) hc
  rw [e1, e2] at hfl
  have hk0 := hM.localAngle_of_oppSide hco he hef i k
  have hk1 := hM.localAngle_of_oppSide hco he hef i (k + 1)
  rw [e3, e4] at hk1
  refine ⟨?_, hbeta⟩
  rcases hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨hk0.1 h2, hk1.2.2 h1, h2, by rw [dist_comm]; exact h1⟩
  · right
    exact ⟨hk0.2.2 h2, hk1.1 h1, h2, by rw [dist_comm]; exact h1⟩

/-! ## 2. C1a + C1b: the partner presents `α` at `P` and `γ` at `Q` -/

/-- **The angle interchange** (C1a + C1b).  Let `T_3 = D.tile i3 ≠ T_A` have the chord `[P, Q]` as its `b`-edge `k3`
(`hlen`, `hend`: the output of `corner_chord_partner_data`).  Its end angles are `{α, γ}` (`third_vertex_b`); it cannot
present `γ` at `P`, where `T_A` already does (`no_double_gamma`, `P` being a non-vertex frontier point); so `T_3`
presents `α` at `P` and `γ` at `Q`, the legs from its third vertex `R'` are `|P R'| = c`, `|Q R'| = a`, and it presents
`β` at `R'`. -/
theorem partner_angles {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) (hco : Nat.Coprime e f)
    (he : 1 ≤ e) (hef : e < f) {k : Fin 3} {iA : Fin N} {P Q : Plane}
    (hC : CornerChord D α β γ k iA P Q) {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3}
    (hlen : dist ((D.tile i3).pts k3) ((D.tile i3).pts (k3 + 1)) = sideOpp D.model 1)
    (hend : ((D.tile i3).pts k3 = P ∧ (D.tile i3).pts (k3 + 1) = Q) ∨
      ((D.tile i3).pts k3 = Q ∧ (D.tile i3).pts (k3 + 1) = P)) :
    (D.tile i3).localAngle P = α ∧ (D.tile i3).localAngle Q = γ ∧
      dist P ((D.tile i3).pts (k3 + 2)) = sideOpp D.model 2 ∧
      dist Q ((D.tile i3).pts (k3 + 2)) = sideOpp D.model 0 ∧
      (D.tile i3).localAngle ((D.tile i3).pts (k3 + 2)) = β := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := angleFacts hA
  have hnoγ : (D.tile i3).localAngle P ≠ γ := fun h2 =>
    Erdos634.Geometry.Dissection.congruentDissection_no_double_gamma D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' hC.P_frontier hC.P_notvert iA i3 hne.symm
      hC.angP h2
  obtain ⟨hcase, hbeta⟩ := third_vertex_b hM hA hco he hef i3 k3 hlen
  rcases hend with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · rw [hP, hQ] at hcase
    rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h1, h2, h4, h3, hbeta⟩
    · exact absurd h1 hnoγ
  · rw [hP, hQ] at hcase
    rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact absurd h2 hnoγ
    · exact ⟨h2, h1, h3, h4, hbeta⟩

/-! ## 3. M11: the union of the two triangles is the parallelogram (pure convex geometry) -/

/-- A nonnegative combination with total weight `1` of three points lies in their convex hull. -/
theorem hull_three_mem {X Y Z x : Plane} {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (huvw : u + v + w = 1) (hx : x = u • X + v • Y + w • Z) : x ∈ convexHull ℝ {X, Y, Z} := by
  have hc := convex_convexHull ℝ ({X, Y, Z} : Set Plane)
  have key := hc.sum_mem (t := (Finset.univ : Finset (Fin 3))) (w := ![u, v, w]) (z := ![X, Y, Z])
    (by intro i _; fin_cases i <;> simp [hu, hv, hw])
    (by simp [Fin.sum_univ_three, huvw])
    (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
  simpa [Fin.sum_univ_three, hx] using key

/-- **M11.**  For ANY three points `A, P, Q`, the triangles `APQ` and `PQR` with `R = P + Q - A` (the point reflection of
`A` through the midpoint of `PQ`) have union the convex hull of the four points `A, P, R, Q`: the parallelogram `A P R Q`
is cut by its diagonal `PQ` into the two triangles. -/
theorem parallelogram_hull_union (A P Q : Plane) :
    convexHull ℝ {A, P, Q} ∪ convexHull ℝ {P, Q, P + Q - A} = convexHull ℝ {A, P, P + Q - A, Q} := by
  ext x
  constructor
  · rintro (hx | hx)
    · refine convexHull_mono ?_ hx
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto
    · refine convexHull_mono ?_ hx
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto
  · intro hx
    rw [convexHull_insert (Set.insert_nonempty _ _), mem_convexJoin] at hx
    obtain ⟨a', ha', y, hy, hxy⟩ := hx
    rw [Set.mem_singleton_iff] at ha'
    rw [ha'] at hxy
    rw [convexHull_insert (Set.insert_nonempty _ _), mem_convexJoin] at hy
    obtain ⟨p', hp', z, hz, hyz⟩ := hy
    rw [Set.mem_singleton_iff] at hp'
    rw [hp'] at hyz
    rw [convexHull_pair] at hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hxy
    obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hyz
    obtain ⟨e', g, he', hg, heg, rfl⟩ := hz
    have hsum : a + b * c + b * d * g + b * d * e' = 1 := by
      linear_combination hab + b * hcd + b * d * heg
    rcases le_or_gt (b * d * e') a with h | h
    · left
      refine hull_three_mem (u := a - b * d * e') (v := b * c + b * d * e') (w := b * d * g + b * d * e')
        (by linarith) (add_nonneg (mul_nonneg hb hc) (mul_nonneg (mul_nonneg hb hd) he'))
        (add_nonneg (mul_nonneg (mul_nonneg hb hd) hg) (mul_nonneg (mul_nonneg hb hd) he')) ?_ ?_
      · linarith
      · module
    · right
      refine hull_three_mem (u := b * c + a) (v := b * d * g + a) (w := b * d * e' - a)
        (add_nonneg (mul_nonneg hb hc) ha) (add_nonneg (mul_nonneg (mul_nonneg hb hd) hg) ha)
        (by linarith) ?_ ?_
      · linarith
      · module

/-! ## 4. C1c + C2 + C3: the parallelogram -/

/-- **`prop:cornerpara`, the corner parallelogram** (plan §2.4).  Let `[P, Q]` be the corner `b`-chord of the corner tile
`T_A` (`hC`), and `T_3 = D.tile i3`, `i3 ≠ iA`, any tile with an edge equal to it (by `corner_chord_partner` there is
exactly one).  Then
* `T_3` presents `α` where `T_A` presents `γ` (at `P`), and `γ` where `T_A` presents `α` (at `Q`);
* `Q` is not a target vertex (it presents `γ`: `not_vertex_of_gamma`);
* the third vertex of `T_3` is `R = P + Q - A` (`T_3` is the half-turn image of `T_A` about the midpoint of the chord);
  the vertex set of `T_3` is `{P, Q, R}`; `T_3` presents `β` at `R`; the opposite sides are equal:
  `|PR| = c = |AQ|`, `|QR| = a = |AP|`;
* `T_A ∪ T_3` is the parallelogram `A P R Q`: the convex hull of the four points (the optional conjunct M11). -/
theorem corner_chord_parallelogram {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q)
    {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3} (h3 : (D.tile i3).edge k3 = segment ℝ P Q) :
    (D.tile i3).localAngle P = α ∧ (D.tile i3).localAngle Q = γ ∧
    Q ∉ Set.range D.target.pts ∧
    ∃ R : Plane, R = P + Q - D.target.pts k ∧ Set.range (D.tile i3).pts = {P, Q, R} ∧
      (D.tile i3).localAngle R = β ∧
      dist P R = sideOpp D.model 2 ∧ dist Q R = sideOpp D.model 0 ∧
      (D.tile iA).carrier ∪ (D.tile i3).carrier = convexHull ℝ {D.target.pts k, P, R, Q} := by
  obtain ⟨φ, c0, i3', k3', -, -, hφP, hφQ, hφA, -, -, hlen, hend, -, hthird, huniq⟩ :=
    corner_chord_partner_data hM hco he hef hC
  obtain ⟨rfl, rfl⟩ := huniq i3 k3 hne h3
  obtain ⟨hαP, hγQ, hPR, hQR, hβR⟩ := partner_angles hM hA hco he hef hC hne hlen hend
  -- the legs are swapped, so the third vertex of `T_3` is the point reflection of `A`
  have hrefl : (D.tile i3).pts (k3 + 2) = P + Q - D.target.pts k :=
    Erdos634.Pi3F6.reflect_of_swapped φ c0 hC.ne_PQ hφP hφQ hφA hthird
      (hPR.trans (hC.lenAQ.symm.trans (dist_comm _ _)))
      (hQR.trans (hC.lenAP.symm.trans (dist_comm _ _)))
  have hrange : Set.range (D.tile i3).pts = {P, Q, P + Q - D.target.pts k} := by
    rw [range_pts_eq (D.tile i3) k3, hrefl]
    rcases hend with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [hP, hQ, Set.insert_comm]
    · rw [hP, hQ]
  refine ⟨hαP, hγQ, not_vertex_of_gamma hM hA hshape hγQ, P + Q - D.target.pts k, rfl, hrange, ?_, ?_, ?_, ?_⟩
  · rw [← hrefl]; exact hβR
  · rw [← hrefl]; exact hPR
  · rw [← hrefl]; exact hQR
  · have hT3 : (D.tile i3).carrier = convexHull ℝ {P, Q, P + Q - D.target.pts k} := by
      show convexHull ℝ (Set.range (D.tile i3).pts) = _
      rw [hrange]
    rw [hC.carrier_eq, hT3]
    exact parallelogram_hull_union _ _ _

/-! ## 5. Consequences for stage CP-4: `Q` is not a target vertex, so `r < 1` -/

/-- `Q` is not a target vertex (the partner presents `γ` there). -/
theorem corner_chord_Q_not_vertex {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    Q ∉ Set.range D.target.pts := by
  obtain ⟨i3, ⟨hne, k3, h3⟩, -⟩ := corner_chord_partner hM hco he hef hC
  exact (corner_chord_parallelogram hM hA hshape hco he hef hC hne h3).2.2.1

/-- **`r < 1`**: with `Q` not a target vertex, the barycentric data of `hC.sides` has `0 < r < 1` (both `P` and `Q` are
strictly inside their sides).  This is what stage CP-4 (the forward tile at `Q`) consumes. -/
theorem corner_chord_sides_strict {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    ∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧ ∃ p r : ℝ, 0 < p ∧ p < 1 ∧ 0 < r ∧ r < 1 ∧
      P = (1 - p) • D.target.pts k + p • D.target.pts w ∧
      Q = (1 - r) • D.target.pts k + r • D.target.pts z :=
  hC.sides_strict (corner_chord_Q_not_vertex hM hA hshape hco he hef hC)

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.third_vertex_b
#print axioms Erdos634.CornerPara.partner_angles
#print axioms Erdos634.CornerPara.hull_three_mem
#print axioms Erdos634.CornerPara.parallelogram_hull_union
#print axioms Erdos634.CornerPara.corner_chord_parallelogram
#print axioms Erdos634.CornerPara.corner_chord_Q_not_vertex
#print axioms Erdos634.CornerPara.corner_chord_sides_strict
