/-
Corner parallelogram, part 2 of 3: the master theorem.  Adapts the assembly theorems of the γ = 2α and π/3 cases to
the base-β tile:
  Draft/GLCG1.lean:208-305        corner_G1      (gamma = 2alpha: the corner tile, its point reflection sharing the corner chord,
                                                  the tile K at each chord end)
  Draft/GLICorner.lean            corner_both    (gamma = 2alpha: the two walls at the corner and their first two chain edges)
  Draft/T30LPi3F6Corner.lean      corner_far_reflection, Draft/T30LPi3F6.lean:167-259 corner_chord_reflection  (pi/3)
and applies (does not copy) the previous modules of this development:
  Draft/CornerParaCorner(+Aux).lean   CornerChord, corner_chord_data, corner_chord_iff
  Draft/CornerParaPartner.lean        corner_chord_partner
  Draft/CornerParaHalfTurn.lean       corner_chord_parallelogram
  Draft/CornerParaChain.lean          walls_exist, corner_first_two_edges
  CornerAnglePermTarget.lean          htarget_of_isosceles, target_apex_angle                    (the isosceles shape of the target)
-/
import Erdos634.Draft.CornerParaChain
import Erdos634.CornerAnglePermTarget

/-!
# Corner parallelogram for the base-β tile, part 2 of 3

The statement.

> Let `T_A` be the tile at a base corner `A`. Its `b`-edge is a chord `[P,Q]` with both endpoints on `∂ABC`, matched by exactly one
> tile `T_3`, which presents `α` where `T_A` presents `γ` and conversely; so `T_A ∪ T_3` is a parallelogram with sides `a` and `c`.
> Consequently the first *two* edges of each of the two sides meeting at `A` lie in `{a, c}`.

`corner_parallelogram` reads, conjunct by conjunct:

* (A) `CornerChord D α β γ k iA P Q`: `T_A = D.tile iA` is the unique tile whose carrier contains the base corner `A = D.target.pts k`
  (corner angle `β`), `A` is its vertex, `P` (the `γ` corner) and `Q` (the `α` corner) are its other two vertices, with `|AP| = a`,
  `|AQ| = c`, `|PQ| = b`, and `P`, `Q` lie on two different target sides at `A` (barycentric form).  Then explicitly, as separate
  conjuncts: `T_A` has an edge of length `b` equal to the segment `[P, Q]` (its `b`-edge is the chord); `P`, `Q` are on `∂ABC`
  (`frontier D.target.carrier`); and `P`, `Q` are strictly inside the two sides (`0 < p, r < 1`, `P = (1-p) A + p V_w`,
  `Q = (1-r) A + r V_z`, `w ≠ z`, `w, z ≠ k`).
* (B) `∃! i3, i3 ≠ iA ∧ ∃ k3, (D.tile i3).edge k3 = segment ℝ P Q`: the chord is matched by exactly one tile other than `T_A`
  (edge equality as sets: `T_3`'s edge is the segment `[P, Q]`; the tiling need not be edge-to-edge).
* (C) for every such partner `T_3`: at `P`,
  `T_A` presents `γ` and `T_3` presents `α`; at `Q`, `T_A` presents `α` and `T_3` presents `γ`; `Q` is not a target vertex; with
  `R = P + Q − A` (so `A + R = P + Q`: `A P R Q` is a parallelogram) the vertex set of
  `T_3` is `{P, Q, R}`, `β` is at `R`, `|PR| = c = |AQ|`, `|QR| = a = |AP|` (opposite sides equal), and
  `T_A ∪ T_3 = hull {A, P, R, Q}` (the union of the two tiles is the parallelogram).
* (D) the two sides meeting at `A` are the walls `wl` from `A` to `V_v` (`v ≠ k`); for each there is a wall and a chain
  (`GLI.exists_wall`, `Wall.exists_chain`), and along every wall and every chain `E` (the edge sequence of the side from the corner:
  `GLI.IsChain` enumerates, in order and without repetition, all tile edges lying on the wall line, the first one starting at `A`):
  `2 ≤ n`, `E 0` belongs to `T_A`, its length is `a` (side through `P`) resp. `c` (side through `Q`), the junction (west end of `E 1`)
  is `P` resp. `Q`, `E 1` has length `a` or `c`, and its owner is a tile other than `T_A` and the partner `T_3` that presents `β` at the
  junction.

Generality.
* More general than the setting of the paper: the model `D.model` has sides `s·(e f, f²−e², f²)` at any scale `s > 0` and any coprime
  `1 ≤ e < f` (the proof never uses the target's size), and `N` is free.  (`D44` has `s = 8`, `(e, f) = (1, 2)`.)
* Extra hypotheses: the angle bundle `MarchSlots.AngleData α β γ` (`0 < α`, `0 < β`, `α ≠ β`, `γ = 2α + β`, `3α + 2β = π`,
  `α ∉ ℚπ`, all consequences of `(e, f)` in the paper's setting, but stated as a bundle here); `BaseBetaModel` (the model's sides
  and angles); `BaseBetaShape` (every corner of the target is `3α` or `β`: a consequence of the target being isosceles with base
  angles `β`, `corner_parallelogram_isosceles`); `Nat.Coprime e f`, `1 ≤ e < f`.
* `E 0 / E 1` are tile edges along the side (`GLI.IsChain`), i.e. the tile edges lying on the side, in order; a tile edge on the side
  need not be the whole side-segment between two junctions of another tile (the tiling is not assumed edge-to-edge).

Every hypothesis of `corner_parallelogram` and of `corner_parallelogram_isosceles` is discharged at the N = 44 tiling `D44`
(`(e, f, s) = (1, 2, 8)`, base corners `0`, `1`) in `Draft/CornerParaWitness.lean`
(`D44_corner_parallelogram`, `D44_corner_parallelogram_isosceles`, `D44_applied_at_both_base_corners`), with the tiles identified and the
numbers pinned (`D44_corner0_pinned`, `D44_corner1_pinned`, `D44_corner0_chains`, `D44_corner1_chains`), and with counterexamples at the apex.
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

/-- **`T_A`'s `b`-edge IS the chord `[P, Q]`**: `T_A` has an edge whose underlying segment is `[P, Q]` and whose length is the
model's `b`-side. -/
theorem corner_chord_b_edge {D : CongruentDissection N} {α β γ : ℝ} {k : Fin 3} {iA : Fin N} {P Q : Plane}
    (hC : CornerChord D α β γ k iA P Q) :
    ∃ e : Fin 3, (D.tile iA).edge e = segment ℝ P Q ∧
      dist ((D.tile iA).pts e) ((D.tile iA).pts (e + 1)) = sideOpp D.model 1 := by
  obtain ⟨j, -, hvert⟩ := hC.vertex
  have e11 : j + 1 + 1 = j + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) j
  refine ⟨j + 1, ?_, ?_⟩
  · rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · show segment ℝ ((D.tile iA).pts (j + 1)) ((D.tile iA).pts (j + 1 + 1)) = _
      rw [e11, hP, hQ]
    · show segment ℝ ((D.tile iA).pts (j + 1)) ((D.tile iA).pts (j + 1 + 1)) = _
      rw [e11, hP, hQ, segment_symm]
  · rw [e11]
    rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hP, ← hQ]; exact hC.lenPQ
    · rw [← hP, ← hQ, dist_comm]; exact hC.lenPQ

/-- **`prop:cornerpara` (Corner parallelogram), for the base-β tile, at ANY scale and any coprime `1 ≤ e < f`.**  See the module
docstring for the conjunct-by-conjunct reading against the paper.  `D` is a congruent dissection whose model has the base-β
sides/angles (`hM`), `hA` the angle bundle, `hshape` the base-β shape of the target, `k` a base corner (angle `β`). -/
theorem corner_parallelogram (D : CongruentDissection N) {e f : ℕ} {s α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∃ (iA : Fin N) (P Q : Plane),
      -- (A) `T_A` the tile at the base corner `A`; its `b`-edge is a chord `[P, Q]` with both endpoints on `∂ABC`
      CornerChord D α β γ k iA P Q ∧
      (∃ e : Fin 3, (D.tile iA).edge e = segment ℝ P Q ∧
        dist ((D.tile iA).pts e) ((D.tile iA).pts (e + 1)) = sideOpp D.model 1) ∧
      P ∈ frontier D.target.carrier ∧ Q ∈ frontier D.target.carrier ∧
      (∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧ ∃ p r : ℝ, 0 < p ∧ p < 1 ∧ 0 < r ∧ r < 1 ∧
        P = (1 - p) • D.target.pts k + p • D.target.pts w ∧
        Q = (1 - r) • D.target.pts k + r • D.target.pts z) ∧
      -- (B) matched by exactly one tile `T_3`
      (∃! i3 : Fin N, i3 ≠ iA ∧ ∃ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q) ∧
      -- (C) `T_3` presents `α` where `T_A` presents `γ` and conversely; `T_A ∪ T_3` is a parallelogram with sides `a`, `c`
      (∀ i3 : Fin N, i3 ≠ iA → ∀ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q →
        ((D.tile iA).localAngle P = γ ∧ (D.tile i3).localAngle P = α) ∧
        ((D.tile iA).localAngle Q = α ∧ (D.tile i3).localAngle Q = γ) ∧ Q ∉ Set.range D.target.pts ∧
        ∃ R : Plane, R = P + Q - D.target.pts k ∧ Set.range (D.tile i3).pts = {P, Q, R} ∧
          (D.tile i3).localAngle R = β ∧ dist P R = sideOpp D.model 2 ∧ dist Q R = sideOpp D.model 0 ∧
          (D.tile iA).carrier ∪ (D.tile i3).carrier = convexHull ℝ {D.target.pts k, P, R, Q}) ∧
      -- (D) the first two edges of each of the two sides meeting at `A` lie in `{a, c}`
      (∀ v : Fin 3, v ≠ k → ∃ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k ∧ wl.b = D.target.pts v ∧
        ∃ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n) ∧
      (∀ i3 : Fin N, i3 ≠ iA → ∀ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q →
        ∀ v : Fin 3, v ≠ k → ∀ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k →
          wl.b = D.target.pts v → ∀ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n →
            2 ≤ n ∧ (E 0).1 = iA ∧ (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧
            ((EdgeWordConversion.len D (E 0) = sideOpp D.model 0 ∧ P ∈ segment ℝ wl.a wl.b ∧
                Placement.edgeWest D.toDissection wl.dir (E 1) = P) ∨
              (EdgeWordConversion.len D (E 0) = sideOpp D.model 2 ∧ Q ∈ segment ℝ wl.a wl.b ∧
                Placement.edgeWest D.toDissection wl.dir (E 1) = Q)) ∧
            (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
              EdgeWordConversion.len D (E 1) = sideOpp D.model 2) ∧
            (D.tile (E 1).1).localAngle (Placement.edgeWest D.toDissection wl.dir (E 1)) = β) := by
  obtain ⟨iA, P, Q, hC⟩ := corner_chord_data D hco he hef hM hA hshape k hcorner
  refine ⟨iA, P, Q, hC, corner_chord_b_edge hC, hC.P_frontier, hC.Q_frontier,
    corner_chord_sides_strict hM hA hshape hco he hef hC, corner_chord_partner hM hco he hef hC,
    fun i3 hne k3 h3 => ?_, fun v hv => walls_exist D k v hv,
    fun i3 hne k3 h3 => corner_first_two_edges hM hA hshape hco he hef hC hne h3⟩
  obtain ⟨hαP, hγQ, hQnv, hR⟩ := corner_chord_parallelogram hM hA hshape hco he hef hC hne h3
  exact ⟨⟨hC.angP, hαP⟩, ⟨hC.angQ, hγQ⟩, hQnv, hR⟩

/-- **`prop:cornerpara` for the paper's own shape of the target.**  The base-β target is isosceles with base angles `β`: for an
apex index `a`, the other two corners `a + 1`, `a + 2` carry `β`; the apex carries `3α` (`target_apex_angle`), so every corner is `3α`
or `β` (`htarget_of_isosceles`: `BaseBetaShape`).  For either base corner `k ∈ {a + 1, a + 2}` the conclusion of
`corner_parallelogram` holds (the first conjunct records the apex angle `3α`). -/
theorem corner_parallelogram_isosceles (D : CongruentDissection N) {e f : ℕ} {s α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) (a : Fin 3)
    (h₁ : cornerAngle (D.target.pts (a + 1 + 1)) (D.target.pts (a + 1)) (D.target.pts (a + 1 + 2)) = β)
    (h₂ : cornerAngle (D.target.pts (a + 2 + 1)) (D.target.pts (a + 2)) (D.target.pts (a + 2 + 2)) = β)
    (k : Fin 3) (hk : k = a + 1 ∨ k = a + 2) :
    cornerAngle (D.target.pts (a + 1)) (D.target.pts a) (D.target.pts (a + 2)) = 3 * α ∧
    ∃ (iA : Fin N) (P Q : Plane),
      CornerChord D α β γ k iA P Q ∧
      (∃ e : Fin 3, (D.tile iA).edge e = segment ℝ P Q ∧
        dist ((D.tile iA).pts e) ((D.tile iA).pts (e + 1)) = sideOpp D.model 1) ∧
      P ∈ frontier D.target.carrier ∧ Q ∈ frontier D.target.carrier ∧
      (∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧ ∃ p r : ℝ, 0 < p ∧ p < 1 ∧ 0 < r ∧ r < 1 ∧
        P = (1 - p) • D.target.pts k + p • D.target.pts w ∧
        Q = (1 - r) • D.target.pts k + r • D.target.pts z) ∧
      (∃! i3 : Fin N, i3 ≠ iA ∧ ∃ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q) ∧
      (∀ i3 : Fin N, i3 ≠ iA → ∀ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q →
        ((D.tile iA).localAngle P = γ ∧ (D.tile i3).localAngle P = α) ∧
        ((D.tile iA).localAngle Q = α ∧ (D.tile i3).localAngle Q = γ) ∧ Q ∉ Set.range D.target.pts ∧
        ∃ R : Plane, R = P + Q - D.target.pts k ∧ Set.range (D.tile i3).pts = {P, Q, R} ∧
          (D.tile i3).localAngle R = β ∧ dist P R = sideOpp D.model 2 ∧ dist Q R = sideOpp D.model 0 ∧
          (D.tile iA).carrier ∪ (D.tile i3).carrier = convexHull ℝ {D.target.pts k, P, R, Q}) ∧
      (∀ v : Fin 3, v ≠ k → ∃ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k ∧ wl.b = D.target.pts v ∧
        ∃ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n) ∧
      (∀ i3 : Fin N, i3 ≠ iA → ∀ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q →
        ∀ v : Fin 3, v ≠ k → ∀ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k →
          wl.b = D.target.pts v → ∀ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n →
            2 ≤ n ∧ (E 0).1 = iA ∧ (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧
            ((EdgeWordConversion.len D (E 0) = sideOpp D.model 0 ∧ P ∈ segment ℝ wl.a wl.b ∧
                Placement.edgeWest D.toDissection wl.dir (E 1) = P) ∨
              (EdgeWordConversion.len D (E 0) = sideOpp D.model 2 ∧ Q ∈ segment ℝ wl.a wl.b ∧
                Placement.edgeWest D.toDissection wl.dir (E 1) = Q)) ∧
            (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
              EdgeWordConversion.len D (E 1) = sideOpp D.model 2) ∧
            (D.tile (E 1).1).localAngle (Placement.edgeWest D.toDissection wl.dir (E 1)) = β) := by
  have hshape : BaseBetaShape D.target α β := htarget_of_isosceles D.target hA.hrel a h₁ h₂
  refine ⟨target_apex_angle D.target hA.hrel a h₁ h₂, ?_⟩
  rcases hk with rfl | rfl
  · exact corner_parallelogram D hco he hef hM hA hshape _ h₁
  · exact corner_parallelogram D hco he hef hM hA hshape _ h₂

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.corner_chord_b_edge
#print axioms Erdos634.CornerPara.corner_parallelogram
#print axioms Erdos634.CornerPara.corner_parallelogram_isosceles
