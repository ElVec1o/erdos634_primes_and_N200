/-
The corner tile of a base-β dissection and its `b`-chord, part 1 of 2.  Adapts the pipeline of `GLCCorner` (γ = 2α)
and `T30LPi3F6Corner` (π/3) to the base-β tile.  The architecture and proof skeleton are redone for the base-β tile; the
files below are not imported, to keep the import cone small.

Adapted from:
  Draft/GLCCorner.lean:171-203   aux_reflection_2a (spans 156-215)  (hPform/hQform barycentric forms; `p < 1`, `r < 1`
                                 from the barycentric coordinate at the corner)  -> param_le_one, corner_chord_of_rays
  Draft/GLCCorner.lean:218-305   corner_far_reflection_2a  (the four-way split: SameRay order x which flank is
                                 which, collapsed to one symmetric core lemma)  -> corner_chord_of_rays, corner_chord_data
  Draft/T30LPi3F6Corner.lean:33-93, 103-177   Pi3F6.aux_reflection / Pi3F6.corner_far_reflection (same split, pi/3)
Imported and applied:
  Draft/H1eCLAlign.lean:33       corner_aligned  (the corner tile's two edges at the corner lie along the two target sides)
  Draft/CornerParaBase.lean, Draft/CornerParaClamp.lean
-/
import Erdos634.Draft.CornerParaClamp
import Erdos634.Draft.H1eCLAlign

/-!
# The corner tile of a base-β dissection and its `b`-chord

Part 1 of 2; part 2 is `Draft/CornerParaCornerAux.lean` (companion lemmas of the structure and the packaged clamp data).
Adapts `GLCCorner` (γ = 2α) and `T30LPi3F6Corner` (π/3) to the base-β tile.

Contents.
* `CornerChord D α β γ k iA P Q`: `A = D.target.pts k` is a base corner (corner angle `β`);
  `T_A = D.tile iA` is the unique tile at `A`; `A = pts j` and `{P, Q} = {pts (j+1), pts (j+2)}`, with `T_A`
  presenting `γ` at `P` and `α` at `Q`; `|AP| = a`, `|AQ| = c`, `|PQ| = b`; `P`, `Q` lie on the two distinct
  target sides at `A` in barycentric form `P = (1-p) A + p V_w`, `Q = (1-r) A + r V_z`, `p ∈ (0,1)`,
  `r ∈ (0,1]` (`Q` may a priori be the far vertex `V_z`; `corner_chord_Q_not_vertex` shows it is not); `P` is not a target vertex.
* `corner_chord_data`:
  `∃ iA P Q, CornerChord D α β γ k iA P Q` at every base corner `k`.  The four cases (SameRay order x which flank is
  which) collapse to one symmetric lemma `corner_chord_of_rays` (generic `P Q`, generic target indices `w z`).

`CornerChord` is the conclusion of `corner_chord_data`, whose hypotheses are the bundles `BaseBetaModel`, `BaseBetaShape`,
`MarchSlots.AngleData` plus a base corner.  These are witnessed at the N = 44 tiling `Tiling44Bridge.D44`
(`(e, f, s) = (1, 2, 8)`, corners `0, 1`) by the modules `Draft/CornerParaWitnessAux` (`D44_corner0_chord`, `D44_corner1_chord`)
and `Draft/CornerParaWitness` (`D44_corner0_pinned`, `D44_corner1_pinned`: chord lengths `16, 32, 24`, the tiles identified).
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

/-! ## 1. The structure -/

/-- **The corner chord.**  `A = D.target.pts k` is a base corner; `T_A = D.tile iA` is the unique tile at `A`; `A` is
its vertex `j`; `{P, Q}` are its other two vertices, `P` the one carrying `γ`, `Q` the one carrying `α`.  The chord
`[P, Q]` is `T_A`'s `b`-edge; `P` and `Q` lie on the two distinct target sides at `A`, in barycentric form
(`w, z` the two target indices other than `k`).  `Q = V_z` is allowed here (`r ≤ 1`; CP-3 excludes it); `p < 1`
holds because `P` presents `γ`, hence is not a target vertex. -/
structure CornerChord {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ) (k : Fin 3) (iA : Fin N)
    (P Q : Plane) : Prop where
  /-- `T_A` is the only tile whose carrier contains `A`. -/
  unique : ∀ i : Fin N, D.target.pts k ∈ (D.tile i).carrier → i = iA
  /-- `A` is the vertex `j` of `T_A`, and `{P, Q}` are the two other vertices (in either order). -/
  vertex : ∃ j : Fin 3, D.target.pts k = (D.tile iA).pts j ∧
    ((P = (D.tile iA).pts (j + 1) ∧ Q = (D.tile iA).pts (j + 2)) ∨
      (P = (D.tile iA).pts (j + 2) ∧ Q = (D.tile iA).pts (j + 1)))
  angA : (D.tile iA).localAngle (D.target.pts k) = β
  angP : (D.tile iA).localAngle P = γ
  angQ : (D.tile iA).localAngle Q = α
  /-- the `a`-edge `[A, P]` (it joins `β` and `γ`) -/
  lenAP : dist (D.target.pts k) P = sideOpp D.model 0
  /-- the `c`-edge `[A, Q]` (it joins `α` and `β`) -/
  lenAQ : dist (D.target.pts k) Q = sideOpp D.model 2
  /-- the `b`-edge `[P, Q]` (it joins `α` and `γ`) -/
  lenPQ : dist P Q = sideOpp D.model 1
  /-- `P` and `Q` lie on the two distinct target sides at `A`. -/
  sides : ∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧ ∃ p r : ℝ, 0 < p ∧ p < 1 ∧ 0 < r ∧ r ≤ 1 ∧
    P = (1 - p) • D.target.pts k + p • D.target.pts w ∧
    Q = (1 - r) • D.target.pts k + r • D.target.pts z
  /-- `P` presents `γ`, so it is not a target vertex. -/
  P_notvert : P ∉ Set.range D.target.pts

/-! ## 2. Small lemmas -/

/-- Every model side is positive. -/
theorem sideOpp_pos' (T : Tri) (m : Fin 3) : 0 < sideOpp T m := by
  unfold sideOpp
  exact dist_pos.mpr (pts_ne T ((by decide : ∀ m : Fin 3, m + 1 ≠ m + 2) m))

/-- **Barycentric bound** (the `p ≤ 1` half of `GLCCorner.aux_reflection_2a:186-194`): a point of the triangle of the form
`(1 - p) T_v + p T_w` with `v ≠ w` has `p ≤ 1` (its coordinate at `v` is `1 - p ≥ 0`). -/
theorem param_le_one (T : Tri) {v w : Fin 3} (hvw : v ≠ w) {X : Plane} {p : ℝ}
    (hX : X ∈ T.carrier) (hform : X = (1 - p) • T.pts v + p • T.pts w) : p ≤ 1 := by
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  rw [T.carrier_eq_nonneg_coord] at hX
  have h := hX v
  rw [hform, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at h
  simp [hvw] at h
  linarith

/-! ## 3. The symmetric core: generic `P Q`, generic target indices `w z` -/

/-- **The symmetric core of `corner_chord_data`.**  Let `T_A = D.tile iA` be the unique tile at `A = D.target.pts k`,
`A` its vertex `j`; let `P, Q` be its other two vertices (either order), with `T_A` presenting `γ` at `P` and `α` at `Q`,
`|AP| = a`, `|AQ| = c`, `|PQ| = b`.  If `P - A` and `Q - A` are on the same rays as `V_w - A` and `V_z - A` for two
distinct target indices `w, z ≠ k`, then `CornerChord`.  (Port of the common part of the two branches of
`GLCCorner.corner_far_reflection_2a:280-305`: the four cases of the original collapse to calls of this lemma.) -/
theorem corner_chord_of_rays {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β)
    {k : Fin 3} {iA : Fin N} {j : Fin 3} {P Q : Plane} {w z : Fin 3}
    (huniq : ∀ i : Fin N, D.target.pts k ∈ (D.tile i).carrier → i = iA)
    (hjk : D.target.pts k = (D.tile iA).pts j)
    (hvert : (P = (D.tile iA).pts (j + 1) ∧ Q = (D.tile iA).pts (j + 2)) ∨
      (P = (D.tile iA).pts (j + 2) ∧ Q = (D.tile iA).pts (j + 1)))
    (hangA : (D.tile iA).localAngle (D.target.pts k) = β)
    (hangP : (D.tile iA).localAngle P = γ) (hangQ : (D.tile iA).localAngle Q = α)
    (hAP : dist (D.target.pts k) P = sideOpp D.model 0)
    (hAQ : dist (D.target.pts k) Q = sideOpp D.model 2)
    (hPQ : dist P Q = sideOpp D.model 1)
    (hkw : w ≠ k) (hkz : z ≠ k) (hwz : w ≠ z)
    (hSP : SameRay ℝ (D.target.pts w - D.target.pts k) (P - D.target.pts k))
    (hSQ : SameRay ℝ (D.target.pts z - D.target.pts k) (Q - D.target.pts k)) :
    CornerChord D α β γ k iA P Q := by
  have hPA : P - D.target.pts k ≠ 0 := by
    intro h
    have h' : P = D.target.pts k := sub_eq_zero.mp h
    rw [h', dist_self] at hAP
    exact (sideOpp_pos' D.model 0).ne hAP
  have hQA : Q - D.target.pts k ≠ 0 := by
    intro h
    have h' : Q = D.target.pts k := sub_eq_zero.mp h
    rw [h', dist_self] at hAQ
    exact (sideOpp_pos' D.model 2).ne hAQ
  have hwA : D.target.pts w - D.target.pts k ≠ 0 :=
    sub_ne_zero.mpr fun h => hkw (D.target.indep.injective h)
  have hzA : D.target.pts z - D.target.pts k ≠ 0 :=
    sub_ne_zero.mpr fun h => hkz (D.target.indep.injective h)
  obtain ⟨p, hp0, hp⟩ := rayparam hwA hPA hSP
  obtain ⟨r, hr0, hr⟩ := rayparam hzA hQA hSQ
  have hPform : P = (1 - p) • D.target.pts k + p • D.target.pts w := by
    have : P = D.target.pts k + p • (D.target.pts w - D.target.pts k) := by rw [← hp]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hQform : Q = (1 - r) • D.target.pts k + r • D.target.pts z := by
    have : Q = D.target.pts k + r • (D.target.pts z - D.target.pts k) := by rw [← hr]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hPmem : P ∈ D.target.carrier := by
    rcases hvert with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact tile_subset_target D.toDissection iA (subset_convexHull ℝ _ ⟨j + 1, rfl⟩)
    · rw [h1]; exact tile_subset_target D.toDissection iA (subset_convexHull ℝ _ ⟨j + 2, rfl⟩)
  have hQmem : Q ∈ D.target.carrier := by
    rcases hvert with ⟨-, h1⟩ | ⟨-, h1⟩
    · rw [h1]; exact tile_subset_target D.toDissection iA (subset_convexHull ℝ _ ⟨j + 2, rfl⟩)
    · rw [h1]; exact tile_subset_target D.toDissection iA (subset_convexHull ℝ _ ⟨j + 1, rfl⟩)
  have hPnv : P ∉ Set.range D.target.pts := not_vertex_of_gamma hM hA hshape hangP
  have hp1 : p < 1 := by
    refine lt_of_le_of_ne (param_le_one D.target hkw.symm hPmem hPform) ?_
    rintro rfl
    exact hPnv ⟨w, by rw [hPform]; simp⟩
  have hr1 : r ≤ 1 := param_le_one D.target hkz.symm hQmem hQform
  exact ⟨huniq, ⟨j, hjk, hvert⟩, hangA, hangP, hangQ, hAP, hAQ, hPQ,
    ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, hr1, hPform, hQform⟩, hPnv⟩

/-! ## 4. Step A: the corner tile and its chord -/

/-- **Step A (A1-A6).**  At a base corner `A = D.target.pts k` (corner angle `β`) of a base-β dissection (model of
scale `s`, coprime `1 ≤ e < f`, the base-β shape of the target) there are a tile `iA` (the unique tile at `A`) and
two points `P, Q` forming a `CornerChord`.  Ingredients: `base_corner_tile_flanks` (A1 + A3: the unique corner tile, its
vertex index, flanks `{a, c}`, opposite side `b`), `H1eCL.corner_aligned` (A2: its two edges at `A` lie along the two
target sides), `BaseBetaModel.localAngle_of_oppSide` (A4: which end carries `γ`), `rayparam` (A5: barycentric
parameters), `not_vertex_of_gamma` (A6: `P` is not a target vertex). -/
theorem corner_chord_data {N : ℕ} (D : CongruentDissection N) {e f : ℕ} {s α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∃ (iA : Fin N) (P Q : Plane), CornerChord D α β γ k iA P Q := by
  obtain ⟨i, j, hij, hangA, huniq, hfl, hopp⟩ := base_corner_tile_flanks hM hA k hcorner
  obtain ⟨j', hj', hrays⟩ := Erdos634.Draft.H1eCL.corner_aligned D.toDissection k i hcorner hangA
  have hjj : j' = j := (D.tile i).indep.injective (hj'.symm.trans hij)
  rw [hjj] at hrays
  have e1 : j + 1 + 1 = j + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) j
  have e2 : j + 1 + 2 = j := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) j
  have e3 : j + 2 + 1 = j := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) j
  have e4 : j + 2 + 2 = j + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) j
  have hL1 := hM.localAngle_of_oppSide hco he hef i (j + 1)
  have hL2 := hM.localAngle_of_oppSide hco he hef i (j + 2)
  rw [e1, e2] at hL1
  rw [e3, e4] at hL2
  -- label the two non-corner vertices of the tile: `P` carries `γ`, `Q` carries `α`
  obtain ⟨P, Q, hvert, hangP, hangQ, hAP, hAQ, hPQ⟩ : ∃ P Q : Plane,
      ((P = (D.tile i).pts (j + 1) ∧ Q = (D.tile i).pts (j + 2)) ∨
        (P = (D.tile i).pts (j + 2) ∧ Q = (D.tile i).pts (j + 1))) ∧
      (D.tile i).localAngle P = γ ∧ (D.tile i).localAngle Q = α ∧
      dist (D.target.pts k) P = sideOpp D.model 0 ∧ dist (D.target.pts k) Q = sideOpp D.model 2 ∧
      dist P Q = sideOpp D.model 1 := by
    rcases hfl with ⟨hc01, ha20⟩ | ⟨ha01, hc20⟩
    · refine ⟨(D.tile i).pts (j + 2), (D.tile i).pts (j + 1), Or.inr ⟨rfl, rfl⟩, hL2.2.2 hc01,
        hL1.1 ha20, ?_, ?_, ?_⟩
      · rw [hij, dist_comm]; exact ha20
      · rw [hij]; exact hc01
      · rw [dist_comm]; exact hopp
    · refine ⟨(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), Or.inl ⟨rfl, rfl⟩, hL1.2.2 hc20,
        hL2.1 ha01, ?_, ?_, hopp⟩
      · rw [hij]; exact ha01
      · rw [hij, dist_comm]; exact hc20
  refine ⟨i, P, Q, ?_⟩
  have hk1 : ∀ x : Fin 3, x + 1 ≠ x := by decide
  have hk2 : ∀ x : Fin 3, x + 2 ≠ x := by decide
  have hk12 : ∀ x : Fin 3, x + 1 ≠ x + 2 := by decide
  rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ <;> rcases hrays with ⟨r1, r2⟩ | ⟨r1, r2⟩
  · exact corner_chord_of_rays hM hA hshape huniq hij (Or.inl ⟨hP, hQ⟩) hangA hangP hangQ hAP hAQ hPQ
      (hk1 k) (hk2 k) (hk12 k) (by rw [hP]; exact r1) (by rw [hQ]; exact r2)
  · exact corner_chord_of_rays hM hA hshape huniq hij (Or.inl ⟨hP, hQ⟩) hangA hangP hangQ hAP hAQ hPQ
      (hk2 k) (hk1 k) (hk12 k).symm (by rw [hP]; exact r1) (by rw [hQ]; exact r2)
  · exact corner_chord_of_rays hM hA hshape huniq hij (Or.inr ⟨hP, hQ⟩) hangA hangP hangQ hAP hAQ hPQ
      (hk2 k) (hk1 k) (hk12 k).symm (by rw [hP]; exact r2) (by rw [hQ]; exact r1)
  · exact corner_chord_of_rays hM hA hshape huniq hij (Or.inr ⟨hP, hQ⟩) hangA hangP hangQ hAP hAQ hPQ
      (hk1 k) (hk2 k) (hk12 k) (by rw [hP]; exact r2) (by rw [hQ]; exact r1)

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.CornerChord
#print axioms Erdos634.CornerPara.sideOpp_pos'
#print axioms Erdos634.CornerPara.param_le_one
#print axioms Erdos634.CornerPara.corner_chord_of_rays
#print axioms Erdos634.CornerPara.corner_chord_data
