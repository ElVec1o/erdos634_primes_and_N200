/-
Corner parallelogram, part 1 of 3: the chain bridge.  Adapts the corner pipeline of the γ = 2α and π/3 cases
to the base-β tile.  The passage from "a tile K at each chord end with an edge on the side" to the ordered edge chain of
the side is redone for the base-β tile on top of the chain API of
  Draft/GLIWall.lean    GLI.Wall, GLI.exists_wall, GLI.Wall.exists_chain, GLI.IsChain  (imported, not copied)
Also imported: Draft/CornerParaForward.lean (ForwardTile, corner_forward_tiles), Draft/CornerParaHalfTurn.lean
(corner_chord_Q_not_vertex), Draft/CornerParaPartner.lean (corner_chord_partner), Draft/CornerParaCornerAux.lean and
CornerParaCorner.lean (CornerChord), Draft/CornerParaBase.lean (BaseBetaModel).
-/
import Erdos634.Draft.CornerParaForward
import Erdos634.Draft.GLIWall

/-!
# Corner parallelogram, part 1 of 3: the second edge of each side at the base corner is the forward edge of `K`

Setting.  `hC : CornerChord D α β γ k iA P Q` is the corner chord of the corner tile `T_A` at the base corner `A = D.target.pts k`;
`i3` its partner; `KP`, `KQ` the forward tiles at the chord ends (`ForwardTile`).  A side of the target at
`A` is an oriented wall `wl : GLI.Wall D.toDissection` with `wl.a = A`, `wl.b = V` a target vertex, and its edge
sequence is a chain `GLI.IsChain wl E n`: `E 0, …, E (n-1)` enumerates (without repetition: `inj`, and exhaustively: `surj`) the tile
edges lying on the wall line, in increasing position (`lb`, `ub`, `nondeg`), the first starting at `wl.a` (`west0`), consecutive ones
meeting (`junc`), the last ending at `wl.b` (`east_last`), `n = (wallList …).length`.

Contents.
* `chain_bridge` (generic, one end `X` of the chord, any wall): if `X = (1-σ) wl.a + σ wl.b` (`0 < σ < 1`), `(iA, e0)` is the flank
  edge `[wl.a, X]` of `T_A` and `K` is the forward tile at `X` toward `wl.b`, then `2 ≤ n`, `E 0 = (iA, e0)`, `(E 1).1 = K`, the west
  end of `E 1` is `X`, `K` presents `β` there, the length of `E 1` is `a` or `c`, and `E 1` is the forward edge of `K`: its east end is
  `X + t (wl.b - X)`.  The method is the uniqueness of a wall edge by its west position (`GLI.IsChain.unique_by_pos`).
* `flank_edges`: the two flank edges `[A, P]`, `[A, Q]` of `T_A`, with their endpoints in either order.
* `corner_first_two_edges_sides` (per side, with the side named by the barycentric data of `P`, `Q`) and `corner_first_two_edges`
  (quantified over the far vertex `v ≠ k`, i.e. over both sides at `A`): along every wall from `A` to a target vertex and every chain
  of it: `2 ≤ n`, `E 0` belongs to `T_A`, its length is `a` (side through `P`) resp. `c` (side through `Q`), the junction is `P`
  resp. `Q`, `E 1` has length `a` or `c`, and its owner is a tile other than `T_A`, `T_3` presenting `β` at the junction.
* `walls_exist`: for every `v ≠ k` there is a wall from `A` to `V_v` and a chain along it (`GLI.exists_wall` + `Wall.exists_chain`),
  so the universally quantified statements are about a non-empty set of chains.

The hypotheses and conclusions are instantiated at the N = 44 tiling in `Draft/CornerParaWitness.lean` (+ `CornerParaWitnessAux.lean`):
`D44_corner0_chains`, `D44_corner1_chains` pin the first two edges of all four sides at the two base corners.
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.GLI Erdos634.Placement Erdos634.OrientBridge
  Erdos634.ChainInstance Erdos634.BaseChain

variable {N : ℕ}

/-! ## 1. Two small facts about an oriented wall -/

/-- The direction functional of a wall is affine along the wall segment. -/
theorem wall_dir_seg {D : Dissection N} (wl : Wall D) (s : ℝ) :
    wl.dir ((1 - s) • wl.a + s • wl.b) = (1 - s) * wl.dir wl.a + s * wl.dir wl.b := by
  rw [map_add, map_smul, map_smul]; rfl

/-- A tile edge with both endpoints on the wall segment is a wall edge. -/
theorem mem_wallList_of_segment {D : Dissection N} (wl : Wall D) (i : Fin N) (e : Fin 3)
    (h1 : (D.tile i).pts e ∈ segment ℝ wl.a wl.b) (h2 : (D.tile i).pts (e + 1) ∈ segment ℝ wl.a wl.b) :
    (i, e) ∈ wallList D wl.g 0 :=
  (mem_wallList D wl.g 0 (i, e)).mpr ⟨wl.hline _ h1, wl.hline _ h2⟩

/-! ## 2. The chain bridge at one end of the corner chord -/

/-- **The chain bridge at one end `X` of the corner chord (plan M13).**  `wl` is a wall from `A = wl.a` to `V = wl.b`
(`GLI.Wall`), `C` a chain along it; `X = (1-σ) A + σ V` lies strictly inside the side; `(iA, e0)` is the flank edge `[A, X]` of
the corner tile; `K` is the forward tile at `X` toward `V` (`ForwardTile`, CP-4).  Then the chain has at least two edges, its first
edge is `(iA, e0)`, its second edge belongs to `K`, has west end `X` (the junction), and `K` presents `β` there; the length of the
second edge is `a` or `c`; and the second edge IS the forward edge of `K`: its east end is `K`'s vertex `pts m = X + t (V - X)`
(`0 < t ≤ 1`), its length is `dist X (pts m)`.  No new geometry: the two edges are identified by their west positions
(`GLI.IsChain.unique_by_pos`). -/
theorem chain_bridge {D : CongruentDissection N} {β : ℝ}
    (wl : GLI.Wall D.toDissection) {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : GLI.IsChain wl E n)
    {iA : Fin N} {X : Plane} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hX : X = (1 - σ) • wl.a + σ • wl.b)
    (e0 : Fin 3)
    (hflank : ((D.tile iA).pts e0 = wl.a ∧ (D.tile iA).pts (e0 + 1) = X) ∨
      ((D.tile iA).pts e0 = X ∧ (D.tile iA).pts (e0 + 1) = wl.a))
    {K : Fin N} (hK : ForwardTile D β X wl.b K) :
    2 ≤ n ∧ E 0 = (iA, e0) ∧ (E 1).1 = K ∧ Placement.edgeWest D.toDissection wl.dir (E 1) = X ∧
      (D.tile (E 1).1).localAngle X = β ∧
      (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
        EdgeWordConversion.len D (E 1) = sideOpp D.model 2) ∧
      ∃ (j m : Fin 3) (t : ℝ), (D.tile K).pts j = X ∧ (m = j + 1 ∨ m = j + 2) ∧ 0 < t ∧ t ≤ 1 ∧
        (D.tile K).pts m = X + t • (wl.b - X) ∧
        Placement.edgeEast D.toDissection wl.dir (E 1) = (D.tile K).pts m ∧
        EdgeWordConversion.len D (E 1) = dist X ((D.tile K).pts m) := by
  have hlt := wl.dir_lt
  have hXseg : X ∈ segment ℝ wl.a wl.b := ⟨1 - σ, σ, by linarith, hσ0.le, by ring, hX.symm⟩
  have hdirX : wl.dir X = (1 - σ) * wl.dir wl.a + σ * wl.dir wl.b := by rw [hX, wall_dir_seg]
  have hAX : wl.dir wl.a < wl.dir X := by rw [hdirX]; nlinarith
  have hXB : wl.dir X < wl.dir wl.b := by rw [hdirX]; nlinarith
  have hXb : X ≠ wl.b := fun h => by rw [h] at hXB; exact lt_irrefl _ hXB
  have hAseg : wl.a ∈ segment ℝ wl.a wl.b := left_mem_segment ℝ _ _
  -- the flank edge is a wall edge at position `dir a`
  have hflank_mem : (iA, e0) ∈ wallList D.toDissection wl.g 0 := by
    apply mem_wallList_of_segment
    · rcases hflank with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; exact hAseg
      · rw [h1]; exact hXseg
    · rcases hflank with ⟨-, h2⟩ | ⟨-, h2⟩
      · rw [h2]; exact hXseg
      · rw [h2]; exact hAseg
  have hpos0 : edgePos D.toDissection wl.dir (iA, e0) = wl.dir wl.a := by
    unfold edgePos
    rcases hflank with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2]; exact min_eq_left hAX.le
    · simp only [h1, h2]; exact min_eq_right hAX.le
  have hposE0 : edgePos D.toDissection wl.dir (E 0) = wl.dir wl.a := by
    rw [← dir_edgeWest, C.west0]
  have hE0 : (iA, e0) = E 0 := C.unique_by_pos hflank_mem C.n_pos (by rw [hpos0, hposE0])
  have hEeast0 : edgeEast D.toDissection wl.dir (E 0) = X := by
    rw [← hE0]; unfold edgeEast
    rcases hflank with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2]; rw [if_pos hAX.le]
    · simp only [h1, h2]; rw [if_neg (not_le.mpr hAX)]
  have hn2 : 2 ≤ n := by
    by_contra hlt2
    have hn1 : n = 1 := by have := C.n_pos; omega
    have h := C.east_last
    rw [hn1, Nat.sub_self, hEeast0] at h
    exact hXb h
  have hpos1 : edgePos D.toDissection wl.dir (E 1) = wl.dir X := by
    have := C.edgePos_next (m := 0) (by omega)
    rw [zero_add] at this
    rw [this, ← dir_edgeEast, hEeast0]
  -- the forward edge of `K` is a wall edge at position `dir X`
  obtain ⟨j, m, t, hj, hm, ht0, ht1, hpm, hsub, ⟨e', hedge', hend'⟩, hlen, hfwd⟩ := hK.edge
  have hmseg : (D.tile K).pts m ∈ segment ℝ wl.a wl.b := by
    have h1 : (D.tile K).pts m ∈ segment ℝ X wl.b := hsub (right_mem_segment ℝ _ _)
    exact (convex_segment wl.a wl.b).segment_subset hXseg (right_mem_segment ℝ _ _) h1
  have hdirm : wl.dir ((D.tile K).pts m) = wl.dir X + t * (wl.dir wl.b - wl.dir X) := by
    rw [hpm, map_add, map_smul, map_sub]; rfl
  have hmX' : wl.dir X < wl.dir ((D.tile K).pts m) := by
    rw [hdirm]; have := mul_pos ht0 (sub_pos.mpr hXB); linarith
  have hKmem : (K, e') ∈ wallList D.toDissection wl.g 0 := by
    apply mem_wallList_of_segment
    · rcases hend' with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; exact hXseg
      · rw [h1]; exact hmseg
    · rcases hend' with ⟨-, h2⟩ | ⟨-, h2⟩
      · rw [h2]; exact hmseg
      · rw [h2]; exact hXseg
  have hKpos : edgePos D.toDissection wl.dir (K, e') = wl.dir X := by
    unfold edgePos
    rcases hend' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2]; exact min_eq_left hmX'.le
    · simp only [h1, h2]; exact min_eq_right hmX'.le
  have hKE1 : (K, e') = E 1 := C.unique_by_pos hKmem (by omega) (by rw [hKpos, hpos1])
  have hE1K : (E 1).1 = K := by rw [← hKE1]
  have hEast1 : edgeEast D.toDissection wl.dir (E 1) = (D.tile K).pts m := by
    rw [← hKE1]; unfold edgeEast
    rcases hend' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2]; rw [if_pos hmX'.le]
    · simp only [h1, h2]; rw [if_neg (not_le.mpr hmX')]
  have hlenE1 : EdgeWordConversion.len D (E 1) = dist X ((D.tile K).pts m) := by
    rw [← hKE1]
    show dist ((D.tile K).pts e') ((D.tile K).pts (e' + 1)) = _
    rcases hend' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  refine ⟨hn2, hE0.symm, hE1K, ?_, ?_, ?_, j, m, t, hj, hm, ht0, ht1, hpm, hEast1, hlenE1⟩
  · have := C.junc 0 (by omega)
    rw [zero_add] at this
    rw [← this, hEeast0]
  · rw [hE1K]; exact hK.ang
  · rw [hlenE1]; exact hlen

/-! ## 3. The flank edges of the corner tile -/

/-- The two flank edges of the corner tile `T_A` at `A`: `[A, P]` and `[A, Q]`, with their endpoints in either order. -/
theorem flank_edges {D : CongruentDissection N} {α β γ : ℝ} {k : Fin 3} {iA : Fin N} {P Q : Plane}
    (hC : CornerChord D α β γ k iA P Q) :
    (∃ e0 : Fin 3, ((D.tile iA).pts e0 = D.target.pts k ∧ (D.tile iA).pts (e0 + 1) = P) ∨
      ((D.tile iA).pts e0 = P ∧ (D.tile iA).pts (e0 + 1) = D.target.pts k)) ∧
    (∃ e0 : Fin 3, ((D.tile iA).pts e0 = D.target.pts k ∧ (D.tile iA).pts (e0 + 1) = Q) ∨
      ((D.tile iA).pts e0 = Q ∧ (D.tile iA).pts (e0 + 1) = D.target.pts k)) := by
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  have e3 : j + 2 + 1 = j := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) j
  rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · exact ⟨⟨j, Or.inl ⟨hjA.symm, hP.symm⟩⟩, ⟨j + 2, Or.inr ⟨hQ.symm, by rw [e3]; exact hjA.symm⟩⟩⟩
  · exact ⟨⟨j + 2, Or.inr ⟨hP.symm, by rw [e3]; exact hjA.symm⟩⟩, ⟨j, Or.inl ⟨hjA.symm, hQ.symm⟩⟩⟩

/-! ## 4. The first two edges of the two sides at the base corner -/

/-- **The first two edges of the two sides at `A`, side by side (plan §2.5).**  `hC` is the corner chord at the base corner `A`,
`i3` a partner (`T_3`: a tile `≠ T_A` with an edge equal to `[P, Q]`).  `P` lies strictly inside the target side `[A, V_w]` and
`Q` strictly inside the side `[A, V_z]` (`w ≠ z`, the two other vertices).  For EVERY wall `wl` from `A` to `V_w` and EVERY chain
`E` of it (`GLI.IsChain wl E n`): `2 ≤ n`; `E 0` belongs to `T_A` and has length `a` (`= |AP|`); the junction (west end of `E 1`)
is `P`; `E 1` belongs to a tile `≠ T_A, T_3` which presents `β` at `P`, is the only tile besides `T_A`, `T_3` containing `P`, and is
THE forward tile at `P` (`ForwardTile D β P V_w (E 1).1`: the only tile presenting `β` at `P`); `E 1` is its forward edge (east end
`P + t (V_w - P)`, `0 < t ≤ 1`, `len (E 1) = |P, east end|`); the length of `E 1` is `a` or `c`.  The same for `V_z`, with `Q` and
`c` (`= |AQ|`) in place of `P` and `a`. -/
theorem corner_first_two_edges_sides {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q)
    {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3} (h3 : (D.tile i3).edge k3 = segment ℝ P Q) :
    ∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧
      (∃ p : ℝ, 0 < p ∧ p < 1 ∧ P = (1 - p) • D.target.pts k + p • D.target.pts w) ∧
      (∃ r : ℝ, 0 < r ∧ r < 1 ∧ Q = (1 - r) • D.target.pts k + r • D.target.pts z) ∧
      (∀ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k → wl.b = D.target.pts w →
        ∀ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n →
          2 ≤ n ∧ (E 0).1 = iA ∧ EdgeWordConversion.len D (E 0) = sideOpp D.model 0 ∧
          (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧
          Placement.edgeWest D.toDissection wl.dir (E 1) = P ∧
          (D.tile (E 1).1).localAngle P = β ∧
          (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
            EdgeWordConversion.len D (E 1) = sideOpp D.model 2) ∧
          (∀ K' : Fin N, P ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = (E 1).1) ∧
          ForwardTile D β P (D.target.pts w) (E 1).1 ∧
          ∃ (j m : Fin 3) (t : ℝ), (D.tile (E 1).1).pts j = P ∧ (m = j + 1 ∨ m = j + 2) ∧
            0 < t ∧ t ≤ 1 ∧ (D.tile (E 1).1).pts m = P + t • (D.target.pts w - P) ∧
            Placement.edgeEast D.toDissection wl.dir (E 1) = (D.tile (E 1).1).pts m ∧
            EdgeWordConversion.len D (E 1) = dist P ((D.tile (E 1).1).pts m)) ∧
      (∀ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k → wl.b = D.target.pts z →
        ∀ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n →
          2 ≤ n ∧ (E 0).1 = iA ∧ EdgeWordConversion.len D (E 0) = sideOpp D.model 2 ∧
          (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧
          Placement.edgeWest D.toDissection wl.dir (E 1) = Q ∧
          (D.tile (E 1).1).localAngle Q = β ∧
          (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
            EdgeWordConversion.len D (E 1) = sideOpp D.model 2) ∧
          (∀ K' : Fin N, Q ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = (E 1).1) ∧
          ForwardTile D β Q (D.target.pts z) (E 1).1 ∧
          ∃ (j m : Fin 3) (t : ℝ), (D.tile (E 1).1).pts j = Q ∧ (m = j + 1 ∨ m = j + 2) ∧
            0 < t ∧ t ≤ 1 ∧ (D.tile (E 1).1).pts m = Q + t • (D.target.pts z - Q) ∧
            Placement.edgeEast D.toDissection wl.dir (E 1) = (D.tile (E 1).1).pts m ∧
            EdgeWordConversion.len D (E 1) = dist Q ((D.tile (E 1).1).pts m)) := by
  obtain ⟨w, z, hkw, hkz, hwz, ⟨p, hp0, hp1, hP⟩, ⟨r, hr0, hr1, hQ⟩, ⟨KP, hKP1, hKP2, hKP, hstarP⟩,
    ⟨KQ, hKQ1, hKQ2, hKQ, hstarQ⟩⟩ := corner_forward_tiles hM hA hshape hco he hef hC hne h3
  obtain ⟨⟨eP, hflP⟩, ⟨eQ, hflQ⟩⟩ := flank_edges hC
  refine ⟨w, z, hkw, hkz, hwz, ⟨p, hp0, hp1, hP⟩, ⟨r, hr0, hr1, hQ⟩, ?_, ?_⟩
  · intro wl hwa hwb E n C
    have hP' : P = (1 - p) • wl.a + p • wl.b := by rw [hwa, hwb]; exact hP
    have hKP' : ForwardTile D β P wl.b KP := by rw [hwb]; exact hKP
    have hflP' : ((D.tile iA).pts eP = wl.a ∧ (D.tile iA).pts (eP + 1) = P) ∨
        ((D.tile iA).pts eP = P ∧ (D.tile iA).pts (eP + 1) = wl.a) := by rw [hwa]; exact hflP
    obtain ⟨hn2, hE0, hE1K, hwest, hang, hlen, j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩ :=
      chain_bridge wl C hp0 hp1 hP' eP hflP' hKP'
    refine ⟨hn2, by rw [hE0], ?_, by rw [hE1K]; exact hKP1, by rw [hE1K]; exact hKP2, hwest, ?_, hlen,
      by rw [hE1K]; exact hstarP, by rw [hE1K]; exact hKP, ?_⟩
    · rw [hE0]
      rcases hflP with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · show dist ((D.tile iA).pts eP) ((D.tile iA).pts (eP + 1)) = _
        rw [h1, h2]; exact hC.lenAP
      · show dist ((D.tile iA).pts eP) ((D.tile iA).pts (eP + 1)) = _
        rw [h1, h2, dist_comm]; exact hC.lenAP
    · exact hang
    · rw [hE1K, ← hwb]; exact ⟨j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩
  · intro wl hwa hwb E n C
    have hQ' : Q = (1 - r) • wl.a + r • wl.b := by rw [hwa, hwb]; exact hQ
    have hKQ' : ForwardTile D β Q wl.b KQ := by rw [hwb]; exact hKQ
    have hflQ' : ((D.tile iA).pts eQ = wl.a ∧ (D.tile iA).pts (eQ + 1) = Q) ∨
        ((D.tile iA).pts eQ = Q ∧ (D.tile iA).pts (eQ + 1) = wl.a) := by rw [hwa]; exact hflQ
    obtain ⟨hn2, hE0, hE1K, hwest, hang, hlen, j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩ :=
      chain_bridge wl C hr0 hr1 hQ' eQ hflQ' hKQ'
    refine ⟨hn2, by rw [hE0], ?_, by rw [hE1K]; exact hKQ1, by rw [hE1K]; exact hKQ2, hwest, ?_, hlen,
      by rw [hE1K]; exact hstarQ, by rw [hE1K]; exact hKQ, ?_⟩
    · rw [hE0]
      rcases hflQ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · show dist ((D.tile iA).pts eQ) ((D.tile iA).pts (eQ + 1)) = _
        rw [h1, h2]; exact hC.lenAQ
      · show dist ((D.tile iA).pts eQ) ((D.tile iA).pts (eQ + 1)) = _
        rw [h1, h2, dist_comm]; exact hC.lenAQ
    · exact hang
    · rw [hE1K, ← hwb]; exact ⟨j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩

/-- **The first two edges of each of the two sides meeting at the base corner `A` lie in `{a, c}` (plan §2.5; the last assertion of
`prop:cornerpara`).**  Quantified over the far vertex `v ≠ k` of the wall (the two sides at `A` are `v = k+1`, `v = k+2`), over
EVERY wall `wl` from `A` to `V_v` and EVERY chain `E` of it.  Then: the chain has at least two edges; its first edge belongs to the
corner tile `T_A`; the first edge is the `a`-edge `[A, P]` and the junction is `P` (the side through `P`), or it is the `c`-edge
`[A, Q]` and the junction is `Q` (the side through `Q`); the second edge has length `a` or `c`; its owner is a tile other than
`T_A` and the partner `T_3` and it presents `β` at the junction. -/
theorem corner_first_two_edges {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q)
    {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3} (h3 : (D.tile i3).edge k3 = segment ℝ P Q) :
    ∀ v : Fin 3, v ≠ k → ∀ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k →
      wl.b = D.target.pts v → ∀ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n →
        2 ≤ n ∧ (E 0).1 = iA ∧ (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧
        ((EdgeWordConversion.len D (E 0) = sideOpp D.model 0 ∧ P ∈ segment ℝ wl.a wl.b ∧
            Placement.edgeWest D.toDissection wl.dir (E 1) = P) ∨
          (EdgeWordConversion.len D (E 0) = sideOpp D.model 2 ∧ Q ∈ segment ℝ wl.a wl.b ∧
            Placement.edgeWest D.toDissection wl.dir (E 1) = Q)) ∧
        (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
          EdgeWordConversion.len D (E 1) = sideOpp D.model 2) ∧
        (D.tile (E 1).1).localAngle (Placement.edgeWest D.toDissection wl.dir (E 1)) = β := by
  obtain ⟨w, z, hkw, hkz, hwz, ⟨p, hp0, hp1, hP⟩, ⟨r, hr0, hr1, hQ⟩, hPw, hQz⟩ :=
    corner_first_two_edges_sides hM hA hshape hco he hef hC hne h3
  intro v hv wl hwa hwb E n C
  have hcases : ∀ k w z v : Fin 3, w ≠ k → z ≠ k → w ≠ z → v ≠ k → v = w ∨ v = z := by decide
  rcases hcases k w z v hkw hkz hwz hv with rfl | rfl
  · obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, -, -, -⟩ := hPw wl hwa hwb E n C
    refine ⟨h1, h2, h4, h5, Or.inl ⟨h3', ?_, h6⟩, h8, by rw [h6]; exact h7⟩
    rw [hwa, hwb]; exact ⟨1 - p, p, by linarith, hp0.le, by ring, hP.symm⟩
  · obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, -, -, -⟩ := hQz wl hwa hwb E n C
    refine ⟨h1, h2, h4, h5, Or.inr ⟨h3', ?_, h6⟩, h8, by rw [h6]; exact h7⟩
    rw [hwa, hwb]; exact ⟨1 - r, r, by linarith, hr0.le, by ring, hQ.symm⟩

/-! ## 5. Non-vacuity of the quantification over walls and chains -/

/-- For every `v ≠ k` there IS a wall from `A = pts k` to `V_v = pts v` and a chain along it (`GLI.exists_wall` +
`GLI.Wall.exists_chain`): the universally quantified statements above are about a non-empty set of chains. -/
theorem walls_exist (D : CongruentDissection N) (k v : Fin 3) (hv : v ≠ k) :
    ∃ wl : GLI.Wall D.toDissection, wl.a = D.target.pts k ∧ wl.b = D.target.pts v ∧
      ∃ (E : ℕ → Fin N × Fin 3) (n : ℕ), GLI.IsChain wl E n := by
  obtain ⟨wl, hwa, hwb⟩ := GLI.exists_wall D.toDissection k v hv.symm
  obtain ⟨E, n, C⟩ := wl.exists_chain D.toDissection.pos
  exact ⟨wl, hwa, hwb, E, n, C⟩

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.wall_dir_seg
#print axioms Erdos634.CornerPara.mem_wallList_of_segment
#print axioms Erdos634.CornerPara.chain_bridge
#print axioms Erdos634.CornerPara.flank_edges
#print axioms Erdos634.CornerPara.corner_first_two_edges_sides
#print axioms Erdos634.CornerPara.corner_first_two_edges
#print axioms Erdos634.CornerPara.walls_exist
