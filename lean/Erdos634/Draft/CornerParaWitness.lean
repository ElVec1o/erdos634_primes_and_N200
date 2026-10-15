/-
The corner parallelogram on the N = 44 tiling `D44`.  The witness follows `Draft/GLCWit3.lean` (gamma = 2alpha,
the N = 1125 tiling) and `Draft/GammaTrapWitness44.lean` (`congruentDissection_gammatrap` on the N = 44 tiling `D44`, including
the controls at the apex).  Imported and applied: `Draft/CornerParaMaster.lean` (`corner_parallelogram`,
`corner_parallelogram_isosceles`), `Draft/CornerParaChain.lean` (`corner_first_two_edges_sides`, `walls_exist`),
`Draft/CornerParaWitnessAux.lean` (the toolkit and corner identification), `Draft/GammaTrapWitness44.lean` and
`Draft/ApexWitness44.lean` (the tiling `D44` and its scalar facts), `Draft/CornerParaCornerAux.lean` (`corner_chord_iff`).
-/
import Erdos634.Draft.CornerParaWitnessAux

/-!
# CP-5 (Witness), part 3b of 3: `prop:cornerpara` on the REAL N = 44 tiling  `D44 = Tiling44Bridge.dissection.relabelModel τ`
is the real kernel-checked tiling of the target `(0,0), (176,0), (88, 24√15)` by 44 copies of the tile `(16, 24, 32)` (`(e, f, s) =
(1, 2, 8)`, `m = 2`).  The master theorem `corner_parallelogram` is scale-free, so the `m = 1` vacuity trap (a witness that does not exist
at `m = 1`) does NOT apply: `D44` is a real instance at `s = 8`.

What this file does.
1. `D44_corner_parallelogram`, `D44_corner_parallelogram_isosceles`, `D44_applied_at_both_base_corners`: the master theorem and its
   isosceles wrapper applied at `D44` with EVERY hypothesis discharged by existing Lean (`D44_model`, `D44_angleData`, `D44_shape`,
   `tgt_hb0/1`, `D44_iso₁/₂`, `Nat.Coprime 1 2`, `1 ≤ 1 < 2`), at both base corners.
2. `D44_corner0_pinned`, `D44_corner1_pinned` ((A), (B), (C) with the tiles IDENTIFIED and the numbers PINNED): chord lengths
   `|AP| = 16 = a`, `|AQ| = 32 = c`, `|PQ| = 24 = b`; the corner tile `tiles[0]` (resp. `tiles[13]`); the partner `tiles[2]` (resp. `tiles[14]`),
   the only other tile with an edge equal to the chord, presenting `α` at `P` and `γ` at `Q`; its third vertex `R = P + Q − A`,
   `|PR| = 32 = c`, `|QR| = 16 = a`; `T_A ∪ T_3 = hull {A, P, R, Q}`.
   `D44_corner0_chains`, `D44_corner1_chains` ((D) with the tiles identified and the numbers pinned): the first two edges of each of the
   two sides at the corner, as `GLI.IsChain` edges, with their owners (`tiles[0]`/`tiles[1]` on the base, `tiles[0]`/`tiles[22]` on the leg at
   corner `0`; `tiles[13]`/`tiles[11]` and `tiles[13]`/`tiles[28]` at corner `1`) and their end points: corner `0` base `(a, a) = (16, 16)`, leg
   `(c, c) = (32, 32)`; corner `1` base `(a, c) = (16, 32)`, leg `(c, a) = (32, 16)` (both `a` and `c` occur as second edges: `∈ {a, c}`
   cannot be sharpened to one value, `D44_second_edge_takes_both_values`).
3. NEGATIVE CONTROLS: at the apex `k = 2` there is no `CornerChord` (`corner_chord_iff`), the hypothesis `hcorner` genuinely fails (the apex
   angle is `3α ≠ β`), and the corner tile is not unique (three tiles meet at the apex); the partner theorem needs `i3 ≠ iA` (the corner tile
   itself has an edge equal to the chord).

Nothing here depends on any exact-arithmetic script: the tile coordinates are read through `pieceTri_pts` from the `ℤ[√15]` data of
`Tiling44.tiles` by `decide`; every theorem prints only the standard three axioms.
-/

namespace Erdos634.CornerPara.Witness44

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Z15Real Erdos634.Tiling44Bridge
  Erdos634.BaseBetaTargetCoord Erdos634.Draft.ApexWitness44 Erdos634.Draft.GammaTrapWitness44
  Erdos634.CornerPara

/-- The angles of the model of `D44`: `α = modelAlpha 1 2`, `β = modelBeta 1 2`, `γ = 2α + β`. -/
local notation "α44" => modelAlpha 1 ((2 : ℕ) : ℝ)
local notation "β44" => modelBeta 1 ((2 : ℕ) : ℝ)
local notation "γ44" => 2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)
/-- The tile index type of `D44`. -/
local notation "T44" => Fin Tiling44.tiles.length

/-! ## 1. The master theorem and its isosceles wrapper, applied at the real tiling -/

/-- **`corner_parallelogram` at the real 44-tiling**, at any base corner `k` (corner angle `β`; `k = 0`, `k = 1`): every hypothesis is
discharged (`D44_model`, `D44_angleData`, `D44_shape`, `Nat.Coprime 1 2`, `1 ≤ 1`, `1 < 2`) and the conclusion is the master theorem's. -/
theorem D44_corner_parallelogram (k : Fin 3)
    (hk : cornerAngle (D44.target.pts (k + 1)) (D44.target.pts k) (D44.target.pts (k + 2)) = β44) :
    ∃ (iA : T44) (P Q : Plane),
      CornerChord D44 α44 β44 γ44 k iA P Q ∧
      (∃ e : Fin 3, (D44.tile iA).edge e = segment ℝ P Q ∧
        dist ((D44.tile iA).pts e) ((D44.tile iA).pts (e + 1)) = sideOpp D44.model 1) ∧
      P ∈ frontier D44.target.carrier ∧ Q ∈ frontier D44.target.carrier ∧
      (∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧ ∃ p r : ℝ, 0 < p ∧ p < 1 ∧ 0 < r ∧ r < 1 ∧
        P = (1 - p) • D44.target.pts k + p • D44.target.pts w ∧
        Q = (1 - r) • D44.target.pts k + r • D44.target.pts z) ∧
      (∃! i3 : T44, i3 ≠ iA ∧ ∃ k3 : Fin 3, (D44.tile i3).edge k3 = segment ℝ P Q) ∧
      (∀ i3 : T44, i3 ≠ iA → ∀ k3 : Fin 3, (D44.tile i3).edge k3 = segment ℝ P Q →
        ((D44.tile iA).localAngle P = γ44 ∧ (D44.tile i3).localAngle P = α44) ∧
        ((D44.tile iA).localAngle Q = α44 ∧ (D44.tile i3).localAngle Q = γ44) ∧
        Q ∉ Set.range D44.target.pts ∧
        ∃ R : Plane, R = P + Q - D44.target.pts k ∧ Set.range (D44.tile i3).pts = {P, Q, R} ∧
          (D44.tile i3).localAngle R = β44 ∧ dist P R = sideOpp D44.model 2 ∧ dist Q R = sideOpp D44.model 0 ∧
          (D44.tile iA).carrier ∪ (D44.tile i3).carrier = convexHull ℝ {D44.target.pts k, P, R, Q}) ∧
      (∀ v : Fin 3, v ≠ k → ∃ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts k ∧ wl.b = D44.target.pts v ∧
        ∃ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n) ∧
      (∀ i3 : T44, i3 ≠ iA → ∀ k3 : Fin 3, (D44.tile i3).edge k3 = segment ℝ P Q →
        ∀ v : Fin 3, v ≠ k → ∀ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts k →
          wl.b = D44.target.pts v → ∀ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n →
            2 ≤ n ∧ (E 0).1 = iA ∧ (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧
            ((EdgeWordConversion.len D44 (E 0) = sideOpp D44.model 0 ∧ P ∈ segment ℝ wl.a wl.b ∧
                Placement.edgeWest D44.toDissection wl.dir (E 1) = P) ∨
              (EdgeWordConversion.len D44 (E 0) = sideOpp D44.model 2 ∧ Q ∈ segment ℝ wl.a wl.b ∧
                Placement.edgeWest D44.toDissection wl.dir (E 1) = Q)) ∧
            (EdgeWordConversion.len D44 (E 1) = sideOpp D44.model 0 ∨
              EdgeWordConversion.len D44 (E 1) = sideOpp D44.model 2) ∧
            (D44.tile (E 1).1).localAngle (Placement.edgeWest D44.toDissection wl.dir (E 1)) = β44) :=
  corner_parallelogram D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData D44_shape k hk

/-- **The isosceles wrapper at the real 44-tiling**: the target is isosceles with base angles `β` at the vertices `a + 1 = 0`,
`a + 2 = 1` (apex `a = 2`, angle `3α`), and `k ∈ {a + 1, a + 2}` is a base corner. -/
theorem D44_corner_parallelogram_isosceles (k : Fin 3) (hk : k = 2 + 1 ∨ k = 2 + 2) :
    cornerAngle (D44.target.pts (2 + 1)) (D44.target.pts 2) (D44.target.pts (2 + 2)) = 3 * α44 ∧
    ∃ (iA : T44) (P Q : Plane),
      CornerChord D44 α44 β44 γ44 k iA P Q ∧
      (∃! i3 : T44, i3 ≠ iA ∧ ∃ k3 : Fin 3, (D44.tile i3).edge k3 = segment ℝ P Q) ∧
      (∀ i3 : T44, i3 ≠ iA → ∀ k3 : Fin 3, (D44.tile i3).edge k3 = segment ℝ P Q →
        (D44.tile i3).localAngle P = α44 ∧ (D44.tile i3).localAngle Q = γ44 ∧
        ∃ R : Plane, R = P + Q - D44.target.pts k ∧
          (D44.tile iA).carrier ∪ (D44.tile i3).carrier = convexHull ℝ {D44.target.pts k, P, R, Q}) := by
  obtain ⟨hap, iA, P, Q, hC, -, -, -, -, hB, hCpar, -, -⟩ :=
    corner_parallelogram_isosceles D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData 2 D44_iso₁ D44_iso₂ k hk
  refine ⟨hap, iA, P, Q, hC, hB, fun i3 hne k3 h3 => ?_⟩
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, -, R, hR, -, -, -, -, hhull⟩ := hCpar i3 hne k3 h3
  exact ⟨h1, h2, R, hR, hhull⟩

/-- Both routes are APPLIED at both real base corners: `corner_parallelogram` at `k = 0` (`tgt_hb0`) and `k = 1` (`tgt_hb1`), and the
isosceles wrapper at `k = 2 + 1 = 0`, `k = 2 + 2 = 1` (`hk` by `decide`); each yields a corner chord at the base corner. -/
theorem D44_applied_at_both_base_corners :
    (∃ (iA : T44) (P Q : Plane), CornerChord D44 α44 β44 γ44 0 iA P Q) ∧
    (∃ (iA : T44) (P Q : Plane), CornerChord D44 α44 β44 γ44 1 iA P Q) ∧
    (∃ (iA : T44) (P Q : Plane), CornerChord D44 α44 β44 γ44 0 iA P Q) ∧
    (∃ (iA : T44) (P Q : Plane), CornerChord D44 α44 β44 γ44 1 iA P Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨iA, P, Q, hC, -⟩ := D44_corner_parallelogram 0 tgt_hb0
    exact ⟨iA, P, Q, hC⟩
  · obtain ⟨iA, P, Q, hC, -⟩ := D44_corner_parallelogram 1 tgt_hb1
    exact ⟨iA, P, Q, hC⟩
  · obtain ⟨-, iA, P, Q, hC, -⟩ := D44_corner_parallelogram_isosceles 0 (by decide)
    exact ⟨iA, P, Q, hC⟩
  · obtain ⟨-, iA, P, Q, hC, -⟩ := D44_corner_parallelogram_isosceles 1 (by decide)
    exact ⟨iA, P, Q, hC⟩

/-! ## 2. Corner `0`: the chord, the partner and the parallelogram, identified and pinned -/

/-- **Corner `k = 0`, `A = (0, 0)`: (A), (B), (C) with tiles identified and numbers pinned.**  The corner tile is `tiles[0]`
(`P = (16, 0)`, `Q = (22, 6√15)`, `|AP| = 16 = a`, `|AQ| = 32 = c`, `|PQ| = 24 = b`); its partner is `tiles[2]` (the only tile other than `tiles[0]`
with an edge equal to the chord), presenting `α` at `P` and `γ` at `Q`; its third vertex `R = tiles[2].pts 1 = (38, 6√15)` is `P + Q − A`,
`|PR| = 32 = c`, `|QR| = 16 = a`, and `tiles[0] ∪ tiles[2]` is the parallelogram `hull {A, P, R, Q}`. -/
theorem D44_corner0_pinned :
    ∃ P Q : Plane,
      CornerChord D44 α44 β44 γ44 0 i0 P Q ∧
      P = (D44.tile i0).pts 1 ∧ Q = (D44.tile i0).pts 2 ∧
      dist (D44.target.pts 0) P = 16 ∧ dist (D44.target.pts 0) Q = 32 ∧ dist P Q = 24 ∧
      ((D44.tile i2).edge 2 = segment ℝ P Q ∧ i2 ≠ i0 ∧
        ∀ i : T44, i ≠ i0 → (∃ k' : Fin 3, (D44.tile i).edge k' = segment ℝ P Q) → i = i2) ∧
      ((D44.tile i2).localAngle P = α44 ∧ (D44.tile i2).localAngle Q = γ44) ∧
      (D44.tile i2).pts 1 = P + Q - D44.target.pts 0 ∧
      dist P ((D44.tile i2).pts 1) = 32 ∧ dist Q ((D44.tile i2).pts 1) = 16 ∧
      (D44.tile i0).carrier ∪ (D44.tile i2).carrier =
        convexHull ℝ {D44.target.pts 0, P, (D44.tile i2).pts 1, Q} := by
  obtain ⟨P, Q, hC, hPe, hQe, h2, hR, huniq⟩ := D44_corner0_chord
  have hne : i2 ≠ i0 := by decide
  obtain ⟨hαP, hγQ, -, R, hRdef, -, -, hPR, hQR, hhull⟩ :=
    corner_chord_parallelogram D44_model D44_angleData D44_shape (by decide) le_rfl (by norm_num) hC hne h2
  have hRe : R = (D44.tile i2).pts 1 := hRdef.trans hR.symm
  rw [hRe] at hPR hQR hhull
  refine ⟨P, Q, hC, hPe, hQe, by rw [hC.lenAP, model_s0], by rw [hC.lenAQ, model_s2],
    by rw [hC.lenPQ, model_s1], ⟨h2, hne, huniq⟩, ⟨hαP, hγQ⟩, hR, by rw [hPR, model_s2],
    by rw [hQR, model_s0], hhull⟩

/-- **Corner `k = 0`: the first two edges of the two sides, identified and pinned (D).**  Along EVERY wall and EVERY chain of the base
`[A, V₁]`: `n ≥ 2`, the first edge belongs to `tiles[0]` and has length `16 = a`, the second belongs to `tiles[1]` (the forward tile at `P`),
has west end `tiles[0].pts 1 = P`, east end `tiles[1].pts 1 = (32, 0)` and length `16 = a`.  Along the leg `[A, V₂]`: the first edge belongs to
`tiles[0]` and has length `32 = c`, the second to `tiles[22]`, west end `tiles[0].pts 2 = Q`, east end `tiles[22].pts 2 = (44, 12√15)`, length
`32 = c`.  Both sides have a wall and a chain. -/
theorem D44_corner0_chains :
    (∀ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 0 → wl.b = D44.target.pts 1 →
      ∀ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n →
        2 ≤ n ∧ (E 0).1 = i0 ∧ EdgeWordConversion.len D44 (E 0) = 16 ∧ (E 1).1 = i1 ∧
        EdgeWordConversion.len D44 (E 1) = 16 ∧
        Placement.edgeWest D44.toDissection wl.dir (E 1) = (D44.tile i0).pts 1 ∧
        Placement.edgeEast D44.toDissection wl.dir (E 1) = (D44.tile i1).pts 1) ∧
    (∀ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 0 → wl.b = D44.target.pts 2 →
      ∀ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n →
        2 ≤ n ∧ (E 0).1 = i0 ∧ EdgeWordConversion.len D44 (E 0) = 32 ∧ (E 1).1 = i22 ∧
        EdgeWordConversion.len D44 (E 1) = 32 ∧
        Placement.edgeWest D44.toDissection wl.dir (E 1) = (D44.tile i0).pts 2 ∧
        Placement.edgeEast D44.toDissection wl.dir (E 1) = (D44.tile i22).pts 2) ∧
    (∃ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 0 ∧ wl.b = D44.target.pts 1 ∧
      ∃ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n) ∧
    (∃ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 0 ∧ wl.b = D44.target.pts 2 ∧
      ∃ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n) := by
  obtain ⟨P, Q, hC, hPe, hQe, h2, hR, huniq⟩ := D44_corner0_chord
  have hne : i2 ≠ i0 := by decide
  obtain ⟨w, z, hkw, hkz, hwz, ⟨p, hp0, hp1, hP⟩, ⟨r, hr0, hr1, hQ⟩, hPw, hQz⟩ :=
    corner_first_two_edges_sides D44_model D44_angleData D44_shape (by decide) le_rfl (by norm_num) hC hne h2
  have hsq : (0 : ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  -- the side through `P` is the base: `w = 1` (the `y`-coordinate of `P = (1-p) A + p V_w` is `0`)
  have hw1 : w = 1 := by
    by_contra hw
    have hw2 : w = 2 := (by decide : ∀ w : Fin 3, w ≠ 0 → w ≠ 1 → w = 2) w hkw hw
    subst hw2
    have := congrArg (fun x : Plane => x 1) hP
    simp only [hPe, coord_t0_1, coord_A0, coord_A2, Erdos634.CertCoord.mkPt_one, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul] at this
    nlinarith [mul_pos hp0 hsq]
  subst hw1
  have hz2 : z = 2 := (by decide : ∀ z : Fin 3, z ≠ 0 → (1 : Fin 3) ≠ z → z = 2) z hkz hwz
  subst hz2
  have hPK : (D44.tile i1).pts 0 = P := by
    rw [hPe]; exact (D44_same i0 i1 1 0 (vt0_1.trans vt1_0.symm)).symm
  have hQK : (D44.tile i22).pts 0 = Q := by
    rw [hQe]; exact (D44_same i0 i22 2 0 (vt0_2.trans vt22_0.symm)).symm
  refine ⟨?_, ?_, walls_exist D44 0 1 (by decide), walls_exist D44 0 2 (by decide)⟩
  · intro wl hwa hwb E n C
    obtain ⟨hn, hE0, hlen0, -, -, hwest, -, -, -, hFT, j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩ :=
      hPw wl hwa hwb E n C
    have hE1 : (E 1).1 = i1 := D44_ident_P0 hFT (by rw [hPK])
    rw [hE1] at hj hpm hEast hlenE
    have hj0 : j = 0 := (D44.tile i1).indep.injective (by rw [hj, hPK])
    subst hj0
    have hm1 : m = 1 := D44_pin_P0 hm (by rw [hPK]; exact hpm)
    subst hm1
    refine ⟨hn, hE0, by rw [hlen0, model_s0], hE1, ?_, by rw [hwest, hPe], hEast⟩
    rw [hlenE, ← hPK]; exact D44_len_P0
  · intro wl hwa hwb E n C
    obtain ⟨hn, hE0, hlen0, -, -, hwest, -, -, -, hFT, j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩ :=
      hQz wl hwa hwb E n C
    have hE1 : (E 1).1 = i22 := D44_ident_Q0 hFT (by rw [hQK])
    rw [hE1] at hj hpm hEast hlenE
    have hj0 : j = 0 := (D44.tile i22).indep.injective (by rw [hj, hQK])
    subst hj0
    have hm2 : m = 2 := D44_pin_Q0 ht0 hm (by rw [hQK]; exact hpm)
    subst hm2
    refine ⟨hn, hE0, by rw [hlen0, model_s2], hE1, ?_, by rw [hwest, hQe], hEast⟩
    rw [hlenE, ← hQK]; exact D44_len_Q0

/-! ## 3. Corner `1`: the chord, the partner, the parallelogram and the first two edges, identified and pinned -/

/-- **Corner `k = 1`, `A = (176, 0)`: (A), (B), (C) with tiles identified and numbers pinned.**  The corner tile is `tiles[13]`
(`P = (160, 0)`, `Q = (154, 6√15)`, `|AP| = 16`, `|AQ| = 32`, `|PQ| = 24`); its partner is `tiles[14]` (the only other tile with an edge equal to the
chord), presenting `α` at `P` and `γ` at `Q`; its third vertex `R = tiles[14].pts 2 = (138, 6√15)` is `P + Q − A`, `|PR| = 32`, `|QR| = 16`, and
`tiles[13] ∪ tiles[14]` is the parallelogram `hull {A, P, R, Q}`. -/
theorem D44_corner1_pinned :
    ∃ P Q : Plane,
      CornerChord D44 α44 β44 γ44 1 i13 P Q ∧
      P = (D44.tile i13).pts 0 ∧ Q = (D44.tile i13).pts 2 ∧
      dist (D44.target.pts 1) P = 16 ∧ dist (D44.target.pts 1) Q = 32 ∧ dist P Q = 24 ∧
      ((D44.tile i14).edge 0 = segment ℝ P Q ∧ i14 ≠ i13 ∧
        ∀ i : T44, i ≠ i13 → (∃ k' : Fin 3, (D44.tile i).edge k' = segment ℝ P Q) → i = i14) ∧
      ((D44.tile i14).localAngle P = α44 ∧ (D44.tile i14).localAngle Q = γ44) ∧
      (D44.tile i14).pts 2 = P + Q - D44.target.pts 1 ∧
      dist P ((D44.tile i14).pts 2) = 32 ∧ dist Q ((D44.tile i14).pts 2) = 16 ∧
      (D44.tile i13).carrier ∪ (D44.tile i14).carrier =
        convexHull ℝ {D44.target.pts 1, P, (D44.tile i14).pts 2, Q} := by
  obtain ⟨P, Q, hC, hPe, hQe, h14, hR, huniq⟩ := D44_corner1_chord
  have hne : i14 ≠ i13 := by decide
  obtain ⟨hαP, hγQ, -, R, hRdef, -, -, hPR, hQR, hhull⟩ :=
    corner_chord_parallelogram D44_model D44_angleData D44_shape (by decide) le_rfl (by norm_num) hC hne h14
  have hRe : R = (D44.tile i14).pts 2 := hRdef.trans hR.symm
  rw [hRe] at hPR hQR hhull
  refine ⟨P, Q, hC, hPe, hQe, by rw [hC.lenAP, model_s0], by rw [hC.lenAQ, model_s2],
    by rw [hC.lenPQ, model_s1], ⟨h14, hne, huniq⟩, ⟨hαP, hγQ⟩, hR, by rw [hPR, model_s2],
    by rw [hQR, model_s0], hhull⟩

/-- **Corner `k = 1`: the first two edges of the two sides, identified and pinned (D).**  Along the base `[A, V₀]`: first edge in `tiles[13]`
of length `16 = a`, second in `tiles[11]` (west end `tiles[13].pts 0 = P`, east end `tiles[11].pts 0 = (128, 0)`) of length `32 = c`.  Along the leg
`[A, V₂]`: first edge in `tiles[13]` of length `32 = c`, second in `tiles[28]` (west end `tiles[13].pts 2 = Q`, east end `tiles[28].pts 2 =
(143, 9√15)`) of length `16 = a`. -/
theorem D44_corner1_chains :
    (∀ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 1 → wl.b = D44.target.pts 0 →
      ∀ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n →
        2 ≤ n ∧ (E 0).1 = i13 ∧ EdgeWordConversion.len D44 (E 0) = 16 ∧ (E 1).1 = i11 ∧
        EdgeWordConversion.len D44 (E 1) = 32 ∧
        Placement.edgeWest D44.toDissection wl.dir (E 1) = (D44.tile i13).pts 0 ∧
        Placement.edgeEast D44.toDissection wl.dir (E 1) = (D44.tile i11).pts 0) ∧
    (∀ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 1 → wl.b = D44.target.pts 2 →
      ∀ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n →
        2 ≤ n ∧ (E 0).1 = i13 ∧ EdgeWordConversion.len D44 (E 0) = 32 ∧ (E 1).1 = i28 ∧
        EdgeWordConversion.len D44 (E 1) = 16 ∧
        Placement.edgeWest D44.toDissection wl.dir (E 1) = (D44.tile i13).pts 2 ∧
        Placement.edgeEast D44.toDissection wl.dir (E 1) = (D44.tile i28).pts 2) ∧
    (∃ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 1 ∧ wl.b = D44.target.pts 0 ∧
      ∃ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n) ∧
    (∃ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 1 ∧ wl.b = D44.target.pts 2 ∧
      ∃ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n) := by
  obtain ⟨P, Q, hC, hPe, hQe, h14, hR, huniq⟩ := D44_corner1_chord
  have hne : i14 ≠ i13 := by decide
  obtain ⟨w, z, hkw, hkz, hwz, ⟨p, hp0, hp1, hP⟩, ⟨r, hr0, hr1, hQ⟩, hPw, hQz⟩ :=
    corner_first_two_edges_sides D44_model D44_angleData D44_shape (by decide) le_rfl (by norm_num) hC hne h14
  have hsq : (0 : ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  -- the side through `P` is the base: `w = 0` (the `y`-coordinate of `P = (1-p) A + p V_w` is `0`)
  have hw0 : w = 0 := by
    by_contra hw
    have hw2 : w = 2 := (by decide : ∀ w : Fin 3, w ≠ 1 → w ≠ 0 → w = 2) w hkw hw
    subst hw2
    have := congrArg (fun x : Plane => x 1) hP
    simp only [hPe, coord_t13_0, coord_A1, coord_A2, Erdos634.CertCoord.mkPt_one, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul] at this
    nlinarith [mul_pos hp0 hsq]
  subst hw0
  have hz2 : z = 2 := (by decide : ∀ z : Fin 3, z ≠ 1 → (0 : Fin 3) ≠ z → z = 2) z hkz hwz
  subst hz2
  have hPK : (D44.tile i11).pts 1 = P := by
    rw [hPe]; exact (D44_same i13 i11 0 1 (vt13_0.trans vt11_1.symm)).symm
  have hQK : (D44.tile i28).pts 1 = Q := by
    rw [hQe]; exact (D44_same i13 i28 2 1 (vt13_2.trans vt28_1.symm)).symm
  refine ⟨?_, ?_, walls_exist D44 1 0 (by decide), walls_exist D44 1 2 (by decide)⟩
  · intro wl hwa hwb E n C
    obtain ⟨hn, hE0, hlen0, -, -, hwest, -, -, -, hFT, j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩ :=
      hPw wl hwa hwb E n C
    have hE1 : (E 1).1 = i11 := D44_ident_P1 hFT (by rw [hPK])
    rw [hE1] at hj hpm hEast hlenE
    have hj1 : j = 1 := (D44.tile i11).indep.injective (by rw [hj, hPK])
    subst hj1
    have hm0 : m = 0 := D44_pin_P1 hm (by rw [hPK]; exact hpm)
    subst hm0
    refine ⟨hn, hE0, by rw [hlen0, model_s0], hE1, ?_, by rw [hwest, hPe], hEast⟩
    rw [hlenE, ← hPK]; exact D44_len_P1
  · intro wl hwa hwb E n C
    obtain ⟨hn, hE0, hlen0, -, -, hwest, -, -, -, hFT, j, m, t, hj, hm, ht0, ht1, hpm, hEast, hlenE⟩ :=
      hQz wl hwa hwb E n C
    have hE1 : (E 1).1 = i28 := D44_ident_Q1 hFT (by rw [hQK])
    rw [hE1] at hj hpm hEast hlenE
    have hj1 : j = 1 := (D44.tile i28).indep.injective (by rw [hj, hQK])
    subst hj1
    have hm2 : m = 2 := D44_pin_Q1 ht0 hm (by rw [hQK]; exact hpm)
    subst hm2
    refine ⟨hn, hE0, by rw [hlen0, model_s2], hE1, ?_, by rw [hwest, hQe], hEast⟩
    rw [hlenE, ← hQK]; exact D44_len_Q1

/-! ## 4. Negative controls -/

/-- **Counterexample (apex).**  At the apex `k = 2` of the 44-tiling the corner angle is `3α`, not `β`: the hypothesis
`hcorner` of `corner_parallelogram` fails there. -/
theorem D44_hcorner_fails_at_apex :
    ¬ cornerAngle (D44.target.pts (2 + 1)) (D44.target.pts 2) (D44.target.pts (2 + 2)) = β44 :=
  apex_to_beta_leg_hcornerbase_false

/-- **Counterexample (apex).**  At the apex `k = 2` there is no corner chord (`corner_chord_iff`): the field `angA` of `CornerChord`
is needed. -/
theorem D44_no_chord_at_apex :
    ¬ ∃ (iA : T44) (P Q : Plane), CornerChord D44 α44 β44 γ44 2 iA P Q := fun h =>
  D44_hcorner_fails_at_apex
    ((corner_chord_iff D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData D44_shape 2).mp h)

/-- **Counterexample (apex): the corner tile is not unique at the apex.**  The `unique` field of `CornerChord` is a statement about
base corners: three distinct tiles meet at the apex of `D44` (`witness44_three_tiles`). -/
theorem D44_apex_tile_not_unique :
    ¬ ∃ iA : T44, ∀ i : T44, D44.target.pts 2 ∈ (D44.tile i).carrier → i = iA := by
  rintro ⟨iA, hiA⟩
  obtain ⟨i₁, i₂, i₃, h12, h13, h23, hiff, -⟩ := witness44_three_tiles
  have h1 : i₁ = iA := hiA i₁ ((hiff i₁).mpr (Or.inl rfl))
  have h2 : i₂ = iA := hiA i₂ ((hiff i₂).mpr (Or.inr (Or.inl rfl)))
  exact h12 (h1.trans h2.symm)

/-- **Counterexample (partner).**  The partner clause needs `i3 ≠ iA`: at both base corners the corner tile itself has an edge equal to
the chord (so without `i3 ≠ iA` the `∃!` of (B) would be false); the partner is a different tile with an edge equal to the chord. -/
theorem D44_partner_needs_ne (k : Fin 3)
    (hk : cornerAngle (D44.target.pts (k + 1)) (D44.target.pts k) (D44.target.pts (k + 2)) = β44) :
    ∃ (iA : T44) (P Q : Plane) (i3 : T44),
      CornerChord D44 α44 β44 γ44 k iA P Q ∧ i3 ≠ iA ∧ (∃ k3 : Fin 3, (D44.tile i3).edge k3 = segment ℝ P Q) ∧
      (∃ kA : Fin 3, (D44.tile iA).edge kA = segment ℝ P Q) := by
  obtain ⟨iA, P, Q, hC⟩ :=
    corner_chord_data D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData D44_shape k hk
  obtain ⟨i3, ⟨hne, k3, h3⟩, -⟩ := corner_chord_partner D44_model (by decide) le_rfl (by norm_num) hC
  exact ⟨iA, P, Q, i3, hC, hne, ⟨k3, h3⟩, hC.chordEdge⟩

/-- **The two values of the second edge.**  The conclusion "the second edge has length in `{a, c}`" is not a single value: on the
44-tiling the second edge of the base from corner `0` is `a = 16` and the second edge of the base from corner `1` is
`c = 32` (`D44_corner0_chains`, `D44_corner1_chains`), and `16 ≠ 32`. -/
theorem D44_second_edge_takes_both_values :
    (∃ (wl : GLI.Wall D44.toDissection) (E : ℕ → T44 × Fin 3) (n : ℕ), wl.a = D44.target.pts 0 ∧
        wl.b = D44.target.pts 1 ∧ GLI.IsChain wl E n ∧ EdgeWordConversion.len D44 (E 1) = 16) ∧
    (∃ (wl : GLI.Wall D44.toDissection) (E : ℕ → T44 × Fin 3) (n : ℕ), wl.a = D44.target.pts 1 ∧
        wl.b = D44.target.pts 0 ∧ GLI.IsChain wl E n ∧ EdgeWordConversion.len D44 (E 1) = 32) ∧
    (16 : ℝ) ≠ 32 := by
  obtain ⟨h0b, -, ⟨wl0, hwa0, hwb0, E0, n0, C0⟩, -⟩ := D44_corner0_chains
  obtain ⟨h1b, -, ⟨wl1, hwa1, hwb1, E1, n1, C1⟩, -⟩ := D44_corner1_chains
  refine ⟨⟨wl0, E0, n0, hwa0, hwb0, C0, (h0b wl0 hwa0 hwb0 E0 n0 C0).2.2.2.2.1⟩,
    ⟨wl1, E1, n1, hwa1, hwb1, C1, (h1b wl1 hwa1 hwb1 E1 n1 C1).2.2.2.2.1⟩, by norm_num⟩

end Erdos634.CornerPara.Witness44

#print axioms Erdos634.CornerPara.Witness44.D44_corner_parallelogram
#print axioms Erdos634.CornerPara.Witness44.D44_corner_parallelogram_isosceles
#print axioms Erdos634.CornerPara.Witness44.D44_applied_at_both_base_corners
#print axioms Erdos634.CornerPara.Witness44.D44_corner0_pinned
#print axioms Erdos634.CornerPara.Witness44.D44_corner0_chains
#print axioms Erdos634.CornerPara.Witness44.D44_corner1_pinned
#print axioms Erdos634.CornerPara.Witness44.D44_corner1_chains
#print axioms Erdos634.CornerPara.Witness44.D44_hcorner_fails_at_apex
#print axioms Erdos634.CornerPara.Witness44.D44_no_chord_at_apex
#print axioms Erdos634.CornerPara.Witness44.D44_apex_tile_not_unique
#print axioms Erdos634.CornerPara.Witness44.D44_partner_needs_ne
#print axioms Erdos634.CornerPara.Witness44.D44_second_edge_takes_both_values
