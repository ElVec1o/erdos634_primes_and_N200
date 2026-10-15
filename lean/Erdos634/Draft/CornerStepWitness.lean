/- Witness of `Draft/CornerStepFormal.lean`
(`lem:cornerstep`, a corollary of `prop:cornerpara`) on the REAL kernel-checked N = 44 tiling `D44`.  Follows
`Draft/CornerParaWitness.lean` (the same tiling, the same hypotheses, the same pinned chains).  Imported and CONSUMED (applied):
`Draft/CornerStepFormal.lean` (`corner_step_base`), `Draft/CornerParaWitness.lean` (`D44_corner0_chains`, `D44_corner1_chains`),
`Draft/CornerParaWitnessAux.lean` (`D44_model`, `D44_iso₁`, `D44_iso₂`, the tile indices), `Draft/GammaTrapWitness44.lean` (`model_s0`).
-/
import Erdos634.Draft.CornerStepFormal
import Erdos634.Draft.CornerParaWitness

/-!
# The corner step at the N = 44 tiling

`D44` (target `(0,0)`, `(176,0)`, `(88, 24√15)`; tile `(16, 24, 32)`; `(e, f, s) = (1, 2, 8)`; apex `2`, base corners `0`, `1`) is an
instance of every hypothesis of `corner_step_base`, at both base corners and along the base, including the hypothesis of the lemma
itself: the corner tile lays an `a`-edge (length `16`) on the base (`hlay`).

1. `D44_corner_step_corner0` / `D44_corner_step_corner1`: the corner step applied along the base from corner `0` (`A = (0,0)`, base
   `[A, V₁]`) and from corner `1` (`A = (176,0)`, base `[A, V₀]`), with the tiles identified: the corner tile `tiles[0]` resp.
   `tiles[13]` is the owner of the first base edge, the owner of the second base edge is `tiles[1]` resp. `tiles[11]` (the `β`-tile), the
   junction is `P = tiles[0].pts 1 = (16, 0)` resp. `tiles[13].pts 0 = (160, 0)`, and the second base edge has length `16 = a` resp.
   `32 = c` (both values of "an `a` or a `c`" occur).
2. `D44_corner_step_hlay_fails_on_leg`: on the leg at either base corner the first edge has length `c = 32`, so the
   hypothesis `hlay` of the lemma fails there, and so does the junction clause: the west end of the second edge is `Q`, not `P`.
   The hypothesis `hlay` is therefore needed.
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

/-- **`lem:cornerstep` at the real 44-tiling, base from corner `0`.**  On the base `[A, V₁]`, `A = (0, 0)`, the first tile edge is an
`a`-edge of `tiles[0]`; the corner step applies, and: the junction is `P = tiles[0].pts 1`, strictly inside the base; `tiles[0]` presents
`γ` there; the tile across the chord presents `α`; the owner of the second base edge is `tiles[1]`, presents `β` at `P`, and the second
edge has length `16 = a`; and `tiles[0]`, the chord partner and `tiles[1]` are the only tiles at `P`. -/
theorem D44_corner_step_corner0 :
    ∃ (wl : GLI.Wall D44.toDissection) (E : ℕ → T44 × Fin 3) (n : ℕ),
      wl.a = D44.target.pts 0 ∧ wl.b = D44.target.pts 1 ∧ GLI.IsChain wl E n ∧
      EdgeWordConversion.len D44 (E 0) = sideOpp D44.model 0 ∧
      ∃ (iA i3 : T44) (P Q : Plane),
        iA = i0 ∧ (E 1).1 = i1 ∧ CornerChord D44 α44 β44 γ44 0 iA P Q ∧ P = (D44.tile i0).pts 1 ∧
        Placement.edgeEast D44.toDissection wl.dir (E 0) = P ∧ P ∈ openSegment ℝ wl.a wl.b ∧
        (D44.tile iA).localAngle P = γ44 ∧ (D44.tile i3).localAngle P = α44 ∧
        (D44.tile (E 1).1).localAngle P = β44 ∧ i3 ≠ iA ∧ i3 ≠ (E 1).1 ∧
        (∀ K : T44, P ∈ (D44.tile K).carrier → K = iA ∨ K = i3 ∨ K = (E 1).1) ∧
        EdgeWordConversion.len D44 (E 1) = 16 := by
  obtain ⟨wl, hwa, hwb, E, n, hE⟩ := walls_exist D44 0 1 (by decide)
  obtain ⟨hn, hE0, hlen0, hE1, hlen1, hwest, -⟩ := D44_corner0_chains.1 wl hwa hwb E n hE
  have hlay : EdgeWordConversion.len D44 (E 0) = sideOpp D44.model 0 := by rw [hlen0, model_s0]
  obtain ⟨-, iA, i3, P, Q, -, h0, hC, -, hjE, hjW, hP, hγ, -, -, -, -, -, hne, -, -, hαP, -, hE13, hang, hall, -⟩ :=
    corner_step_base D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData 2 D44_iso₁ D44_iso₂ 0
      (by decide) (by decide) (by decide) wl hwa hwb E n hE hlay
  exact ⟨wl, E, n, hwa, hwb, hE, hlay, iA, i3, P, Q, h0.symm.trans hE0, hE1, hC, hjW.symm.trans hwest, hjE,
    hP, hγ, hαP, hang, hne, fun h => hE13 h.symm, hall, hlen1⟩

/-- **`lem:cornerstep` at the real 44-tiling, base from corner `1`.**  On the base `[A, V₀]`, `A = (176, 0)`, the first tile edge is an
`a`-edge of `tiles[13]`; the junction is `P = tiles[13].pts 0 = (160, 0)`; the owner of the second base edge is `tiles[11]` and the second
edge has length `32 = c` (the other value of "an `a` or a `c`"). -/
theorem D44_corner_step_corner1 :
    ∃ (wl : GLI.Wall D44.toDissection) (E : ℕ → T44 × Fin 3) (n : ℕ),
      wl.a = D44.target.pts 1 ∧ wl.b = D44.target.pts 0 ∧ GLI.IsChain wl E n ∧
      EdgeWordConversion.len D44 (E 0) = sideOpp D44.model 0 ∧
      ∃ (iA i3 : T44) (P Q : Plane),
        iA = i13 ∧ (E 1).1 = i11 ∧ CornerChord D44 α44 β44 γ44 1 iA P Q ∧ P = (D44.tile i13).pts 0 ∧
        Placement.edgeEast D44.toDissection wl.dir (E 0) = P ∧ P ∈ openSegment ℝ wl.a wl.b ∧
        (D44.tile iA).localAngle P = γ44 ∧ (D44.tile i3).localAngle P = α44 ∧
        (D44.tile (E 1).1).localAngle P = β44 ∧ i3 ≠ iA ∧ i3 ≠ (E 1).1 ∧
        (∀ K : T44, P ∈ (D44.tile K).carrier → K = iA ∨ K = i3 ∨ K = (E 1).1) ∧
        EdgeWordConversion.len D44 (E 1) = 32 := by
  obtain ⟨wl, hwa, hwb, E, n, hE⟩ := walls_exist D44 1 0 (by decide)
  obtain ⟨hn, hE0, hlen0, hE1, hlen1, hwest, -⟩ := D44_corner1_chains.1 wl hwa hwb E n hE
  have hlay : EdgeWordConversion.len D44 (E 0) = sideOpp D44.model 0 := by rw [hlen0, model_s0]
  obtain ⟨-, iA, i3, P, Q, -, h0, hC, -, hjE, hjW, hP, hγ, -, -, -, -, -, hne, -, -, hαP, -, hE13, hang, hall, -⟩ :=
    corner_step_base D44 (by decide) le_rfl (by norm_num) D44_model D44_angleData 2 D44_iso₁ D44_iso₂ 1
      (by decide) (by decide) (by decide) wl hwa hwb E n hE hlay
  exact ⟨wl, E, n, hwa, hwb, hE, hlay, iA, i3, P, Q, h0.symm.trans hE0, hE1, hC, hjW.symm.trans hwest, hjE,
    hP, hγ, hαP, hang, hne, fun h => hE13 h.symm, hall, hlen1⟩

/-- **The hypothesis `hlay` is needed.**  On the leg at a base corner of the 44-tiling the first edge has
length `c = 32 ≠ a = 16`, so `hlay` fails there; and so does the junction clause of the conclusion, since the west end of the second leg
edge is `Q`, not `P`.  (Corner `0`, leg `[A, V₂]`; corner `1`, leg `[A, V₂]`.) -/
theorem D44_corner_step_hlay_fails_on_leg :
    (∀ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 0 → wl.b = D44.target.pts 2 →
      ∀ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n →
        EdgeWordConversion.len D44 (E 0) ≠ sideOpp D44.model 0 ∧
        Placement.edgeWest D44.toDissection wl.dir (E 1) ≠ (D44.tile i0).pts 1) ∧
    (∀ wl : GLI.Wall D44.toDissection, wl.a = D44.target.pts 1 → wl.b = D44.target.pts 2 →
      ∀ (E : ℕ → T44 × Fin 3) (n : ℕ), GLI.IsChain wl E n →
        EdgeWordConversion.len D44 (E 0) ≠ sideOpp D44.model 0 ∧
        Placement.edgeWest D44.toDissection wl.dir (E 1) ≠ (D44.tile i13).pts 0) := by
  refine ⟨fun wl hwa hwb E n hE => ?_, fun wl hwa hwb E n hE => ?_⟩
  · obtain ⟨hn, hE0, hlen0, hE1, hlen1, hwest, -⟩ := D44_corner0_chains.2.1 wl hwa hwb E n hE
    refine ⟨by rw [hlen0, model_s0]; norm_num, fun h => ?_⟩
    have h21 : (2 : Fin 3) = 1 := (D44.tile i0).indep.injective (hwest.symm.trans h)
    exact absurd h21 (by decide)
  · obtain ⟨hn, hE0, hlen0, hE1, hlen1, hwest, -⟩ := D44_corner1_chains.2.1 wl hwa hwb E n hE
    refine ⟨by rw [hlen0, model_s0]; norm_num, fun h => ?_⟩
    have h20 : (2 : Fin 3) = 0 := (D44.tile i13).indep.injective (hwest.symm.trans h)
    exact absurd h20 (by decide)

end Erdos634.CornerPara.Witness44

#print axioms Erdos634.CornerPara.Witness44.D44_corner_step_corner0
#print axioms Erdos634.CornerPara.Witness44.D44_corner_step_corner1
#print axioms Erdos634.CornerPara.Witness44.D44_corner_step_hlay_fails_on_leg
