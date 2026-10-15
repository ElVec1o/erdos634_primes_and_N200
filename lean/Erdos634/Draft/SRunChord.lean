/-
Draft/SRunChord.lean  In `AllThreshold`.

The statement `S_run(f)` and the implication `S_run(f) → ¬ BetaTilable 1 f (f−1)`.

THE STATEMENT.  Member `(1, f)`, tile `(f, f² − 1, f²)` (model `MF f`), target `T_f(1,f)` (`DeltaTri f _ f _`, the frame of the
reframing).  `ℓ` is the chord `[chordP f, chordQ f]` of `ReframeBWall` (parallel to the base at the height of `T_1`, on
the line `skewX f = chordX f`).  An `f`-run on `ℓ` from above (`RunOnChord`) is: `f` tiles `t 0, …, t (f−1)` of the
dissection, each lying in the closed half-plane `{skewX f ≤ chordX f}` (the apex side of `ℓ`), each laying its side `c` on
`ℓ` at the abscissae `x₀ + j f²` (so the `c`-edges are contiguous), all of the same type `C1` or all `C2` (same end showing
`α`).  The tile-on-segment predicate is the one in which `thm:siderunall` is stated, `SideRunG.LaysBaseOn` (side `c` on the
segment, third vertex at the distances of the type), not a new notion.

    RunOnChord        -- the configuration above, for a segment `[P, Q]` and the line at abscissa `c`
    SRun f hf         -- no congruent dissection of `T_f(1,f)` (target `DeltaTri f _ f _`, model `MF f`) has an `f`-run on
                      --   `ℓ = [chordP f, chordQ f]` from above
    topTri, carrier_topTri_inter
                      -- the part of `T_{M+1}(1,f)` above the chord at the height of `T_1` is the translate of `T_M(1,f)`
                      --   (for every `M ≥ 1`; `ReframeB.frame_chord` is the case `M = f − 1`)
    run_of_wall       -- every congruent dissection of `T_{M+1}(1,f)` in which no tile crosses that chord has an `f`-run on
                      --   the chord from above (the restriction `ChordCutTiles.restrict_below_tiles` + `thm_siderunall_T_pinned`
                      --   on the base of the upper triangle, read back in the tiles of the original dissection)
    not_betaTilable_of_srun
                      -- **`SRun f → ¬ BetaTilable 1 f (f − 1)`** (via `LayerE1Chord.layer_chord`)
    srun_config_occurs, srun_config_occurs_4_4
                      -- NON-VACUITY of the configuration: for every `f ≥ 2` and `M ≥ f` there IS a congruent dissection of
                      --   `T_{M+1}(1,f)` with the chord at the height of `T_1` uncrossed and an `f`-run on it from above
    srun_domain_nonempty
                      -- the class `SRun` quantifies over is not empty (`T_f(1,f)` has a dissection, `CollarE1.betaTilable_e1`)

ORIENTATION.  `RunOnChord` measures abscissae from `P = chordP f` (the end on the leg `AB`).  Reading the same run from the
other end exchanges `C1` and `C2` and reverses the indices; since both types are allowed, the set of configurations is the
same, but that symmetry is NOT proved here: `SRun` forbids runs written from `chordP f`, which is exactly what the proof uses.
Every `f`-run is caught this way (the base of the upper triangle runs from its vertex 0 = `chordP` to its vertex 1 = `chordQ`,
`topTri_pts0`, `topTri_pts1`).

`SRun f` is a hypothesis; `not_betaTilable_of_srun` is an implication, and nothing here proves `SRun` for any `f`.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.SideRunGMain
import Erdos634.Draft.ReframeBWall
import Erdos634.Draft.ChordCutTiles

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh RTiling.cast)

namespace Erdos634.Draft.SRunChord
open Erdos634.Draft.WFrameF
open Erdos634.Draft.WtoDeltaF (DS DeltaTri DTriR carrier_DeltaTri)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi skewX_ne_zero layer_chord layer_chord_at)
open Erdos634.Draft.UniformThreshold (BetaTilable hasSides_congr)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.ReframeB (shiftE image_inter_skewX)
open Erdos634.Draft.ReframeBWall (chordX chordP chordQ)
open Erdos634.Draft.SideRunG (LaysBaseOn thm_siderunall_T_pinned)
open Erdos634.Draft.W2E1 (Ty)
open Erdos634.ChordTraceReal (straddlers)

/-! ## The configuration and the statement -/

/-- **An `f`-run on the segment `[P, Q]` (on the line `skewX f = c`) from above**: `f` tiles of `D`, each contained in the
closed half-plane `{skewX f ≤ c}` (the apex side), each laying its side `c` on `[P, Q]` at the distance `x₀ + j f²` from `P`
(`LaysBaseOn`, the predicate of `thm:siderunall`), all of type `C1` or all of type `C2`. -/
def RunOnChord {N : ℕ} (f : ℕ) (c : ℝ) (D : CongruentDissection N) (P Q : Plane) : Prop :=
  ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist P Q ∧
    (∀ j, j < f → ∀ y ∈ (D.tile (t j)).carrier, skewX (f : ℝ) y ≤ c) ∧
    ((∀ j, j < f → LaysBaseOn D ((1 : ℕ) : ℝ) (f : ℝ) P Q (t j) Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
     (∀ j, j < f → LaysBaseOn D ((1 : ℕ) : ℝ) (f : ℝ) P Q (t j) Ty.C2 (x₀ + j * (f : ℝ) ^ 2)))

/-- **`S_run(f)`**: no congruent dissection of `T_f(1,f)` into copies of the tile
`(f, f² − 1, f²)` has an `f`-run from above on the chord `ℓ = [chordP f, chordQ f]` parallel to the base at the height of
`T_1`. -/
def SRun (f : ℕ) (hf : 2 ≤ f) : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri f hf f (by omega) →
    D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) →
    ¬ RunOnChord f (chordX f) D (chordP f) (chordQ f)

/-! ## The upper triangle at every scale -/

/-- the chord of `T_{M+1}` at the height of `T_1`: abscissa `A₀ M` -/
noncomputable def cX (f M : ℕ) : ℝ := (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ)

/-- its end on the leg `AB` -/
noncomputable def cP (f M : ℕ) : Plane := Phi (f : ℝ) (cX f M, 2 * (f : ℝ) ^ 2 - 1)

/-- its end on the leg `AC` -/
noncomputable def cQ (f M : ℕ) : Plane :=
  Phi (f : ℝ) (cX f M, (3 * (f : ℝ) ^ 2 - 1) * (M : ℝ) + (2 * (f : ℝ) ^ 2 - 1))

theorem cX_pred (f : ℕ) : cX f (f - 1) = chordX f := rfl

theorem cP_pred (f : ℕ) : cP f (f - 1) = chordP f := rfl

theorem cQ_pred (f : ℕ) (hf : 2 ≤ f) : cQ f (f - 1) = chordQ f := by
  have hmR : ((f - 1 : ℕ) : ℝ) = (f : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  unfold cQ chordQ
  congr 2
  rw [hmR]; ring

/-- the upper part of `T_{M+1}(1,f)`: the translate of `T_M(1,f)` by `Φ_f (0, B₀)` -/
noncomputable def topTri (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : 0 < M) : Erdos634.Geometry.Tri :=
  Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff (shiftE f)) (DeltaTri f hf M hM)

theorem topTri_pts (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : 0 < M) (j : Fin 3) :
    (topTri f hf M hM).pts j = shiftE f ((DeltaTri f hf M hM).pts j) := rfl

theorem shiftE_Phi (f : ℕ) (u v : ℝ) : shiftE f (Phi (f : ℝ) (u, v)) = Phi (f : ℝ) (u, v + (2 * (f : ℝ) ^ 2 - 1)) := by
  show Phi (f : ℝ) (u, v) + Phi (f : ℝ) (0, 2 * (f : ℝ) ^ 2 - 1) = _
  simp only [Phi, zero_smul, zero_add, add_smul]
  abel

theorem topTri_pts0 (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : 0 < M) : (topTri f hf M hM).pts 0 = cP f M := by
  rw [topTri_pts]
  simp only [DeltaTri, DTriR, Erdos634.Draft.WBrickF.triC_pts, Matrix.cons_val_zero]
  rw [shiftE_Phi]
  unfold cP cX
  congr 2
  ring

theorem topTri_pts1 (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : 0 < M) : (topTri f hf M hM).pts 1 = cQ f M := by
  rw [topTri_pts]
  simp only [DeltaTri, DTriR, Erdos634.Draft.WBrickF.triC_pts, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_zero]
  rw [shiftE_Phi]
  rfl

/-- the sides of the upper triangle: legs `M f³`, base `M (3f² − 1)` (an isometric image of `T_M`) -/
theorem topTri_sides (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : 0 < M) :
    dist ((topTri f hf M hM).pts 1) ((topTri f hf M hM).pts 2) = (M : ℝ) * (f : ℝ) ^ 3 ∧
    dist ((topTri f hf M hM).pts 2) ((topTri f hf M hM).pts 0) = (M : ℝ) * (f : ℝ) ^ 3 ∧
    dist ((topTri f hf M hM).pts 0) ((topTri f hf M hM).pts 1) = (3 * (f : ℝ) ^ 2 - 1) * M := by
  obtain ⟨t12, t20, t01⟩ := Erdos634.Draft.LayerE1.DeltaTri_sides f hf M hM
  simp only [topTri_pts, (shiftE f).dist_eq]
  exact ⟨t12, t20, t01⟩

/-- in the frame: the points of `DS (A s) (B s) (C s)`, `s = t + 1`, with `x ≤ A t` are the translate by `(0, B)` of
`DS (A t) (B t) (C t)` (any `A > 0`, `t > 0`) -/
theorem frame_chord_gen (A B C t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    Sh (0, B) (DS (A * t) (B * t) (C * t)) =
      DS (A * (t + 1)) (B * (t + 1)) (C * (t + 1)) ∩ {p | p.1 ≤ A * t} := by
  have hs : 0 < t + 1 := by linarith
  ext p
  simp only [Sh, DS, Set.mem_setOf_eq, Set.mem_inter_iff, Prod.fst_sub, Prod.snd_sub, sub_zero]
  set E2 := A * B * (t + 1) - B * p.1 - A * p.2 with hE2
  set E3 := A * (p.2 - B * (t + 1)) - (C - B) * p.1 with hE3
  have i2 : A * t * (B * t) - (B * t * p.1 + A * t * (p.2 - B)) = t * E2 := by rw [hE2]; ring
  have i2' : A * (t + 1) * (B * (t + 1)) - (B * (t + 1) * p.1 + A * (t + 1) * p.2) = (t + 1) * E2 := by rw [hE2]; ring
  have i3 : A * t * (p.2 - B - B * t) - (C * t - B * t) * p.1 = t * E3 := by rw [hE3]; ring
  have i3' : A * (t + 1) * (p.2 - B * (t + 1)) - (C * (t + 1) - B * (t + 1)) * p.1 = (t + 1) * E3 := by
    rw [hE3]; ring
  have key : ∀ r : ℝ, 0 < r → ∀ E : ℝ, r * E ≤ 0 ↔ E ≤ 0 := by
    intro r hr E
    constructor
    · intro h
      exact le_of_mul_le_mul_left (by rw [mul_zero]; exact h) hr
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos hr.le h
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e2 : E2 ≤ 0 := (key t ht E2).mp (by rw [← i2]; linarith)
    have e3 : E3 ≤ 0 := (key t ht E3).mp (by rw [← i3]; linarith)
    have f2 := (key (t + 1) hs E2).mpr e2
    have f3 := (key (t + 1) hs E3).mpr e3
    refine ⟨⟨by nlinarith, by linarith [i2'], by linarith [i3']⟩, h1⟩
  · rintro ⟨⟨_, h2, h3⟩, h1⟩
    have e2 : E2 ≤ 0 := (key (t + 1) hs E2).mp (by rw [← i2']; linarith)
    have e3 : E3 ≤ 0 := (key (t + 1) hs E3).mp (by rw [← i3']; linarith)
    have f2 := (key t ht E2).mpr e2
    have f3 := (key t ht E3).mpr e3
    exact ⟨h1, by linarith [i2], by linarith [i3]⟩

/-- **the upper triangle is the part of `T_{M+1}` on the side `{skewX ≤ A₀ M}` of the chord** -/
theorem carrier_topTri_inter (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : 0 < M) :
    (topTri f hf M hM).carrier = (DeltaTri f hf (M + 1) (by omega)).carrier ∩
      {y | skewX (f : ℝ) y ≤ cX f M} := by
  have hF := Erdos634.Draft.WPgramF.hF f hf
  have hc : (⇑(shiftE f) : Plane → Plane) = fun x => x + Phi (f : ℝ) (0, 2 * (f : ℝ) ^ 2 - 1) := by
    funext x; rfl
  have h1 := Erdos634.DissectionMap.mapTri_carrier (Erdos634.Ladder.isoAff (shiftE f)) (DeltaTri f hf M hM)
  simp only [Erdos634.Ladder.isoAff_coe] at h1
  have hA : (0 : ℝ) < (f : ℝ) * ((f : ℝ) ^ 2 - 1) := by
    have : (1 : ℝ) < f := hF
    exact mul_pos (by linarith) (by nlinarith)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [topTri, h1, carrier_DeltaTri f hf M hM, hc, image_shift (f : ℝ) (0, 2 * (f : ℝ) ^ 2 - 1) _,
    frame_chord_gen _ _ _ (M : ℝ) hA hMR, carrier_DeltaTri f hf (M + 1) (by omega), image_inter_skewX hF]
  push_cast
  rfl

/-! ## The run on the chord of a chord-walled dissection -/

/-- **A chord-walled dissection of `T_{M+1}(1,f)` has an `f`-run on the chord from above.**  If no tile of a congruent
dissection `D` of `T_K(1,f)`, `K = M + 1`, `M ≥ 1` (target `DeltaTri f _ K _`, model `MF f`) has points strictly on both
sides of the chord at the height of `T_1` (`straddlers = ∅`), then `D` has an `f`-run on that chord from above: the tiles above
the chord dissect the upper triangle (a copy of `T_M(1,f)`, `ChordCutTiles.restrict_below_tiles`), whose base is the chord and
whose base corners are both `β`; `thm:siderunall` (`thm_siderunall_T_pinned`) puts the run on it. -/
theorem run_of_wall (f : ℕ) (hf : 2 ≤ f) (M K : ℕ) (hM : 0 < M) (hK : K = M + 1) {N : ℕ} (D : CongruentDissection N)
    (hT : D.target = DeltaTri f hf K (by omega))
    (hMod : D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf))
    (h0 : straddlers D.toDissection (skewX (f : ℝ)) (cX f M) = ∅) :
    RunOnChord f (cX f M) D (cP f M) (cQ f M) := by
  subst hK
  have hF := Erdos634.Draft.WPgramF.hF f hf
  have hT'c : (topTri f hf M hM).carrier = D.target.carrier ∩ {y | skewX (f : ℝ) y ≤ cX f M} := by
    rw [hT]; exact carrier_topTri_inter f hf M hM
  obtain ⟨N', D', hD't, hD'm, htiles⟩ := Erdos634.Draft.ChordCutTiles.restrict_below_tiles D (skewX (f : ℝ))
    (skewX_ne_zero hF) _ h0 _ hT'c
  -- the sides of the upper triangle, in the form of `thm_siderunall_T_pinned` (`e = 1`, `s = M`)
  obtain ⟨t12, t20, t01⟩ := topTri_sides f hf M hM
  have hs : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h1 : dist (D'.target.pts ((Equiv.refl (Fin 3)) 1)) (D'.target.pts ((Equiv.refl (Fin 3)) 2))
      = (M : ℝ) * (f : ℝ) ^ 3 := by simp only [Equiv.refl_apply, hD't]; exact t12
  have h2 : dist (D'.target.pts ((Equiv.refl (Fin 3)) 2)) (D'.target.pts ((Equiv.refl (Fin 3)) 0))
      = (M : ℝ) * (f : ℝ) ^ 3 := by simp only [Equiv.refl_apply, hD't]; exact t20
  have h3 : dist (D'.target.pts ((Equiv.refl (Fin 3)) 0)) (D'.target.pts ((Equiv.refl (Fin 3)) 1))
      = (M : ℝ) * (((1 : ℕ) : ℝ) * (3 * (f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2)) := by
    simp only [Equiv.refl_apply, hD't]; rw [t01]; push_cast; ring
  -- the model
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hF
  have hMF0 : HasSides (Erdos634.Draft.WBrickF.MF (f : ℝ) hF) (f : ℝ) ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - 1) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact m2,
      by simp only [Equiv.refl_apply]; rw [dist_comm]; exact m3,
      by simp only [Equiv.refl_apply]; exact m1⟩
  have hMs : HasSides D'.model (((1 : ℕ) : ℝ) * f) ((f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
    rw [hD'm, hMod]
    exact hasSides_congr (hasSides_rot (hasSides_swap hMF0)) (by push_cast; ring) (by push_cast; ring) rfl
  obtain ⟨x₀, t, hx0, hend, hrun, -⟩ := thm_siderunall_T_pinned 1 f le_rfl (by omega) (Nat.coprime_one_left f) hs D'
    (Equiv.refl _) h1 h2 h3 hMs
  simp only [Equiv.refl_apply, hD't, topTri_pts0, topTri_pts1] at hrun hend
  -- back to the tiles of `D`
  choose emb hemb using htiles
  have hLay : ∀ j T x, LaysBaseOn D' ((1 : ℕ) : ℝ) (f : ℝ) (cP f M) (cQ f M) (t j) T x →
      LaysBaseOn D ((1 : ℕ) : ℝ) (f : ℝ) (cP f M) (cQ f M) (emb (t j)) T x := by
    intro j T x h
    unfold LaysBaseOn at h ⊢
    rw [← hemb]
    exact h
  have hdist : dist (cP f M) (cQ f M) = (M : ℝ) * (((1 : ℕ) : ℝ) * (3 * (f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2)) := by
    rw [← topTri_pts0 f hf M hM, ← topTri_pts1 f hf M hM, t01]; push_cast; ring
  refine ⟨x₀, fun j => emb (t j), hx0, by rw [hdist]; exact hend, ?_, ?_⟩
  · intro j hj y hy
    rw [← hemb] at hy
    have hy' := tile_subset_target D'.toDissection (t j) hy
    have : y ∈ (topTri f hf M hM).carrier := by
      have e : D'.toDissection.target = topTri f hf M hM := hD't
      rw [e] at hy'; exact hy'
    rw [hT'c] at this
    exact this.2
  · rcases hrun with hr | hr
    · exact Or.inl (fun j hj => hLay j _ _ (hr j hj))
    · exact Or.inr (fun j hj => hLay j _ _ (hr j hj))

/-! ## The implication -/

/-- **`S_run(f)` excludes `T_{f−1}(1,f)`.**  If no dissection of `T_f(1,f)` has an `f`-run from above on the chord at the
height of `T_1`, then `T_{f−1}(1,f)` has no tiling: a tiling of it gives (`LayerE1Chord.layer_chord`, the layer of
`prop:layer`) a dissection of `T_f(1,f)` with that chord uncrossed, and `run_of_wall` puts an `f`-run on it from above. -/
theorem not_betaTilable_of_srun (f : ℕ) (hf : 2 ≤ f) : SRun f hf → ¬ BetaTilable 1 f (f - 1) := by
  intro hS hB
  obtain ⟨N, D, hT, hM, h0⟩ := layer_chord f hf hB
  have hrun := run_of_wall f hf (f - 1) f (by omega) (by omega) D hT hM h0
  rw [cP_pred, cQ_pred f hf] at hrun
  exact hS N D hT hM hrun

/-! ## Non-vacuity -/

/-- **THE CONFIGURATION THAT `S_run` FORBIDS OCCURS AT EVERY LARGER SCALE.**  For every `f ≥ 2` and every `M ≥ f` there is a
congruent dissection of `T_{M+1}(1,f)` into copies of the tile in which the chord at the height of `T_1` is crossed by no
tile and carries an `f`-run from above (the layer over the tiling of `T_M(1,f)`, `CollarE1.betaTilable_e1`, Paliy's
construction formalized in this project; then `run_of_wall`).  So `RunOnChord` is satisfiable and `S_run` is a statement about
scale `f` exactly. -/
theorem srun_config_occurs (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : f ≤ M) :
    ∃ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri f hf (M + 1) (by omega) ∧
      D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) ∧
      straddlers D.toDissection (skewX (f : ℝ)) (cX f M) = ∅ ∧
      RunOnChord f (cX f M) D (cP f M) (cQ f M) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hTC := Erdos634.Draft.LayerE1.TClosed_of_betaTilable (g + 2) hf M (by omega)
    (Erdos634.Draft.CollarE1.betaTilable_e1 (g + 2) hf M hM)
  obtain ⟨N, D, hT, hMd, h0⟩ := layer_chord_at g M (by omega) hTC
  exact ⟨N, D, hT, hMd, h0, run_of_wall (g + 2) hf M (M + 1) (by omega) rfl D hT hMd h0⟩

/-- the instance `f = 4`, `M = 4`: a dissection of `T_5(1,4)` with the chord uncrossed and a `4`-run on it from above -/
theorem srun_config_occurs_4_4 :
    ∃ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri 4 (by norm_num) 5 (by norm_num) ∧
      straddlers D.toDissection (skewX ((4 : ℕ) : ℝ)) (cX 4 4) = ∅ ∧
      RunOnChord 4 (cX 4 4) D (cP 4 4) (cQ 4 4) := by
  obtain ⟨N, D, hT, -, h0, hr⟩ := srun_config_occurs 4 (by norm_num) 4 le_rfl
  exact ⟨N, D, hT, h0, hr⟩

/-- the class of dissections `SRun f` quantifies over is not empty (`T_f(1,f)` is tiled, `CollarE1.betaTilable_e1`) -/
theorem srun_domain_nonempty (f : ℕ) (hf : 2 ≤ f) :
    ∃ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri f hf f (by omega) ∧
      D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) := by
  obtain ⟨R⟩ := Erdos634.Draft.LayerE1.TClosed_of_betaTilable f hf f (by omega)
    (Erdos634.Draft.CollarE1.betaTilable_e1 f hf f le_rfl)
  exact ⟨_, Erdos634.Draft.RegionTiling.toCD (T := DeltaTri f hf f (by omega))
    (RTiling.cast (carrier_DeltaTri f hf f (by omega)).symm R), rfl, rfl⟩

end Erdos634.Draft.SRunChord

#print axioms Erdos634.Draft.SRunChord.carrier_topTri_inter
#print axioms Erdos634.Draft.SRunChord.run_of_wall
#print axioms Erdos634.Draft.SRunChord.not_betaTilable_of_srun
#print axioms Erdos634.Draft.SRunChord.srun_config_occurs
#print axioms Erdos634.Draft.SRunChord.srun_config_occurs_4_4
#print axioms Erdos634.Draft.SRunChord.srun_domain_nonempty
