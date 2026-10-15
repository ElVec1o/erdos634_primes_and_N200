/-
Draft/WStripChord.lean  In `AllThreshold`.  Chord step for `prop:wstrip`.

Statement.  `prop:wstrip` (c): "Consequently, if `M(f − e) ≥ f` and `W_{M−1}(e, f)` has a tiling, then `W_M(e, f)` has a tiling.  And for every member: `W_M(e, f)` has no tiling for every `M < f` if and only if `W_{f−1}(e, f)` has none."
(d): "`W_{f−1}(e, f)` has a tiling if and only if some tiling of `W_f(e, f)` has the chord `A₁Q₁`, the chord parallel to `AQ` that cuts off the copy of `W_{f−1}` at `B`, as a wall."  (A wall is a segment that contains no interior point of a tile.)

Proved here (the strip step is `Draft/WStrip.lean`; the chord is read in the frame of `CollarG`, `u = e`, `g = f − e`, `F = f/e`, as `LayerE1Chord`, `ReframeB`, `ReframeBWall` do for `e = 1`).
* `wstrip_c_step`, `wstrip_mono`, `wstrip_c`: the two statements of (c) in the notation of the paper (`e`, `f`), from the strip step (`WStrip.wstrip_step`), `WStripArith.strip_z_exists_iff`, `WStripArith.no_w_below_iff_top` and `cor:thickw` (a) (`SideRunGA.thickw_a_pred`);
* `frame_chord_W`: the part of `W_M` below the chord `y = cB (M − 1)` is the translate of `W_{M−1}` by `(cA, 0)`; `chordTriW`: that part as a triangle;
* `wcount`: a tiling of the frame triangle `W_T` by `N` copies of the tile has `N = (2f² − e²) T²` tiles (area, `ARA.area_heron`);
* `chord_restrict_W`: a congruent dissection of `W_M` in which no tile crosses the chord gives a tiling of `W_{M−1}` (`ChordCut.restrict_below`);
* `wstrip_d`: `WTilable e f (f − 1)` iff there is a congruent dissection of the frame triangle `W_f` (model `Mod`) in which no tile crosses the chord (`straddlers = ∅`); `wstrip_d_wall`: the same with "the open chord `A₁Q₁` contains no interior point of a tile".

No sorry, no native_decide.
-/
import Erdos634.Draft.WStrip
import Erdos634.Draft.WStripArith
import Erdos634.Draft.SideRunGThick

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WStripChord
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.WAddF (Wt)
open Erdos634.Draft.WtoDeltaF (WS)
open Erdos634.Draft.CollarG (gF hF1 hfr hvpos hapos hbpos Mod Mod_sides ca cb cQ cA cB cApos cBpos WT carrier_WT WT_sides
  WTilable wTilable_iff_frame)
open Erdos634.Draft.WStripG (skewY skewY_Phi skewY_ne_zero strip_nat_dis wstrip_step)
open Erdos634.ChordTraceReal (straddlers)

/-! ## The chord in the frame -/

/-- the plane form: `Φ_F '' (S ∩ {y ≤ c}) = Φ_F '' S ∩ {skewY ≤ c}` -/
theorem image_inter_skewY {F : ℝ} (hF : 1 < F) (S : Set (ℝ × ℝ)) (c : ℝ) :
    Phi F '' (S ∩ {p | p.2 ≤ c}) = Phi F '' S ∩ {y | skewY F y ≤ c} := by
  ext y
  constructor
  · rintro ⟨p, ⟨hp, hpc⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    show skewY F (Phi F p) ≤ c
    rw [skewY_Phi hF]
    exact hpc
  · rintro ⟨⟨p, hp, rfl⟩, hy⟩
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    have h : skewY F (Phi F p) ≤ c := hy
    rw [skewY_Phi hF] at h
    exact h

/-- the translation of the plane by `Φ_F (cA, 0)` -/
noncomputable def shiftW (u g : ℝ) : Plane ≃ᵢ Plane :=
  IsometryEquiv.addRight (Phi (gF u g) (cA u g, 0))

section frame
variable {u g : ℝ} (hu : 0 < u) (hg : 0 < g)
include hu hg

/-- **The part of `W_M` below the chord `y = cB (M − 1)`** is the translate by `(cA, 0)` of `W_{M−1}`. -/
theorem frame_chord_W {M : ℝ} (hM : 1 < M) :
    Sh (cA u g, 0) (Wt (cA u g) (cB u g) (M - 1)) =
      Wt (cA u g) (cB u g) M ∩ {p | p.2 ≤ cB u g * (M - 1)} := by
  have hA := cApos hu hg
  have hB := cBpos hu hg
  ext p
  simp only [Sh, Wt, Set.mem_setOf_eq, Set.mem_inter_iff, Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨by nlinarith [h1], by nlinarith [h2], by nlinarith [h3]⟩, h2⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨by nlinarith [h1], h4, by nlinarith [h3]⟩

/-- **The part of `W_M` below the chord, as a triangle**: the translate of `W_{M−1}` by `Φ_F (cA, 0)`. -/
noncomputable def chordTriW {M : ℝ} (hM : 1 < M) : Erdos634.Geometry.Tri :=
  Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff (shiftW u g)) (WT hu hg (M - 1) (sub_pos.mpr hM))

theorem carrier_chordTriW_eq {M : ℝ} (hM : 1 < M) :
    (chordTriW hu hg hM).carrier = shiftW u g '' (WT hu hg (M - 1) (sub_pos.mpr hM)).carrier := by
  have h1 := Erdos634.DissectionMap.mapTri_carrier (Erdos634.Ladder.isoAff (shiftW u g))
    (WT hu hg (M - 1) (sub_pos.mpr hM))
  simp only [Erdos634.Ladder.isoAff_coe] at h1
  exact h1

theorem carrier_chordTriW {M : ℝ} (hM : 1 < M) :
    (chordTriW hu hg hM).carrier = Phi (gF u g) '' Sh (cA u g, 0) (Wt (cA u g) (cB u g) (M - 1)) := by
  have hc : (⇑(shiftW u g) : Plane → Plane) = fun x => x + Phi (gF u g) (cA u g, 0) := by
    funext x
    rfl
  rw [carrier_chordTriW_eq, carrier_WT hu hg (M - 1) (sub_pos.mpr hM), hc]
  exact image_shift (gF u g) (cA u g, 0) _

theorem carrier_chordTriW_inter {M : ℝ} (hM : 1 < M) :
    (chordTriW hu hg hM).carrier = (WT hu hg M (by linarith)).carrier ∩
      {y | skewY (gF u g) y ≤ cB u g * (M - 1)} := by
  rw [carrier_chordTriW hu hg hM, carrier_WT hu hg M (by linarith), frame_chord_W hu hg hM,
    image_inter_skewY (hF1 hu hg)]

/-! ## The converse: a dissection with the chord uncrossed gives a tiling of `W_{M−1}` -/

/-- **(d), converse half.**  A congruent dissection `D` of the frame triangle `W_M` with model `Mod` in which no tile has points strictly on both sides of the
line `y = cB (M − 1)` gives a tiling of `W_{M−1}`: the tiles on the side of `B` form a congruent dissection of the translate of `W_{M−1}`
(`ChordCut.restrict_below`), which is moved back by the translation. -/
theorem chord_restrict_W {M : ℝ} (hM : 1 < M) {N : ℕ} (D : CongruentDissection N)
    (hT : D.target = WT hu hg M (by linarith)) (hMo : D.model = Mod hu hg)
    (h0 : straddlers D.toDissection (skewY (gF u g)) (cB u g * (M - 1)) = ∅) :
    ∃ N' : ℕ, Nonempty (RTiling (WT hu hg (M - 1) (sub_pos.mpr hM)).carrier (Mod hu hg) N') := by
  have hT'c : (chordTriW hu hg hM).carrier = D.target.carrier ∩ {y | skewY (gF u g) y ≤ cB u g * (M - 1)} := by
    rw [hT]
    exact carrier_chordTriW_inter hu hg hM
  obtain ⟨N', D', hD't, hD'm⟩ := Erdos634.Draft.ChordCut.restrict_below D (skewY (gF u g))
    (skewY_ne_zero (hF1 hu hg)) _ h0 (chordTriW hu hg hM) hT'c
  have R1 : RTiling (chordTriW hu hg hM).carrier (Mod hu hg) N' :=
    remodel (RTiling.cast (congrArg Erdos634.Geometry.Tri.carrier hD't) (ofCD D'))
      (by rw [hD'm, hMo]; exact Erdos634.Geometry.Tri.Congruent.refl _)
  have R2 := RegionTiling.map R1 (shiftW u g).symm
  have hsymm : (shiftW u g).symm '' (chordTriW hu hg hM).carrier = (WT hu hg (M - 1) (sub_pos.mpr hM)).carrier := by
    rw [carrier_chordTriW_eq, Set.image_image]
    simp [IsometryEquiv.symm_apply_apply]
  exact ⟨N', ⟨RTiling.cast hsymm R2⟩⟩

/-! ## The number of tiles of `W_T` -/

/-- the Heron polynomial of the tile is positive -/
theorem Hh_tile_pos : 0 < Erdos634.ARA.Hh (cb u g) ((u + g) ^ 2) (ca u g) := by
  have hE : Erdos634.ARA.Hh (cb u g) ((u + g) ^ 2) (ca u g)
      = (2 * u ^ 2 + 5 * u * g + 2 * g ^ 2) * (g * (3 * u + 2 * g)) * (u * (2 * u + g)) * (u * g) := by
    unfold Erdos634.ARA.Hh; simp only [ca, cb]; ring
  rw [hE]; positivity

/-- **The number of tiles of `W_T`.**  A tiling of the frame triangle `W_T` by `N` copies of the tile has `N = (2f² − e²) T²` tiles
(`f = u + g`, `e = u`): the area relation in Heron form (`ARA.area_heron`). -/
theorem wcount (T : ℝ) (hT : 0 < T) {N : ℕ} (R : RTiling (WT hu hg T hT).carrier (Mod hu hg) N) :
    (N : ℝ) = cQ u g * T ^ 2 := by
  obtain ⟨D, hDT, hDM⟩ : ∃ D : CongruentDissection N, D.target = WT hu hg T hT ∧ D.model = Mod hu hg :=
    ⟨toCD (T := WT hu hg T hT) R, rfl, rfl⟩
  have h := Erdos634.ARA.area_heron D
  rw [hDM, hDT] at h
  obtain ⟨m1, m2, m3⟩ := Mod_sides hu hg
  obtain ⟨t01, t12, t02⟩ := WT_sides hu hg T hT
  obtain ⟨a0, a1, a2⟩ := Erdos634.Draft.LayerE1.oppLen_eq (Mod hu hg)
  obtain ⟨b0, b1, b2⟩ := Erdos634.Draft.LayerE1.oppLen_eq (WT hu hg T hT)
  have e0 : (Mod hu hg).oppLen 0 = cb u g := by rw [a0]; exact m2
  have e1 : (Mod hu hg).oppLen 1 = (u + g) ^ 2 := by rw [a1, dist_comm]; exact m3
  have e2 : (Mod hu hg).oppLen 2 = ca u g := by rw [a2]; exact m1
  have g0 : (WT hu hg T hT).oppLen 0 = cA u g * T := by rw [b0]; exact t12
  have g1 : (WT hu hg T hT).oppLen 1 = T * (u + g) ^ 3 := by rw [b1, dist_comm]; exact t02
  have g2 : (WT hu hg T hT).oppLen 2 = cB u g * T := by rw [b2]; exact t01
  rw [e0, e1, e2, g0, g1, g2] at h
  have hP := Hh_tile_pos hu hg
  have hz : ((N : ℝ) ^ 2 - (cQ u g * T ^ 2) ^ 2) * Erdos634.ARA.Hh (cb u g) ((u + g) ^ 2) (ca u g) = 0 := by
    unfold Erdos634.ARA.Hh at h ⊢
    simp only [cQ, ca, cb, cA, cB] at h ⊢
    linear_combination h
  have hsq : (N : ℝ) ^ 2 = (cQ u g * T ^ 2) ^ 2 := by
    rcases mul_eq_zero.mp hz with h0 | h0
    · linarith
    · exact absurd h0 hP.ne'
  have hQ : 0 ≤ cQ u g * T ^ 2 := by
    have hq : 0 < cQ u g := by
      have hE : cQ u g = u ^ 2 + 4 * u * g + 2 * g ^ 2 := by simp only [cQ]; ring
      rw [hE]; positivity
    positivity
  exact (sq_eq_sq₀ (Nat.cast_nonneg N) hQ).mp hsq

end frame

/-! ## The chord and the dissections of `W_f` with the chord uncrossed (natural numbers) -/

section nat

/-- `b ≥ f` for a member: `(u + g)² − u² ≥ u + g` -/
theorem b_ge_f (u g : ℕ) (hu : 0 < u) (hg : 0 < g) : u + g ≤ (u + g) ^ 2 - u ^ 2 := by
  have hb : (u + g) ^ 2 - u ^ 2 = g * (2 * u + g) := by
    have : u ^ 2 ≤ (u + g) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    zify [this]; ring
  rw [hb]
  have h1 : u + g ≤ g * (u + g) := Nat.le_mul_of_pos_left _ hg
  have h2 : g * (u + g) ≤ g * (2 * u + g) := Nat.mul_le_mul_left _ (by omega)
  exact le_trans h1 h2

/-- **(d), forward half**: `W_{f−1}` has a tiling, then the frame triangle `W_f` has a congruent dissection in which no tile crosses the chord (the strip at the scale `f`: `z = b`, `x = 0`). -/
theorem wstrip_forward (u g : ℕ) (hu : 0 < u) (hg : 0 < g) (h : WTilable u (u + g) (u + g - 1)) :
    ∃ D : CongruentDissection ((2 * (u + g) ^ 2 - u ^ 2) * (u + g) ^ 2),
      D.model = Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ∧
      D.target = WT (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ((u + g : ℕ) : ℝ)
        (Nat.cast_pos.mpr (by omega)) ∧
      straddlers D.toDissection (skewY (gF (u : ℝ) (g : ℝ))) (cB (u : ℝ) (g : ℝ) * (((u + g : ℕ) : ℝ) - 1)) = ∅ :=
  strip_nat_dis u g (u + g) ((u + g) ^ 2 - u ^ 2) 0 hu hg (b_ge_f u g hu hg) (by omega) (by rw [Nat.zero_mul, Nat.zero_add, Nat.mul_comm]) h

/-- **(d), converse half, natural numbers**: a congruent dissection of the frame triangle `W_f` (any number of tiles) in which no tile crosses the chord gives `WTilable u (u + g) (u + g − 1)`. -/
theorem wstrip_converse (u g : ℕ) (hu : 0 < u) (hg : 0 < g) {N : ℕ} (D : CongruentDissection N)
    (hT : D.target = WT (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ((u + g : ℕ) : ℝ)
      (Nat.cast_pos.mpr (by omega)))
    (hMo : D.model = Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg))
    (h0 : straddlers D.toDissection (skewY (gF (u : ℝ) (g : ℝ))) (cB (u : ℝ) (g : ℝ) * (((u + g : ℕ) : ℝ) - 1)) = ∅) :
    WTilable u (u + g) (u + g - 1) := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hf1 : (1 : ℝ) < ((u + g : ℕ) : ℝ) := by
    have : 1 < u + g := by omega
    exact_mod_cast this
  obtain ⟨N', ⟨R⟩⟩ := chord_restrict_W hu' hg' hf1 D hT hMo h0
  have hcount := wcount hu' hg' _ (sub_pos.mpr hf1) R
  have hM1 : ((u + g : ℕ) : ℝ) - 1 = ((u + g - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1 : u ^ 2 ≤ 2 * (u + g) ^ 2 := by nlinarith [Nat.zero_le g, Nat.zero_le u]
  have hNn : N' = (2 * (u + g) ^ 2 - u ^ 2) * (u + g - 1) ^ 2 := by
    have : (N' : ℝ) = (((2 * (u + g) ^ 2 - u ^ 2) * (u + g - 1) ^ 2 : ℕ) : ℝ) := by
      rw [hcount, hM1, Nat.cast_mul, Nat.cast_sub h1]; simp only [cQ]; push_cast; ring
    exact_mod_cast this
  have hpos : 0 < u + g - 1 := by omega
  have hS : (WT hu' hg' (((u + g : ℕ) : ℝ) - 1) (sub_pos.mpr hf1)).carrier =
      Phi (gF (u : ℝ) (g : ℝ)) '' Wt (cA (u : ℝ) (g : ℝ)) (cB (u : ℝ) (g : ℝ)) ((u + g - 1 : ℕ) : ℝ) := by
    rw [carrier_WT hu' hg' _ (sub_pos.mpr hf1), hM1]
  exact (wTilable_iff_frame u g (u + g - 1) hu hg hpos).mpr ⟨RTiling.castN hNn (RTiling.cast hS R)⟩

/-- **`prop:wstrip` (d)**: `W_{f−1}(e, f)` has a tiling if and only if the frame triangle `W_f(e, f)` has a congruent dissection (model `Mod`, any number of tiles)
in which no tile has points strictly on both sides of the chord `A₁Q₁` (the line parallel to `AQ` that cuts off the copy of `W_{f−1}` at `B`). -/
theorem wstrip_d (u g : ℕ) (hu : 0 < u) (hg : 0 < g) :
    WTilable u (u + g) (u + g - 1) ↔
      ∃ (N : ℕ) (D : CongruentDissection N),
        D.target = WT (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ((u + g : ℕ) : ℝ)
          (Nat.cast_pos.mpr (by omega)) ∧
        D.model = Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ∧
        straddlers D.toDissection (skewY (gF (u : ℝ) (g : ℝ))) (cB (u : ℝ) (g : ℝ) * (((u + g : ℕ) : ℝ) - 1)) = ∅ :=
  ⟨fun h => by
    obtain ⟨D, hM, hT, h0⟩ := wstrip_forward u g hu hg h
    exact ⟨_, D, hT, hM, h0⟩,
   fun ⟨_, D, hT, hM, h0⟩ => wstrip_converse u g hu hg D hT hM h0⟩

end nat

/-! ## The chord as a segment: the paper's wording -/

section wall
variable {u g : ℝ} (hu : 0 < u) (hg : 0 < g)
include hu hg

/-- the end of the chord on the leg `AB`: `A₁ = Φ_F (cA, cB (M − 1))` -/
noncomputable def chordP (u g M : ℝ) : Plane := Phi (gF u g) (cA u g, cB u g * (M - 1))

/-- the end of the chord on the side `QB`: `Q₁ = Φ_F (cA M, cB (M − 1))` -/
noncomputable def chordQ (u g M : ℝ) : Plane := Phi (gF u g) (cA u g * M, cB u g * (M - 1))

theorem skewY_chordP {M : ℝ} : skewY (gF u g) (chordP u g M) = cB u g * (M - 1) :=
  skewY_Phi (hF1 hu hg) _

theorem skewY_chordQ {M : ℝ} : skewY (gF u g) (chordQ u g M) = cB u g * (M - 1) :=
  skewY_Phi (hF1 hu hg) _

theorem skewY_openSegment {M : ℝ} {y : Plane} (hy : y ∈ openSegment ℝ (chordP u g M) (chordQ u g M)) :
    skewY (gF u g) y = cB u g * (M - 1) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [map_add, map_smul, map_smul, skewY_chordP hu hg, skewY_chordQ hu hg, smul_eq_mul, smul_eq_mul, ← add_mul,
    hab, one_mul]

/-- **The chord is the intersection of the target with the line.**  Every point of `W_M` on the line `y = cB (M − 1)` lies on the segment `[A₁, Q₁]`. -/
theorem chord_hline {M : ℝ} (hM : 1 < M) :
    ∀ y ∈ (WT hu hg M (by linarith)).carrier, skewY (gF u g) y = cB u g * (M - 1) →
      y ∈ segment ℝ (chordP u g M) (chordQ u g M) := by
  have hA := cApos hu hg
  have hB := cBpos hu hg
  intro y hy hl
  rw [carrier_WT hu hg M (by linarith)] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [skewY_Phi (hF1 hu hg)] at hl
  obtain ⟨h1, h2, h3⟩ := hp
  -- `cA ≤ p.1 ≤ cA M`
  have hlow : cA u g ≤ p.1 := by
    rw [hl] at h3
    have key : 0 ≤ cB u g * (p.1 - cA u g) := by nlinarith [h3]
    have := (mul_nonneg_iff_of_pos_left hB).mp key
    linarith
  have hM0 : 0 < cA u g * (M - 1) := mul_pos hA (by linarith)
  set t := (p.1 - cA u g) / (cA u g * (M - 1)) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hM0.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hM0]; nlinarith [h1]
  have hseg : p ∈ segment ℝ (cA u g, cB u g * (M - 1)) (cA u g * M, cB u g * (M - 1)) := by
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have hM1' : M - 1 ≠ 0 := (by linarith : (0 : ℝ) < M - 1).ne'
      have hA' : cA u g ≠ 0 := hA.ne'
      rw [ht]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hl]; ring
  have himg := (image_segment ℝ (Erdos634.Draft.WBrickF.PhiL (gF u g)).toAffineMap (cA u g, cB u g * (M - 1))
    (cA u g * M, cB u g * (M - 1)))
  have : Phi (gF u g) p ∈ (Erdos634.Draft.WBrickF.PhiL (gF u g)).toAffineMap '' segment ℝ
      (cA u g, cB u g * (M - 1)) (cA u g * M, cB u g * (M - 1)) := ⟨p, hseg, rfl⟩
  rw [himg] at this
  exact this

end wall

/-- **`prop:wstrip` (d), in the paper's wording**: `W_{f−1}(e, f)` has a tiling if and only if the frame triangle `W_f(e, f)` has a congruent dissection in which the chord
`A₁Q₁` contains no interior point of a tile (the open segment is a wall). -/
theorem wstrip_d_wall (u g : ℕ) (hu : 0 < u) (hg : 0 < g) :
    WTilable u (u + g) (u + g - 1) ↔
      ∃ (N : ℕ) (D : CongruentDissection N),
        D.target = WT (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ((u + g : ℕ) : ℝ)
          (Nat.cast_pos.mpr (by omega)) ∧
        D.model = Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ∧
        ∀ y ∈ openSegment ℝ (chordP (u : ℝ) (g : ℝ) ((u + g : ℕ) : ℝ)) (chordQ (u : ℝ) (g : ℝ) ((u + g : ℕ) : ℝ)),
          ∀ i, y ∉ interior (D.tile i).carrier := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hf1 : (1 : ℝ) < ((u + g : ℕ) : ℝ) := by
    have : 1 < u + g := by omega
    exact_mod_cast this
  rw [wstrip_d u g hu hg]
  constructor
  · rintro ⟨N, D, hT, hM, h0⟩
    refine ⟨N, D, hT, hM, fun y hy i hyi => ?_⟩
    have hl := skewY_openSegment hu' hg' hy
    exact Erdos634.Draft.ChordCut.not_straddles_of_empty D.toDissection _ _ h0 i
      (Erdos634.ChordTraceReal.interior_on_line_straddles (D.tile i) (skewY (gF (u : ℝ) (g : ℝ)))
        (skewY_ne_zero (hF1 hu' hg')) _ hyi hl)
  · rintro ⟨N, D, hT, hM, hw⟩
    refine ⟨N, D, hT, hM, ?_⟩
    exact Erdos634.Draft.ChordCut.straddlers_eq_empty_of_wall D.toDissection (skewY (gF (u : ℝ) (g : ℝ))) _
      (P := chordP (u : ℝ) (g : ℝ) ((u + g : ℕ) : ℝ)) (Q := chordQ (u : ℝ) (g : ℝ) ((u + g : ℕ) : ℝ))
      (fun y hy hl => chord_hline hu' hg' hf1 y (by rw [← hT]; exact hy) hl) hw

/-! ## `prop:wstrip` (c) in the notation of the paper -/

/-- **`prop:wstrip` (c), first statement**: if `M (f − e) ≥ f` and `W_{M−1}(e, f)` has a tiling, then `W_M(e, f)` has a tiling (`M ≥ 2` is implied; coprime `e < f`). -/
theorem wstrip_c_step (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 2 ≤ M)
    (hMf : f ≤ M * (f - e)) (h : WTilable e f (M - 1)) : WTilable e f M := by
  obtain ⟨z, hz, hzf, hzM⟩ := (Erdos634.Draft.WStripArith.strip_z_exists_iff e f M he hef hco hM).mpr hMf
  obtain ⟨x, -, hW⟩ := wstrip_step e f M z he hef hM hz hzf hzM h
  exact hW

/-- the tilings of `W_M(e, f)` at the scales `M` with `M (f − e) ≥ f` propagate to all larger scales (the last sentence of the proof of (c)) -/
theorem wstrip_mono (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hMf : f ≤ M * (f - e)) (h : WTilable e f M) : ∀ k, WTilable e f (M + k) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    have hpos : f - e ≤ (k + 1) * (f - e) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
    have hmul : (M + (k + 1)) * (f - e) = M * (f - e) + (k + 1) * (f - e) := Nat.add_mul _ _ _
    have hcond : f ≤ (M + (k + 1)) * (f - e) := by omega
    refine wstrip_c_step e f (M + (k + 1)) he hef hco (by omega) hcond ?_
    have e1 : M + (k + 1) - 1 = M + k := by omega
    rw [e1]; exact ih

/-- **`prop:wstrip` (c), second statement**: for every member, `W_M(e, f)` has no tiling for every `M < f` if and only if `W_{f−1}(e, f)` has none
(the strip step above the scales with `M (f − e) ≥ f`, and `cor:thickw` (a) below them). -/
theorem wstrip_c (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    (∀ M, 1 ≤ M → M < f → ¬ WTilable e f M) ↔ ¬ WTilable e f (f - 1) :=
  Erdos634.Draft.WStripArith.no_w_below_iff_top e f he hef (fun M => WTilable e f M)
    (fun M hM hMf h => wstrip_c_step e f M he hef hco hM hMf h)
    (fun M hM hMe => Erdos634.Draft.SideRunGA.thickw_a_pred e f M he hef hco hM hMe)

end Erdos634.Draft.WStripChord

#print axioms Erdos634.Draft.WStripChord.frame_chord_W
#print axioms Erdos634.Draft.WStripChord.chord_restrict_W
#print axioms Erdos634.Draft.WStripChord.wcount
#print axioms Erdos634.Draft.WStripChord.wstrip_forward
#print axioms Erdos634.Draft.WStripChord.wstrip_converse
#print axioms Erdos634.Draft.WStripChord.wstrip_d
#print axioms Erdos634.Draft.WStripChord.chord_hline
#print axioms Erdos634.Draft.WStripChord.wstrip_d_wall
#print axioms Erdos634.Draft.WStripChord.wstrip_c_step
#print axioms Erdos634.Draft.WStripChord.wstrip_mono
#print axioms Erdos634.Draft.WStripChord.wstrip_c
