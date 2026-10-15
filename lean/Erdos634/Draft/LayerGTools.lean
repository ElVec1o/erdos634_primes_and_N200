/-
Draft/LayerGTools.lean  In `AllThreshold`.

Tools for `Draft.LayerG` and `Draft.LayerGChord` (paper: `prop:layerall` (b), (c)): the base-β target `T_M` of the member `(e, f)` in the frame `Φ_F`
(`F = f / e`; the frame of `CollarG`, `u = e`, `g = f − e`), for every member.  Nothing here is a construction.

* `TTri`, `carrier_TTri`, `TTri_sides`, `vol_TTri`: `T_M = DS (A M) (B M) (C M)` as a triangle of the library (`WtoDeltaF.DTriR`), its sides (legs `M f³`, base `C M`) and its volume;
* `tcountG`: a tiling of `T_M` by `N` copies of the tile has `N = (3f² − u²) M²` tiles (area, `ARA.area_heron`);
* `frame_tiling_of_dissection`, `frameT_of_betaTilable`, `betaTilable_of_frameT`: a congruent dissection with the sides of `T_M` and of the tile (ANY number of tiles) is a tiling of
  the frame region, and conversely; so `BetaTilable u (u + g) M` (`UniformThreshold`) is a tiling of the frame region `Φ_F '' LT u g M`, for natural `u, g, M ≥ 1`;
* `pack_tracked`: `LayerE1Chord.pack_exists_tracked` with a stronger extra conclusion: every tile of the dissection IS a tile of one of the region tilings;
* `SideOK F c R`: no tile of the region tiling `R` has points strictly on both sides of the line `skewX F = c` (the first frame coordinate equal to `c`), and its transport under casts,
  remodelling and the translations `(0, ·)` of the frame;
* `cP`: `3 f² − u²`.

No sorry, no native_decide.
-/
import Erdos634.Draft.LayerGGeom
import Erdos634.Draft.LayerE1Chord

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.LayerG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC carrier_triC vol_triC)
open Erdos634.Draft.WtoDeltaF (DS DTriR carrier_DTriR hull_DS)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable hasSides_congr)
open Erdos634.Draft.CollarG (gF hF1 hfr hvpos hapos hbpos cApos cBpos hPpos Mod Mod_sides Mod_hasSides volMod ca cb cA cB cC cQ)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi skewX_ne_zero straddlers_empty_of_sides)
open Erdos634.ChordTraceReal (straddlers)

/-- `P = 3 f² − u²` (`f = u + g`, `u = e`): `T_M` has `P M²` tiles -/
def cP (u g : ℝ) : ℝ := 3 * (u + g) ^ 2 - u ^ 2

/-! ## The triangle `T_M` -/

section tri
variable {u g : ℝ} (hu : 0 < u) (hg : 0 < g)
include hu hg

/-- `T_M` of the member `(u, u + g)`, as a triangle of the library -/
noncomputable def TTri (M : ℝ) (hM : 0 < M) : Erdos634.Geometry.Tri :=
  DTriR (gF u g) (hF1 hu hg) (cA u g * M) (cB u g * M) (cC u g * M) (mul_pos (cApos hu hg) hM)
    (mul_pos (lcC_pos hu hg) hM)

theorem carrier_TTri (M : ℝ) (hM : 0 < M) : (TTri hu hg M hM).carrier = Phi (gF u g) '' LT u g M :=
  carrier_DTriR (gF u g) (hF1 hu hg) _ _ _ (mul_pos (cApos hu hg) hM) (mul_pos (cBpos hu hg) hM)
    (mul_lt_mul_of_pos_right (lcB_lt_cC hu hg) hM)

/-- the sides of `T_M` in the frame: legs `M f³` (on the edges `12`, `20`) and base `C M` (edge `01`) -/
theorem TTri_sides (M : ℝ) (hM : 0 < M) :
    dist ((TTri hu hg M hM).pts 1) ((TTri hu hg M hM).pts 2) = M * (u + g) ^ 3 ∧
    dist ((TTri hu hg M hM).pts 2) ((TTri hu hg M hM).pts 0) = M * (u + g) ^ 3 ∧
    dist ((TTri hu hg M hM).pts 0) ((TTri hu hg M hM).pts 1) = cC u g * M := by
  have hA : 0 < cA u g * M := mul_pos (cApos hu hg) hM
  have hC : 0 < cC u g * M := mul_pos (lcC_pos hu hg) hM
  obtain ⟨q01, q12, q02⟩ := Erdos634.Draft.CollarG.DTriR_sq (gF u g) (hF1 hu hg) (cA u g * M) (cB u g * M)
    (cC u g * M) hA hC
  have hleg : 0 ≤ M * (u + g) ^ 3 := by positivity
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg hleg).mp ?_
    simp only [TTri]
    rw [q12]; simp only [cA, cB, cC, gF]; field_simp; ring
  · rw [dist_comm]
    refine (sq_eq_sq₀ dist_nonneg hleg).mp ?_
    simp only [TTri]
    rw [q02]; simp only [cA, cB, cC, gF]; field_simp; ring
  · simp only [TTri]
    exact (sq_eq_sq₀ dist_nonneg hC.le).mp q01

open MeasureTheory in
theorem vol_TTri (M : ℝ) (hM : 0 < M) : volume (TTri hu hg M hM).carrier
    = ENNReal.ofReal (|sD (gF u g) / (2 * gF u g)| * (cA u g * M * (cC u g * M)))
      * volume Erdos634.AreaDet.stdCarrier := by
  have hu' : 0 < cA u g * M := mul_pos (cApos hu hg) hM
  have hv' : 0 < cB u g * M := mul_pos (cBpos hu hg) hM
  have hw' : 0 < cC u g * M := mul_pos (lcC_pos hu hg) hM
  have hvw' : cB u g * M < cC u g * M := mul_lt_mul_of_pos_right (lcB_lt_cC hu hg) hM
  have hdet : (((cA u g * M, cC u g * M) : ℝ × ℝ).1 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB u g * M) : ℝ × ℝ).2 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB u g * M) : ℝ × ℝ).1 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA u g * M, cC u g * M) : ℝ × ℝ).2 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).2)
      = cA u g * M * (cC u g * M) := by ring
  have hne : (((cA u g * M, cC u g * M) : ℝ × ℝ).1 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB u g * M) : ℝ × ℝ).2 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB u g * M) : ℝ × ℝ).1 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA u g * M, cC u g * M) : ℝ × ℝ).2 - ((cA u g * M, (0 : ℝ)) : ℝ × ℝ).2)
      ≠ 0 := by rw [hdet]; exact (mul_pos hu' hw').ne'
  have hc : (TTri hu hg M hM).carrier
      = (triC (gF u g) (hfr hu hg) (cA u g * M, 0) (cA u g * M, cC u g * M) (0, cB u g * M) hne).carrier := by
    rw [carrier_TTri hu hg M hM, carrier_triC]
    show Phi (gF u g) '' DS _ _ _ = _
    rw [← hull_DS _ _ _ hu' hv' hvw']
  rw [hc, vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  rw [hdet, abs_of_pos (mul_pos hu' hw')]

/-- the Heron polynomial of the tile is positive -/
theorem Hh_tile_pos : 0 < Erdos634.ARA.Hh (cb u g) ((u + g) ^ 2) (ca u g) := by
  have hE : Erdos634.ARA.Hh (cb u g) ((u + g) ^ 2) (ca u g)
      = (2 * u ^ 2 + 5 * u * g + 2 * g ^ 2) * (g * (3 * u + 2 * g)) * (u * (2 * u + g)) * (u * g) := by
    unfold Erdos634.ARA.Hh; simp only [ca, cb]; ring
  rw [hE]; positivity

/-- **The number of tiles of `T_M`.**  A tiling of the frame triangle `T_M` by `N` copies of the tile has `N = (3 f² − u²) M²` tiles
(`f = u + g`, `u = e`): the area relation in Heron form (`ARA.area_heron`). -/
theorem tcountG (M : ℝ) (hM : 0 < M) {N : ℕ} (R : RTiling (TTri hu hg M hM).carrier (Mod hu hg) N) :
    (N : ℝ) = cP u g * M ^ 2 := by
  obtain ⟨D, hDT, hDM⟩ : ∃ D : CongruentDissection N, D.target = TTri hu hg M hM ∧ D.model = Mod hu hg :=
    ⟨toCD (T := TTri hu hg M hM) R, rfl, rfl⟩
  have h := Erdos634.ARA.area_heron D
  rw [hDM, hDT] at h
  obtain ⟨m1, m2, m3⟩ := Mod_sides hu hg
  obtain ⟨t12, t20, t01⟩ := TTri_sides hu hg M hM
  obtain ⟨a0, a1, a2⟩ := Erdos634.Draft.LayerE1.oppLen_eq (Mod hu hg)
  obtain ⟨b0, b1, b2⟩ := Erdos634.Draft.LayerE1.oppLen_eq (TTri hu hg M hM)
  have e0 : (Mod hu hg).oppLen 0 = cb u g := by rw [a0]; exact m2
  have e1 : (Mod hu hg).oppLen 1 = (u + g) ^ 2 := by rw [a1, dist_comm]; exact m3
  have e2 : (Mod hu hg).oppLen 2 = ca u g := by rw [a2]; exact m1
  have g0 : (TTri hu hg M hM).oppLen 0 = M * (u + g) ^ 3 := by rw [b0]; exact t12
  have g1 : (TTri hu hg M hM).oppLen 1 = M * (u + g) ^ 3 := by rw [b1]; exact t20
  have g2 : (TTri hu hg M hM).oppLen 2 = cC u g * M := by rw [b2]; exact t01
  rw [e0, e1, e2, g0, g1, g2] at h
  have hP := Hh_tile_pos hu hg
  have hz : ((N : ℝ) ^ 2 - (cP u g * M ^ 2) ^ 2) * Erdos634.ARA.Hh (cb u g) ((u + g) ^ 2) (ca u g) = 0 := by
    unfold Erdos634.ARA.Hh at h ⊢
    simp only [cP, ca, cb, cC] at h ⊢
    linear_combination h
  have hsq : (N : ℝ) ^ 2 = (cP u g * M ^ 2) ^ 2 := by
    rcases mul_eq_zero.mp hz with h0 | h0
    · linarith
    · exact absurd h0 hP.ne'
  have hQ : 0 ≤ cP u g * M ^ 2 := by
    have hq : 0 < cP u g := hPpos hu hg
    positivity
  exact (sq_eq_sq₀ (Nat.cast_nonneg N) hQ).mp hsq

/-- **A congruent dissection with the sides of `T_M` and of the tile is a tiling of the frame region** (any number of tiles). -/
theorem frame_tiling_of_dissection {M : ℝ} (hM : 0 < M) {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target (M * (u + g) ^ 3) (M * (u + g) ^ 3) (cC u g * M))
    (hMo : HasSides D.model (cb u g) ((u + g) ^ 2) (ca u g)) :
    Nonempty (RTiling (Phi (gF u g) '' LT u g M) (Mod hu hg) N) := by
  obtain ⟨t12, t20, t01⟩ := TTri_sides hu hg M hM
  have hTU : D.target.Congruent (TTri hu hg M hM) := congruent_of_hasSides hT t12 t20 t01
  obtain ⟨g', D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hTU
  obtain ⟨m1, m2, m3⟩ := Mod_sides hu hg
  have hMF : D.model.Congruent (Mod hu hg) := congruent_of_hasSides' hMo m1 m2 m3
  have R : RTiling (TTri hu hg M hM).carrier (Mod hu hg) N :=
    { tile := D'.tile
      covers := by rw [D'.covers, hD'T]
      disj := D'.interiors_disjoint
      cong := fun i => (D'.tiles_congruent i).trans (by rw [hD'M]; exact hMF) }
  exact ⟨RTiling.cast (carrier_TTri hu hg M hM) R⟩

/-- the converse: a tiling of the frame region by `N` tiles is a congruent dissection with the sides of `T_M` and of the tile -/
theorem dissection_of_frame_tiling {M : ℝ} (hM : 0 < M) {N : ℕ}
    (R : RTiling (Phi (gF u g) '' LT u g M) (Mod hu hg) N) :
    ∃ D : CongruentDissection N, HasSides D.target (M * (u + g) ^ 3) (M * (u + g) ^ 3) (cC u g * M) ∧
      HasSides D.model (cb u g) ((u + g) ^ 2) (ca u g) := by
  obtain ⟨D, hT, hM'⟩ : ∃ D : CongruentDissection N, D.target = TTri hu hg M hM ∧ D.model = Mod hu hg :=
    ⟨toCD (T := TTri hu hg M hM) (RTiling.cast (carrier_TTri hu hg M hM).symm R), rfl, rfl⟩
  obtain ⟨t12, t20, t01⟩ := TTri_sides hu hg M hM
  refine ⟨D, ⟨Equiv.refl _, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Equiv.refl_apply]; rw [hT]; exact t12
  · simp only [Equiv.refl_apply]; rw [hT]; exact t20
  · simp only [Equiv.refl_apply]; rw [hT]; exact t01
  · rw [hM']; exact Mod_hasSides hu hg

end tri

/-! ## `BetaTilable` and the frame region (natural numbers) -/

section nat

/-- **`BetaTilable u (u + g) M` is a tiling of the frame region `T_M`** (any number of tiles): natural `u, g, M ≥ 1`. -/
theorem frameT_of_betaTilable (u g M : ℕ) (hu : 0 < u) (hg : 0 < g) (hM : 0 < M) (h : BetaTilable u (u + g) M) :
    ∃ N : ℕ, Nonempty (RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) (M : ℝ))
      (Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)) N) := by
  obtain ⟨N, D, hT, hMo⟩ := h
  have hM' : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  refine ⟨N, frame_tiling_of_dissection (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) hM' D ?_ ?_⟩
  · exact hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by simp only [cC]; push_cast; ring)
  · exact hasSides_congr (hasSides_rot hMo) (by simp only [cb]; push_cast; ring) (by push_cast; ring)
      (by simp only [ca]; push_cast; ring)

/-- the converse: a tiling of the frame region `T_M` is `BetaTilable u (u + g) M` -/
theorem betaTilable_of_frameT (u g M : ℕ) (hu : 0 < u) (hg : 0 < g) (hM : 0 < M) {N : ℕ}
    (R : RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) (M : ℝ))
      (Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)) N) :
    BetaTilable u (u + g) M := by
  have hM' : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  obtain ⟨D, hT, hMo⟩ := dissection_of_frame_tiling (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) hM' R
  refine ⟨N, D, hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by simp only [cC]; push_cast; ring), ?_⟩
  exact hasSides_congr (hasSides_rot (hasSides_rot hMo)) (by simp only [ca]; push_cast; ring)
    (by simp only [cb]; push_cast; ring) (by push_cast; ring)

end nat

/-! ## The packing lemma with the identity of each tile -/

open MeasureTheory in
/-- **`S2L.pack_exists`, with the origin of each tile.**  Same hypotheses and the same proof as `LayerE1Chord.pack_exists_tracked`; the extra
conclusion says that every tile of the dissection IS a tile of one of the region tilings. -/
theorem pack_tracked {m : ℕ} {M T : Erdos634.Geometry.Tri} (S : Fin m → Set Plane) (n : Fin m → ℕ)
    (R : ∀ a, RTiling (S a) M (n a))
    (hS : ∀ a b, a ≠ b → Disjoint (interior (S a)) (interior (S b)))
    (hsub : ∀ a, S a ⊆ T.carrier)
    (hvol : ((∑ a, n a : ℕ) : ENNReal) * volume M.carrier = volume T.carrier) :
    ∃ D : CongruentDissection (∑ a, n a), D.model = M ∧ D.target = T ∧
      ∀ e, ∃ a j, D.tile e = (R a).tile j := by
  classical
  let tile : Fin (∑ a, n a) → Erdos634.Geometry.Tri := fun e =>
    (R (finSigmaFinEquiv.symm e).1).tile (finSigmaFinEquiv.symm e).2
  have tsub : ∀ (p : (a : Fin m) × Fin (n a)), ((R p.1).tile p.2).carrier ⊆ S p.1 := by
    intro p x hx
    rw [← (R p.1).covers]
    exact Set.mem_iUnion.mpr ⟨_, hx⟩
  have hsub' : ∀ e, (tile e).carrier ⊆ T.carrier := fun e => (tsub _).trans (hsub _)
  have key : ∀ (p q : (a : Fin m) × Fin (n a)), p ≠ q →
      Disjoint (interior ((R p.1).tile p.2).carrier) (interior ((R q.1).tile q.2).carrier) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hne
    by_cases hab : a = b
    · subst hab
      have : x ≠ y := fun h => hne (by rw [h])
      exact (R a).disj this
    · exact (hS a b hab).mono (interior_mono (tsub ⟨a, x⟩)) (interior_mono (tsub ⟨b, y⟩))
  have hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier) :=
    fun i j hij => key _ _ (fun h => hij (finSigmaFinEquiv.symm.injective h))
  have hcong : ∀ e, (tile e).Congruent M := fun e => (R _).cong _
  have hvol' : ∑ e, volume (tile e).carrier = volume T.carrier := by
    rw [Finset.sum_congr rfl (fun e _ => Erdos634.CongruentArea.volume_congruent (hcong e))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hvol
  refine ⟨{ Erdos634.ConvexCover.ofCertificate T tile hsub' hdisj hvol' with
           model := M
           tiles_congruent := hcong }, rfl, rfl, ?_⟩
  intro e
  exact ⟨(finSigmaFinEquiv.symm e).1, (finSigmaFinEquiv.symm e).2, rfl⟩

/-! ## `SideOK`: no tile crosses a line -/

/-- no tile of `R` has points strictly on both sides of the line `skewX F = c` -/
def SideOK (F c : ℝ) {S : Set Plane} {M : Erdos634.Geometry.Tri} {N : ℕ} (R : RTiling S M N) : Prop :=
  ∀ i, (∀ y ∈ (R.tile i).carrier, skewX F y ≤ c) ∨ (∀ y ∈ (R.tile i).carrier, c ≤ skewX F y)

theorem cast_tile {S S' : Set Plane} {M : Erdos634.Geometry.Tri} {N : ℕ} (h : S = S') (R : RTiling S M N) :
    (RTiling.cast h R).tile = R.tile := by
  subst h; rfl

theorem SideOK_cast {F c : ℝ} {S S' : Set Plane} {M : Erdos634.Geometry.Tri} {N : ℕ} (h : S = S') (R : RTiling S M N) :
    SideOK F c (RTiling.cast h R) ↔ SideOK F c R := by
  subst h; exact Iff.rfl

theorem SideOK_castN {F c : ℝ} {S : Set Plane} {M : Erdos634.Geometry.Tri} {N N' : ℕ} (h : N = N') (R : RTiling S M N) :
    SideOK F c (RTiling.castN h R) ↔ SideOK F c R := by
  subst h; exact Iff.rfl

theorem SideOK_remodel {F c : ℝ} {S : Set Plane} {M M' : Erdos634.Geometry.Tri} {N : ℕ} (R : RTiling S M N)
    (h : M.Congruent M') : SideOK F c (RegionTiling.remodel R h) ↔ SideOK F c R := Iff.rfl

/-- a translation by `Φ_F v` with `v.1 = 0` keeps the first frame coordinate, so it keeps `SideOK` -/
theorem SideOK_shift {F : ℝ} (hF : 1 < F) {S : Set (ℝ × ℝ)} {M : Erdos634.Geometry.Tri} {N : ℕ}
    (R : RTiling (Phi F '' S) M N) (v : ℝ × ℝ) (hv : v.1 = 0) (c : ℝ) (h : SideOK F c R) :
    SideOK F c (shiftR R v) := by
  intro i
  have hcar : ((shiftR R v).tile i).carrier = (IsometryEquiv.addRight (Phi F v)) '' (R.tile i).carrier := by
    have := Erdos634.DissectionMap.mapTri_carrier (Erdos634.Ladder.isoAff (IsometryEquiv.addRight (Phi F v)))
      (R.tile i)
    simp only [Erdos634.Ladder.isoAff_coe] at this
    show ((RTiling.cast _ (RegionTiling.map R (IsometryEquiv.addRight (Phi F v)))).tile i).carrier = _
    rw [cast_tile]
    exact this
  have hkey : ∀ y, skewX F ((IsometryEquiv.addRight (Phi F v)) y) = skewX F y := fun y => by
    show skewX F (y + Phi F v) = skewX F y
    rw [map_add, skewX_Phi hF, hv, add_zero]
  rcases h i with h1 | h1
  · left
    intro y hy
    rw [hcar] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    rw [hkey]; exact h1 y0 hy0
  · right
    intro y hy
    rw [hcar] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    rw [hkey]; exact h1 y0 hy0

/-- a `SideOK` tiling gives a dissection in which no tile straddles the line -/
theorem straddlers_empty_of_SideOK {F c : ℝ} {M : Erdos634.Geometry.Tri} {N : ℕ} {T : Erdos634.Geometry.Tri}
    (R : RTiling T.carrier M N) (h : SideOK F c R) :
    straddlers (toCD (T := T) R).toDissection (skewX F) c = ∅ :=
  straddlers_empty_of_sides _ _ _ h

end Erdos634.Draft.LayerG

#print axioms Erdos634.Draft.LayerG.TTri_sides
#print axioms Erdos634.Draft.LayerG.vol_TTri
#print axioms Erdos634.Draft.LayerG.tcountG
#print axioms Erdos634.Draft.LayerG.frameT_of_betaTilable
#print axioms Erdos634.Draft.LayerG.betaTilable_of_frameT
#print axioms Erdos634.Draft.LayerG.pack_tracked
#print axioms Erdos634.Draft.LayerG.SideOK_shift
