/-
Draft/LayerE1.lean -- the layer of the base-β target of the members `(1, f)` (paper: `prop:layer`).

    theorem layer_real      -- real parameters: a tiling of `T_t` by `n₀` tiles gives a dissection of `T_{t+1}`
    theorem layer_step (g M : ℕ) (hM : g + 2 ≤ 2 * M) : TClosed (g + 2) _ M → TClosed (g + 2) _ (M + 1)
    theorem betaTilable_succ (f M : ℕ) (hf : 2 ≤ f) (hM : f ≤ 2 * M) : BetaTilable 1 f M → BetaTilable 1 f (M + 1)
    theorem betaTilable_mono (f : ℕ) (hf : 2 ≤ f) {M M' : ℕ} (hM : 1 ≤ M) (h : M ≤ M') :
        BetaTilable 1 f M → BetaTilable 1 f M'
    theorem threshold_e1_iff_top (f : ℕ) (hf : 2 ≤ f) :
        (∀ M, 1 ≤ M → ThresholdAt 1 f M) ↔ ¬ BetaTilable 1 f (f - 1)

For `f ≥ 2` and `2M ≥ f` the base-β target `T_{M+1}(1, f)` (legs `(M + 1) f³`, base `(M + 1)(3f² − 1)`) is a translate
of `T_M` together with a layer, and the layer is cut into `(2M + 1)(3f² − 1)` copies of the tile `(f, f² − 1, f²)`: the
six pieces of the cap of the collar, `x_a = (2M − f) f + 1` rows of `f` parallelograms `(f² − 1) × f`, `M + 1` rows of
`f² − 1` parallelograms `f × (f² − 1)`, and the tile at scale `f`.  So the set of scales with a tiling is an up-set
(`betaTilable_mono`; a tiling at scale `M` forces `2M > f` by `SideRun.not_betaTilable_e1_le_half`), and the threshold
statement of the member `(1, f)` is equivalent to the exclusion of the single scale `f − 1`
(`threshold_e1_iff_top`).  This file does not decide whether `T_{f−1}(1, f)` has a tiling; that is open for `f ≥ 4`.

The cap is D. Paliy's cap of six pieces ("A six-block cap for every primitive W and beta tile", unrefereed), taken
here from `Draft.CollarE1` (regions `Z3, …, Z8`, tilings `RT3, …, RT8`) at `τ = 0` and translated; the tilings at
the scales `M ≥ f` (`CollarE1.betaTilable_e1`, used in `threshold_e1_iff_top`) are his too.
Layout and linear bounds: `Draft.LayerE1Geom`.  Frame-level predicate `TClosed` and the passage to and from
`BetaTilable`: `Draft.LayerE1Tools`.  Here: the tilings of the nine regions, the packing lemma with the area identity
(`S2L.pack_exists`), and the induction.  The proof follows `CollarE1.collar_real` / `collar_step` line by line.
No sorry, no native_decide.
-/
import Erdos634.Draft.CollarE1
import Erdos634.Draft.LayerE1Geom
import Erdos634.Draft.LayerE1Tools
import Erdos634.Draft.SideRunHalf

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.LayerE1
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.BrickGridF (shift_rect)
open Erdos634.Draft.WtoDeltaF (DS)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable ThresholdAt hasSides_congr)
open Erdos634.Draft.CollarE1

noncomputable section

/-! ## Tools -/

/-- a tiling of a subset of `Φ_F '' Z`, translated by `Φ_F v` (for the two lattice parallelograms of the cap, whose
tilings are tilings of subsets) -/
theorem shift_sub_exists {F : ℝ} {M : Erdos634.Geometry.Tri} {n : ℕ} {Z : Set (ℝ × ℝ)} (v : ℝ × ℝ)
    (h : ∃ S : Set Plane, Nonempty (RTiling S M n) ∧ S ⊆ Phi F '' Z) :
    ∃ S : Set Plane, Nonempty (RTiling S M n) ∧ S ⊆ Phi F '' Sh v Z := by
  obtain ⟨S, ⟨R⟩, hS⟩ := h
  refine ⟨(IsometryEquiv.addRight (Phi F v)) '' S,
    ⟨RegionTiling.map R (IsometryEquiv.addRight (Phi F v))⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨p, hp, rfl⟩ := hS hx
  refine ⟨p + v, ?_, ?_⟩
  · show p + v - v ∈ Z
    simpa using hp
  · show Phi F (p + v) = Phi F p + Phi F v
    exact Phi_add F p v

/-! ## The target `T_{t+1}` in the frame -/

theorem oneF {d : ℝ} (hd : 0 ≤ d) : (1 : ℝ) < d + 2 := by linarith

theorem huT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : 0 < cA d * (t + 1) :=
  mul_pos (cA_pos hd (le_refl (0 : ℝ))) (by linarith)

theorem hvT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : 0 < cB d * (t + 1) :=
  mul_pos (cB_pos hd (le_refl (0 : ℝ))) (by linarith)

theorem hwT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : 0 < cC d * (t + 1) :=
  mul_pos (cC_pos hd) (by linarith)

theorem hvwT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : cB d * (t + 1) < cC d * (t + 1) :=
  mul_lt_mul_of_pos_right (cB_lt_cC hd) (by linarith)

/-- the target `T_{t+1}`: the triangle `(A (t+1), 0)`, `(A (t+1), C (t+1))`, `(0, B (t+1))` -/
def tgtT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : Erdos634.Geometry.Tri :=
  Erdos634.Draft.WtoDeltaF.DTriR (d + 2) (oneF hd) (cA d * (t + 1)) (cB d * (t + 1)) (cC d * (t + 1))
    (huT hd h2t) (hwT hd h2t)

theorem carrier_tgtT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    (tgtT hd h2t).carrier = Phi (d + 2) '' YT d t :=
  Erdos634.Draft.WtoDeltaF.carrier_DTriR _ _ _ _ _ (huT hd h2t) (hvT hd h2t) (hvwT hd h2t)

/-- the sides of the target: legs `(t + 1) F³`, base `C (t + 1)` -/
theorem tgtT_sides {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    dist ((tgtT hd h2t).pts 1) ((tgtT hd h2t).pts 2) = (t + 1) * (d + 2) ^ 3 ∧
    dist ((tgtT hd h2t).pts 2) ((tgtT hd h2t).pts 0) = (t + 1) * (d + 2) ^ 3 ∧
    dist ((tgtT hd h2t).pts 0) ((tgtT hd h2t).pts 1) = cC d * (t + 1) := by
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hpos : (0 : ℝ) ≤ (t + 1) * (d + 2) ^ 3 := mul_nonneg ht1.le (pow_nonneg (hFpos hd).le 3)
  have q : dist ((tgtT hd h2t).pts 1) ((tgtT hd h2t).pts 2) ^ 2
        = (cA d * (t + 1)) ^ 2 + (cC d * (t + 1) - cB d * (t + 1)) ^ 2
          + cA d * (t + 1) * (cC d * (t + 1) - cB d * (t + 1)) / (d + 2) ∧
      dist ((tgtT hd h2t).pts 2) ((tgtT hd h2t).pts 0) ^ 2
        = (cA d * (t + 1)) ^ 2 + (cB d * (t + 1)) ^ 2 - cA d * (t + 1) * (cB d * (t + 1)) / (d + 2) ∧
      dist ((tgtT hd h2t).pts 0) ((tgtT hd h2t).pts 1) ^ 2 = (cC d * (t + 1)) ^ 2 :=
    DTriR_sq (d + 2) (oneF hd) (cA d * (t + 1)) (cB d * (t + 1)) (cC d * (t + 1)) (huT hd h2t) (hwT hd h2t)
  obtain ⟨q12, q20, q01⟩ := q
  refine ⟨(sq_eq_sq₀ dist_nonneg hpos).mp ?_, (sq_eq_sq₀ dist_nonneg hpos).mp ?_,
    (sq_eq_sq₀ dist_nonneg (hwT hd h2t).le).mp q01⟩
  -- the identities `A² + F⁴ + A F = F⁶` and `A² + B² − A B / F = F⁶`, as in `CollarE1.tgt_sides`
  · rw [q12]; simp only [cA, cB, cC]
    field_simp
    ring
  · rw [q20]; simp only [cA, cB, cC]
    field_simp
    ring

open MeasureTheory in
theorem vol_tgtT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : volume (tgtT hd h2t).carrier
    = ENNReal.ofReal (|sD (d + 2) / (2 * (d + 2))| * (cA d * (t + 1) * (cC d * (t + 1))))
      * volume Erdos634.AreaDet.stdCarrier := by
  have hu' := huT hd h2t
  have hv' := hvT hd h2t
  have hw' := hwT hd h2t
  have hvw' := hvwT hd h2t
  have hdet : (((cA d * (t + 1), cC d * (t + 1)) : ℝ × ℝ).1 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB d * (t + 1)) : ℝ × ℝ).2 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB d * (t + 1)) : ℝ × ℝ).1 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA d * (t + 1), cC d * (t + 1)) : ℝ × ℝ).2 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).2)
      = cA d * (t + 1) * (cC d * (t + 1)) := by ring
  have hne : (((cA d * (t + 1), cC d * (t + 1)) : ℝ × ℝ).1 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB d * (t + 1)) : ℝ × ℝ).2 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB d * (t + 1)) : ℝ × ℝ).1 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA d * (t + 1), cC d * (t + 1)) : ℝ × ℝ).2 - ((cA d * (t + 1), (0 : ℝ)) : ℝ × ℝ).2)
      ≠ 0 := by rw [hdet]; exact (mul_pos hu' hw').ne'
  -- copy of `CollarE1.vol_tgt` with `WS`, `hull_WS` replaced by `DS`, `hull_DS`
  have hc : (tgtT hd h2t).carrier
      = (triC (d + 2) (hfr hd) (cA d * (t + 1), 0) (cA d * (t + 1), cC d * (t + 1))
          (0, cB d * (t + 1)) hne).carrier := by
    rw [carrier_tgtT hd h2t, carrier_triC]
    show Phi (d + 2) '' DS _ _ _ = _
    rw [← Erdos634.Draft.WtoDeltaF.hull_DS _ _ _ hu' hv' hvw']
  rw [hc, vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  rw [hdet, abs_of_pos (mul_pos hu' hw')]

/-! ## The tilings of the regions -/

theorem row_ge {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    cB d + cL d ≤ cB d + cL d + (d + 2) * xa d t := by
  have h := mul_nonneg (hFpos hd).le (xa_pos hd h2t).le
  linarith

/-- `Y1`: `x_a` rows of height `F` (`F` columns of width `F² − 1`) below `t + 1` rows of height `F² − 1`
(`F² − 1` columns of width `F`); the patterns of `CollarE1.RT1` and `CollarE1.RT2` -/
def RY1 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) (k1 l1 k2 l2 : ℕ) (hk1 : (k1 : ℝ) + 1 = d + 2)
    (hl1 : (l1 : ℝ) + 1 = xa d t) (hk2 : (k2 : ℝ) + 1 = (d + 2) ^ 2 - 1) (hl2 : (l2 : ℝ) + 1 = t + 1) :
    RTiling (Phi (d + 2) '' Y1 d t) (Mod hd) (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) :=
  -- `S2G.vstack` of two shifted grids; the four side conditions are the identities
  -- `A = (F² − 1) F`, `F x_a`, `A = F (F² − 1)`, `H = (F² − 1)(t + 1) + (B + L₀ + F x_a)`
  Erdos634.Draft.S2G.vstack (hfr hd) (row_ge hd h2t) (cH_ge' hd h2t)
    (shift_rect (grid (hfr hd) (hbpos hd) (hFpos hd) (cellA hd) k1 l1) (cA d * t) (cB d + cL d)
      (cA d * t + cA d) (cB d + cL d + (d + 2) * xa d t)
      (by rw [hk1]; simp only [cA]; ring) (by rw [hl1]; ring))
    (shift_rect (grid (hfr hd) (hFpos hd) (hbpos hd) (cellB hd) k2 l2) (cA d * t)
      (cB d + cL d + (d + 2) * xa d t) (cA d * t + cA d) (cH d t)
      (by rw [hk2]; simp only [cA]; ring) (by rw [hl2]; simp only [cH, cB, cL, xa]; ring))

theorem detY {d : ℝ} (hd : 0 ≤ d) (t : ℝ) :
    ((uB d t).1 - (uA d t).1) * ((uC d t).2 - (uA d t).2)
      - ((uC d t).1 - (uA d t).1) * ((uB d t).2 - (uA d t).2) ≠ 0 := by
  have e : ((uB d t).1 - (uA d t).1) * ((uC d t).2 - (uA d t).2)
      - ((uC d t).1 - (uA d t).1) * ((uB d t).2 - (uA d t).2) = -(cA d * (d + 2) ^ 2) := by
    simp only [uA, uB, uC]; ring
  rw [e]
  exact neg_ne_zero.mpr (mul_pos (cA_pos hd (le_refl (0 : ℝ))) (pow_pos (hFpos hd) 2)).ne'

/-- `Y2`, the tile at scale `F` (the pattern of `CollarE1.RT3`) -/
def RY2 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = d + 2) :
    RTiling (Phi (d + 2) '' Y2 d t) (Mod hd) (k * k) :=
  -- the three side conditions are `|uB − uA|² = (F·F)²`, `|uC − uB|² = (F (F² − 1))²`,
  -- `|uC − uA|² = F² · F⁴` in the skew norm
  scaledRT (d + 2) (hfr hd) (uA d t) (uB d t) (uC d t) k hk0 (detY hd t) _
    (baseTri_cong _ _ (d + 2) ((d + 2) ^ 2 - 1) (((d + 2) ^ 2) ^ 2) (hFpos hd) (hbpos hd) (hab_id hd) _ _ _ k hk0 _
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [uA, uB, uC, cA]
          field_simp
          ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [uA, uB, uC, cA]
          field_simp
          ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [uA, uB, uC, cA]
          field_simp
          ring))

/-! ## Assembly: the nine regions fill `T_{t+1}` -/

/-- the regions in the plane; the two parallelograms of the cap are given as sets -/
def regionL (d t : ℝ) (S6 S7 : Set Plane) : Fin 9 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (d + 2) '' Y0 d t
  | ⟨1, _⟩ => Phi (d + 2) '' Y1 d t
  | ⟨2, _⟩ => Phi (d + 2) '' Y2 d t
  | ⟨3, _⟩ => Phi (d + 2) '' Sh (vsh d t) (Z3 d 0)
  | ⟨4, _⟩ => Phi (d + 2) '' Sh (vsh d t) (Z4 d 0)
  | ⟨5, _⟩ => Phi (d + 2) '' Sh (vsh d t) (Z5 d 0)
  | ⟨6, _⟩ => S6
  | ⟨7, _⟩ => S7
  | ⟨8, _⟩ => Phi (d + 2) '' Sh (vsh d t) (Z8 d 0)
  | ⟨k + 9, h⟩ => absurd h (by omega)

/-- **The layer step, real parameters.**  A tiling of `T_t` by `n₀` tiles gives a dissection of `T_{t+1}`
(`F ≤ 2t`; `t` may be smaller than `F`).  The counts: `k1 + 1 = F`, `l1 + 1 = x_a`, `k2 + 1 = F² − 1`, `l2 + 1 = t + 1`,
`k3 = F`, and `k4, k6, l6, k7` as in `CollarE1.collar_real`. -/
theorem layer_real {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) (n0 k1 l1 k2 l2 k3 k4 k6 l6 k7 : ℕ)
    (hn0 : (n0 : ℝ) = cC d * t ^ 2)
    (hk1 : (k1 : ℝ) + 1 = d + 2) (hl1 : (l1 : ℝ) + 1 = xa d t)
    (hk2 : (k2 : ℝ) + 1 = (d + 2) ^ 2 - 1) (hl2 : (l2 : ℝ) + 1 = t + 1)
    (hk30 : 0 < k3) (hk3 : (k3 : ℝ) = d + 2) (hk40 : 0 < k4) (hk4 : (k4 : ℝ) = d + 1)
    (hk6 : (k6 : ℝ) + 1 = (d + 2) * (d + 1)) (hl6 : (l6 : ℝ) + 1 = d + 1) (hk7 : (k7 : ℝ) + 1 = d + 1)
    (R0 : RTiling (Phi (d + 2) '' DS (cA d * t) (cB d * t) (cC d * t)) (Mod hd) n0) :
    ∃ (N : ℕ) (D : CongruentDissection N), (N : ℝ) = cC d * (t + 1) ^ 2 ∧ D.model = Mod hd ∧
      D.target = tgtT hd h2t := by
  have h0 : (0 : ℝ) ≤ 0 := le_refl 0
  obtain ⟨S6, ⟨R6⟩, h6⟩ := shift_sub_exists (vsh d t) (RT6 hd h0 k6 l6 hk6 hl6)
  obtain ⟨S7, ⟨R7⟩, h7⟩ := shift_sub_exists (vsh d t) (RT7 hd h0 k7 hk7)
  have R0s : RTiling (Phi (d + 2) '' Y0 d t) (Mod hd) n0 := shiftR R0 (0, cB d)
  have Rall : ∀ a : Fin 9, RTiling (regionL d t S6 S7 a) (Mod hd)
      (cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a) := fun a => match a with
    | ⟨0, _⟩ => R0s
    | ⟨1, _⟩ => RY1 hd h2t k1 l1 k2 l2 hk1 hl1 hk2 hl2
    | ⟨2, _⟩ => RY2 hd t k3 hk30 hk3
    | ⟨3, _⟩ => shiftR (RT3 hd h0 k3 hk30 hk3) (vsh d t)
    | ⟨4, _⟩ => shiftR (RT4 hd h0 k4 hk40 hk4) (vsh d t)
    | ⟨5, _⟩ => shiftR (RT5 hd h0 k4 hk40 hk4) (vsh d t)
    | ⟨6, _⟩ => R6
    | ⟨7, _⟩ => R7
    | ⟨8, _⟩ => shiftR (RT8 hd h0 k4 hk40 hk4) (vsh d t)
    | ⟨k + 9, h⟩ => absurd h (by omega)
  have sub_all : ∀ a : Fin 9, regionL d t S6 S7 a ⊆ Phi (d + 2) '' Yf d t a := fun a => match a with
    | ⟨0, _⟩ => subset_rfl
    | ⟨1, _⟩ => subset_rfl
    | ⟨2, _⟩ => subset_rfl
    | ⟨3, _⟩ => subset_rfl
    | ⟨4, _⟩ => subset_rfl
    | ⟨5, _⟩ => subset_rfl
    | ⟨6, _⟩ => h6
    | ⟨7, _⟩ => h7
    | ⟨8, _⟩ => subset_rfl
    | ⟨k + 9, h⟩ => absurd h (by omega)
  have hS_all : ∀ a b : Fin 9, a ≠ b →
      Disjoint (interior (regionL d t S6 S7 a)) (interior (regionL d t S6 S7 b)) := fun a b hab =>
    (disjoint_image' (hfr hd) (dY_all hd h2t a b hab)).mono (interior_mono (sub_all a)) (interior_mono (sub_all b))
  have hsub_all : ∀ a : Fin 9, regionL d t S6 S7 a ⊆ (tgtT hd h2t).carrier := fun a => by
    rw [carrier_tgtT hd h2t]
    exact (sub_all a).trans (Set.image_mono (Yf_sub hd h2t a))
  have hsumR : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ℝ)
      = cC d * (t + 1) ^ 2 := by
    rw [sum_cnt]
    push_cast
    rw [hn0, hk1, hl1, hk2, hl2, hk3, hk4, hk6, hl6, hk7]
    simp only [cC, xa]; ring
  have hvol : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ENNReal)
        * MeasureTheory.volume (Mod hd).carrier
      = MeasureTheory.volume (tgtT hd h2t).carrier := by
    have hNR : (0 : ℝ) ≤ ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    rw [volMod hd h0, vol_tgtT hd h2t, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR, hsumR]
    congr 2
    simp only [cA, cC]; ring
  obtain ⟨D, hM, hT⟩ := Erdos634.Draft.S2L.pack_exists (M := Mod hd) (T := tgtT hd h2t) (regionL d t S6 S7) _
    Rall hS_all hsub_all hvol
  exact ⟨_, D, hsumR, hM, hT⟩

/-! ## The step for naturals -/

/-- **The layer step**: `T_M → T_{M+1}` for the member `(1, f)`, `f = g + 2`, `f ≤ 2M`. -/
theorem layer_step (g M : ℕ) (hM : g + 2 ≤ 2 * M) (hT : TClosed (g + 2) (by omega) M) :
    TClosed (g + 2) (by omega) (M + 1) := by
  obtain ⟨R⟩ := hT
  have hd : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have h2t : (g : ℝ) + 2 ≤ 2 * (M : ℝ) := by exact_mod_cast hM
  have h0 : (0 : ℝ) ≤ 0 := le_refl 0
  have hf : 2 ≤ g + 2 := by omega
  have hFr := Erdos634.Draft.WPgramF.hF (g + 2) hf
  have eF : ((g + 2 : ℕ) : ℝ) = (g : ℝ) + 2 := by push_cast; ring
  -- the given tiling, in the notation of this file
  have hS : Phi ((g + 2 : ℕ) : ℝ) '' DS (((g + 2 : ℕ) : ℝ) * (((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ))
      ((2 * ((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ)) ((3 * ((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ))
      = Phi ((g : ℝ) + 2) '' DS (cA (g : ℝ) * (M : ℝ)) (cB (g : ℝ) * (M : ℝ)) (cC (g : ℝ) * (M : ℝ)) := by
    simp only [cA, cB, cC]; push_cast; rfl
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hFr
  obtain ⟨s1, s2, s3⟩ := Mod_sides hd h0
  have hMF0 : HasSides (Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) hFr) ((g + 2 : ℕ) : ℝ)
      (((g + 2 : ℕ) : ℝ) ^ 2) (((g + 2 : ℕ) : ℝ) ^ 2 - 1) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact m2,
      by simp only [Equiv.refl_apply]; rw [dist_comm]; exact m3, by simp only [Equiv.refl_apply]; exact m1⟩
  have hMF : (Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) hFr).Congruent (Mod hd) :=
    congruent_of_hasSides' (hasSides_rot (hasSides_rot (hasSides_swap hMF0)))
      (by rw [s1, eF]) (by rw [s2, eF]) (by rw [s3, eF])
  have h1 : 1 ≤ 3 * (g + 2) ^ 2 := by nlinarith
  have R0 : RTiling (Phi ((g : ℝ) + 2) '' DS (cA (g : ℝ) * (M : ℝ)) (cB (g : ℝ) * (M : ℝ)) (cC (g : ℝ) * (M : ℝ)))
      (Mod hd) ((3 * (g + 2) ^ 2 - 1) * M ^ 2) := RegionTiling.remodel (RTiling.cast hS R) hMF
  have hn0 : (((3 * (g + 2) ^ 2 - 1) * M ^ 2 : ℕ) : ℝ) = cC (g : ℝ) * (M : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub h1]; simp only [cC]; push_cast; ring
  obtain ⟨k2, hk2n⟩ : ∃ k2, k2 + 1 = (g + 2) ^ 2 - 1 :=
    ⟨(g + 2) ^ 2 - 1 - 1, Nat.sub_add_cancel (Nat.le_sub_of_add_le (by nlinarith))⟩
  obtain ⟨k6, hk6n⟩ : ∃ k6, k6 + 1 = (g + 2) * (g + 1) :=
    ⟨(g + 2) * (g + 1) - 1, Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))⟩
  have hl1 : ((((2 * M - (g + 2)) * (g + 2) : ℕ)) : ℝ) + 1 = xa (g : ℝ) (M : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hM]; simp only [xa]; push_cast; ring
  have hk2 : (k2 : ℝ) + 1 = ((g : ℝ) + 2) ^ 2 - 1 := by
    have h4 : 1 ≤ (g + 2) ^ 2 := by nlinarith
    have h := congrArg (Nat.cast : ℕ → ℝ) hk2n
    rw [Nat.cast_sub h4] at h
    push_cast at h; linarith
  have hk6 : (k6 : ℝ) + 1 = ((g : ℝ) + 2) * ((g : ℝ) + 1) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hk6n
    push_cast at h; linarith
  obtain ⟨N, D, hN, hMd, hTd⟩ := layer_real hd h2t _ (g + 1) ((2 * M - (g + 2)) * (g + 2)) k2 M (g + 2) (g + 1)
    k6 g g hn0 (by push_cast; ring) hl1 hk2 rfl (by omega) (by push_cast; ring) (by omega) (by push_cast; ring)
    hk6 rfl rfl R0
  -- the number of tiles
  have hNn : N = (3 * (g + 2) ^ 2 - 1) * (M + 1) ^ 2 := by
    have hc : (N : ℝ) = (((3 * (g + 2) ^ 2 - 1) * (M + 1) ^ 2 : ℕ) : ℝ) := by
      rw [hN, Nat.cast_mul, Nat.cast_sub h1]; simp only [cC]; push_cast; ring
    exact_mod_cast hc
  subst hNn
  obtain ⟨t12, t20, t01⟩ := tgtT_sides hd h2t
  refine TClosed_of_dissection (g + 2) hf (M + 1) (by omega) D ?_ ?_
  · have hTs : HasSides D.target (((M : ℝ) + 1) * ((g : ℝ) + 2) ^ 3) (((M : ℝ) + 1) * ((g : ℝ) + 2) ^ 3)
        (cC (g : ℝ) * ((M : ℝ) + 1)) :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hTd]; exact t12,
        by simp only [Equiv.refl_apply]; rw [hTd]; exact t20,
        by simp only [Equiv.refl_apply]; rw [hTd]; exact t01⟩
    exact hasSides_congr hTs (by push_cast; ring) (by push_cast; ring) (by simp only [cC]; push_cast; ring)
  · have hMs : HasSides D.model (((g : ℝ) + 2) ^ 2 - 1) (((g : ℝ) + 2) ^ 2) ((g : ℝ) + 2) :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hMd]; exact s2,
        by simp only [Equiv.refl_apply]; rw [hMd, dist_comm]; exact s3,
        by simp only [Equiv.refl_apply]; rw [hMd]; exact s1⟩
    exact hasSides_congr (hasSides_rot (hasSides_rot (hasSides_swap hMs))) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)

/-- the layer step for the member `(1, f)`, any `f ≥ 2` -/
theorem tClosed_succ (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : f ≤ 2 * M) (hT : TClosed f hf M) :
    TClosed f hf (M + 1) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  exact layer_step g M hM hT

/-! ## The scales with a tiling form an up-set -/

/-- **`prop:layer` (a).**  For `f ≥ 2` and `f ≤ 2M`: a tiling of the base-β target of `(1, f)` at scale `M` gives one
at scale `M + 1`. -/
theorem betaTilable_succ (f M : ℕ) (hf : 2 ≤ f) (hM : f ≤ 2 * M) :
    BetaTilable 1 f M → BetaTilable 1 f (M + 1) := by
  intro h
  have hM1 : 1 ≤ M := by omega
  exact betaTilable_of_TClosed f hf (M + 1) (by omega)
    (tClosed_succ f hf M hM (TClosed_of_betaTilable f hf M hM1 h))

/-- **`prop:layer` (b).**  The scales at which the base-β target of `(1, f)` has a tiling form an up-set: a tiling at
a scale `M ≥ 1` forces `f < 2M` (`SideRun.not_betaTilable_e1_le_half`), and then the layer applies at every step. -/
theorem betaTilable_mono (f : ℕ) (hf : 2 ≤ f) {M M' : ℕ} (hM : 1 ≤ M) (h : M ≤ M') :
    BetaTilable 1 f M → BetaTilable 1 f M' := by
  intro hB
  have hfM : f ≤ 2 * M := by
    by_contra hc
    exact Erdos634.Draft.SideRun.not_betaTilable_e1_le_half f M hM (by omega) hB
  have key : ∀ n, M ≤ n → BetaTilable 1 f n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hB
    | succ n hn ih => exact betaTilable_succ f n hf (by omega) ih
  exact key M' h

/-- **`prop:layer` (c).**  The threshold statement of the member `(1, f)` (a tiling of the base-β target at scale `M`
if and only if `M ≥ f`) holds at every scale if and only if there is no tiling at the single scale `f − 1`.
(For `f = 2` the right-hand side is the known `¬ BetaTilable 1 2 1`.)  The existence half for `M ≥ f` is
`CollarE1.thresholdAt_e1_of_ge` (D. Paliy's construction). -/
theorem threshold_e1_iff_top (f : ℕ) (hf : 2 ≤ f) :
    (∀ M, 1 ≤ M → ThresholdAt 1 f M) ↔ ¬ BetaTilable 1 f (f - 1) := by
  constructor
  · intro h hB
    have h1 := (h (f - 1) (by omega)).mp hB
    omega
  · intro hno M hM
    by_cases h1 : f ≤ M
    · exact thresholdAt_e1_of_ge f hf h1
    · exact ⟨fun hB => absurd (betaTilable_mono f hf (M' := f - 1) hM (by omega) hB) hno,
        fun hfM => absurd hfM h1⟩

/-- **`prop:layer` (b), closed form.**  For `f ≥ 2` there is a scale `Ms` with `f < 2 Ms ≤ 2f` such that, for `M ≥ 1`,
the base-β target of `(1, f)` at scale `M` has a tiling if and only if `Ms ≤ M`.  (`Ms` is the least scale with a
tiling; nothing here says which value in `(f/2, f]` it takes for `f ≥ 4`.) -/
theorem exists_min_scale (f : ℕ) (hf : 2 ≤ f) :
    ∃ Ms : ℕ, f < 2 * Ms ∧ Ms ≤ f ∧ ∀ M, 1 ≤ M → (BetaTilable 1 f M ↔ Ms ≤ M) := by
  classical
  have hex : ∃ M, 1 ≤ M ∧ BetaTilable 1 f M :=
    ⟨f, by omega, Erdos634.Draft.CollarE1.betaTilable_e1 f hf f le_rfl⟩
  refine ⟨Nat.find hex, ?_, ?_, ?_⟩
  · obtain ⟨h1, hB⟩ := Nat.find_spec hex
    by_contra hc
    exact Erdos634.Draft.SideRun.not_betaTilable_e1_le_half f _ h1 (by omega) hB
  · exact Nat.find_min' hex ⟨by omega, Erdos634.Draft.CollarE1.betaTilable_e1 f hf f le_rfl⟩
  · intro M hM
    constructor
    · intro hB
      exact Nat.find_min' hex ⟨hM, hB⟩
    · intro h
      obtain ⟨h1, hB⟩ := Nat.find_spec hex
      exact betaTilable_mono f hf h1 h hB

end

/-! ## Witnesses: the hypotheses of the theorems above are satisfied

At `f = 2`, `M = 2` the hypothesis of `betaTilable_succ` holds (the tiling at the scale `M = f` is `CollarE1`'s), so
the theorem produces a tiling at scale `3`; and at `f = 2` both sides of `threshold_e1_iff_top` are true (the right-hand
side is `SideRun.not_betaTilable_e1_le_half`).  For `M < f` the hypothesis `BetaTilable 1 f M` is exactly the open
question (`f ≥ 4`), so no witness exists there. -/
example : BetaTilable 1 2 3 :=
  betaTilable_succ 2 2 (le_refl 2) (by norm_num)
    (Erdos634.Draft.CollarE1.betaTilable_e1 2 (le_refl 2) 2 (le_refl 2))

example : ∀ M, 1 ≤ M → ThresholdAt 1 2 M :=
  (threshold_e1_iff_top 2 (le_refl 2)).mpr
    (show ¬ BetaTilable 1 2 1 from Erdos634.Draft.SideRun.not_betaTilable_e1_le_half 2 1 (le_refl 1) (by norm_num))

end Erdos634.Draft.LayerE1

#print axioms Erdos634.Draft.LayerE1.layer_real
#print axioms Erdos634.Draft.LayerE1.layer_step
#print axioms Erdos634.Draft.LayerE1.betaTilable_succ
#print axioms Erdos634.Draft.LayerE1.betaTilable_mono
#print axioms Erdos634.Draft.LayerE1.threshold_e1_iff_top
#print axioms Erdos634.Draft.LayerE1.exists_min_scale
