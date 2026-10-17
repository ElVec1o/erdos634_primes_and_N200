/-
Draft/LaczFamily.lean — **Laczkovich's macro-dissection family** (Lead 1 of private/ROOM/DISCOVERY/leads4.md).
Tile `(a, b, c) = (u², v² - u², uv)`, `γ = 2α`, `u < v < 2u`.  If `(v²-u²)³ v² > u⁸` the isosceles triangle with base angles
`α` is tiled by `(v²-u²) · (K v (u⁴ - u²v² + v⁴))²` copies of the tile for every `K ≥ 1` with
`K ((v²-u²)³ v² - u⁸) = u v x + (v²-u²) y`, `x, y ≥ 1` (`lacz_family`); unconditionally for `K = 2 (v²-u²) u v`
(`lacz_family_uncond`).  Instances: `N = 5 · 183²` for `(u, v) = (2, 3)` (control: the known tiling of 167445) and
`N = 16 · 2405² = 92,544,400` for `(u, v) = (3, 5)` (first tile `u ≥ 3` with a tiling of this shape).
The macro-dissection (seven tile-similar triangles of scales `K·{u⁵v, u⁶, u⁴b, u³vb, uvb², u²v²b, v²b²}` + one
`α`-parallelogram `U × V`, `U = K u⁵ v b`, `V = K ((v²-u²)³v² - u⁸)`) is due to M. Laczkovich (reported in Beeson,
"Tilings of an isosceles triangle", sec. 9; our reconstruction `rust/g3g/src/bin/recon.rs`, uniformization in `(u,v)` by
the DISCOVERY room).  The geometry is `Draft.LaczGeom`, the tilings of the pieces are `Draft.LaczTile`; here: assembly,
volume count, natural-number statement.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.LaczTile
import Erdos634.Draft.TileCountFamilies

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.LaczFamily
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.S2L (pack_exists)

theorem cross_T {x y z : ℝ} : cross (P5 x y z) (P4 x y z) (P9 x y z)
    = -(z ^ 2 * x * y ^ 3 * (bq x y) ^ 2 * (q1 x y) ^ 2) := by ug; ring

theorem det_T {x y z : ℝ} (h : LP x y z) : cross (P5 x y z) (P4 x y z) (P9 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  rw [cross_T]; exact neg_ne_zero.mpr (by positivity)

/-- the target: the isosceles triangle `P5 P4 P9`. -/
noncomputable def tgt {x y z : ℝ} (h : LP x y z) : Tri :=
  triC (fr x y) (hfr h) (P5 x y z) (P4 x y z) (P9 x y z) (fun hh => det_T h (by unfold cross; linarith))

theorem tgt_carrier {x y z : ℝ} (h : LP x y z) : (tgt h).carrier = Phi (fr x y) '' HT x y z :=
  carrier_triC _ _ _ _ _ _

open MeasureTheory in
theorem volMod {x y z : ℝ} (h : LP x y z) : volume (Mod h).carrier
    = ENNReal.ofReal (|sD (fr x y) / (2 * fr x y)| * ((x * y) * bq x y)) * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hX : 0 < (x * y) * bq x y := mul_pos (hcc h) (hbb h)
  rw [← abs_of_pos hX]
  congr 1
  dsimp only
  ring

open MeasureTheory in
theorem volTgt {x y z : ℝ} (h : LP x y z) : volume (tgt h).carrier
    = ENNReal.ofReal (|sD (fr x y) / (2 * fr x y)| * (z ^ 2 * x * y ^ 3 * (bq x y) ^ 2 * (q1 x y) ^ 2))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold tgt
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hX : 0 < z ^ 2 * x * y ^ 3 * (bq x y) ^ 2 * (q1 x y) ^ 2 := by positivity
  rw [← abs_of_pos hX, ← abs_neg]
  congr 1
  have := cross_T (x := x) (y := y) (z := z)
  unfold cross at this
  linarith

open MeasureTheory in
theorem hvol_all {x y z : ℝ} (h : LP x y z) (N : ℕ) (hN : (N : ℝ) = z ^ 2 * y ^ 2 * bq x y * (q1 x y) ^ 2) :
    (N : ENNReal) * volume (Mod h).carrier = volume (tgt h).carrier := by
  rw [volMod h, volTgt h, ← mul_assoc, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 2
  rw [hN]; ring

theorem dTR {f : ℝ} (hf : 1 < 4 * f ^ 2) {A R R' : Set (ℝ × ℝ)} (hd : Disjoint (interior A) (interior R'))
    (hsub : R ⊆ R') : Disjoint (interior (Phi f '' A)) (interior (Phi f '' R)) :=
  (disjoint_image' hf hd).mono_right (interior_mono (Set.image_mono hsub))

/-- the nine regions: seven triangles, the lower bricks, the upper bricks. -/
noncomputable def Sset {x y z : ℝ} (kA lA kB lB : ℕ) : Fin 9 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (fr x y) '' Hbl x y z
  | ⟨1, _⟩ => Phi (fr x y) '' Hlg x y z
  | ⟨2, _⟩ => Phi (fr x y) '' Hgr x y z
  | ⟨3, _⟩ => Phi (fr x y) '' Hlb x y z
  | ⟨4, _⟩ => Phi (fr x y) '' Hor x y z
  | ⟨5, _⟩ => Phi (fr x y) '' Hpk x y z
  | ⟨6, _⟩ => Phi (fr x y) '' Hrd x y z
  | ⟨7, _⟩ => Phi (fr x y) '' Rect 0 (x * y * ((kA : ℝ) + 1)) 0 (bq x y * ((lA : ℝ) + 1))
  | ⟨8, _⟩ => Phi (fr x y) '' Rect 0 (bq x y * ((kB : ℝ) + 1)) (bq x y * ((lA : ℝ) + 1))
      (x * y * ((lB : ℝ) + 1) + bq x y * ((lA : ℝ) + 1))
  | ⟨k + 9, hk⟩ => absurd hk (by omega)

def cntS (k0 k1 k2 k3 k4 k5 k6 kA lA kB lB : ℕ) : Fin 9 → ℕ := fun i => match i with
  | ⟨0, _⟩ => k0 * k0
  | ⟨1, _⟩ => k1 * k1
  | ⟨2, _⟩ => k2 * k2
  | ⟨3, _⟩ => k3 * k3
  | ⟨4, _⟩ => k4 * k4
  | ⟨5, _⟩ => k5 * k5
  | ⟨6, _⟩ => k6 * k6
  | ⟨7, _⟩ => 2 * (kA + 1) * (lA + 1)
  | ⟨8, _⟩ => 2 * (kB + 1) * (lB + 1)
  | ⟨k + 9, hk⟩ => absurd hk (by omega)

section asm
variable {x y z : ℝ} (h : LP x y z) {kA lA kB lB : ℕ}
  (eA : (kA : ℝ) + 1 = z * x ^ 4 * bq x y) (eB : (kB : ℝ) + 1 = z * x ^ 5 * y)
  (eR : bq x y * ((lA : ℝ) + 1) + x * y * ((lB : ℝ) + 1) = z * Vp x y)
include h eA eB eR

theorem subRA : Rect 0 (x * y * ((kA : ℝ) + 1)) 0 (bq x y * ((lA : ℝ) + 1)) ⊆ Rw x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  rintro p ⟨h1, h2, h3, h4⟩
  have e1 : x * y * ((kA : ℝ) + 1) = Ub x y z := by rw [eA]; unfold Ub; ring
  have e2 : 0 ≤ x * y * ((lB : ℝ) + 1) := by positivity
  refine ⟨h1, by rw [← e1]; exact h2, h3, ?_⟩
  unfold Vb; nlinarith

theorem subRB : Rect 0 (bq x y * ((kB : ℝ) + 1)) (bq x y * ((lA : ℝ) + 1))
      (x * y * ((lB : ℝ) + 1) + bq x y * ((lA : ℝ) + 1)) ⊆ Rw x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  rintro p ⟨h1, h2, h3, h4⟩
  have e1 : bq x y * ((kB : ℝ) + 1) = Ub x y z := by rw [eB]; unfold Ub; ring
  have e2 : 0 ≤ bq x y * ((lA : ℝ) + 1) := by positivity
  refine ⟨h1, by rw [← e1]; exact h2, by linarith, ?_⟩
  unfold Vb; nlinarith

theorem dRR : Disjoint (interior (Phi (fr x y) '' Rect 0 (x * y * ((kA : ℝ) + 1)) 0 (bq x y * ((lA : ℝ) + 1))))
    (interior (Phi (fr x y) '' Rect 0 (bq x y * ((kB : ℝ) + 1)) (bq x y * ((lA : ℝ) + 1))
      (x * y * ((lB : ℝ) + 1) + bq x y * ((lA : ℝ) + 1)))) :=
  disjoint_image' (hfr h) (interior_disj_snd (bq x y * ((lA : ℝ) + 1)) (fun p hp => hp.2.2.2) (fun p hp => hp.2.2.1))

theorem hS_all : ∀ a b : Fin 9, a ≠ b →
    Disjoint (interior (Sset (x := x) (y := y) (z := z) kA lA kB lB a)) (interior (Sset (x := x) (y := y) (z := z) kA lA kB lB b)) := by
  have hf := hfr h
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => disjoint_image' hf (d_0_1 h)
  | ⟨0, _⟩, ⟨2, _⟩ => disjoint_image' hf (d_0_2 h)
  | ⟨0, _⟩, ⟨3, _⟩ => disjoint_image' hf (d_0_3 h)
  | ⟨0, _⟩, ⟨4, _⟩ => disjoint_image' hf (d_0_4 h)
  | ⟨0, _⟩, ⟨5, _⟩ => disjoint_image' hf (d_0_5 h)
  | ⟨0, _⟩, ⟨6, _⟩ => disjoint_image' hf (d_0_6 h)
  | ⟨0, _⟩, ⟨7, _⟩ => dTR hf (d_0_7 h) (subRA h eA eB eR)
  | ⟨0, _⟩, ⟨8, _⟩ => dTR hf (d_0_7 h) (subRB h eA eB eR)
  | ⟨1, _⟩, ⟨0, _⟩ => (disjoint_image' hf (d_0_1 h)).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => disjoint_image' hf (d_1_2 h)
  | ⟨1, _⟩, ⟨3, _⟩ => disjoint_image' hf (d_1_3 h)
  | ⟨1, _⟩, ⟨4, _⟩ => disjoint_image' hf (d_1_4 h)
  | ⟨1, _⟩, ⟨5, _⟩ => disjoint_image' hf (d_1_5 h)
  | ⟨1, _⟩, ⟨6, _⟩ => disjoint_image' hf (d_1_6 h)
  | ⟨1, _⟩, ⟨7, _⟩ => dTR hf (d_1_7 h) (subRA h eA eB eR)
  | ⟨1, _⟩, ⟨8, _⟩ => dTR hf (d_1_7 h) (subRB h eA eB eR)
  | ⟨2, _⟩, ⟨0, _⟩ => (disjoint_image' hf (d_0_2 h)).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (disjoint_image' hf (d_1_2 h)).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => disjoint_image' hf (d_2_3 h)
  | ⟨2, _⟩, ⟨4, _⟩ => disjoint_image' hf (d_2_4 h)
  | ⟨2, _⟩, ⟨5, _⟩ => disjoint_image' hf (d_2_5 h)
  | ⟨2, _⟩, ⟨6, _⟩ => disjoint_image' hf (d_2_6 h)
  | ⟨2, _⟩, ⟨7, _⟩ => dTR hf (d_2_7 h) (subRA h eA eB eR)
  | ⟨2, _⟩, ⟨8, _⟩ => dTR hf (d_2_7 h) (subRB h eA eB eR)
  | ⟨3, _⟩, ⟨0, _⟩ => (disjoint_image' hf (d_0_3 h)).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (disjoint_image' hf (d_1_3 h)).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (disjoint_image' hf (d_2_3 h)).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => disjoint_image' hf (d_3_4 h)
  | ⟨3, _⟩, ⟨5, _⟩ => disjoint_image' hf (d_3_5 h)
  | ⟨3, _⟩, ⟨6, _⟩ => disjoint_image' hf (d_3_6 h)
  | ⟨3, _⟩, ⟨7, _⟩ => dTR hf (d_3_7 h) (subRA h eA eB eR)
  | ⟨3, _⟩, ⟨8, _⟩ => dTR hf (d_3_7 h) (subRB h eA eB eR)
  | ⟨4, _⟩, ⟨0, _⟩ => (disjoint_image' hf (d_0_4 h)).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (disjoint_image' hf (d_1_4 h)).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (disjoint_image' hf (d_2_4 h)).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (disjoint_image' hf (d_3_4 h)).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨4, _⟩, ⟨5, _⟩ => disjoint_image' hf (d_4_5 h)
  | ⟨4, _⟩, ⟨6, _⟩ => disjoint_image' hf (d_4_6 h)
  | ⟨4, _⟩, ⟨7, _⟩ => dTR hf (d_4_7 h) (subRA h eA eB eR)
  | ⟨4, _⟩, ⟨8, _⟩ => dTR hf (d_4_7 h) (subRB h eA eB eR)
  | ⟨5, _⟩, ⟨0, _⟩ => (disjoint_image' hf (d_0_5 h)).symm
  | ⟨5, _⟩, ⟨1, _⟩ => (disjoint_image' hf (d_1_5 h)).symm
  | ⟨5, _⟩, ⟨2, _⟩ => (disjoint_image' hf (d_2_5 h)).symm
  | ⟨5, _⟩, ⟨3, _⟩ => (disjoint_image' hf (d_3_5 h)).symm
  | ⟨5, _⟩, ⟨4, _⟩ => (disjoint_image' hf (d_4_5 h)).symm
  | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hab
  | ⟨5, _⟩, ⟨6, _⟩ => disjoint_image' hf (d_5_6 h)
  | ⟨5, _⟩, ⟨7, _⟩ => dTR hf (d_5_7 h) (subRA h eA eB eR)
  | ⟨5, _⟩, ⟨8, _⟩ => dTR hf (d_5_7 h) (subRB h eA eB eR)
  | ⟨6, _⟩, ⟨0, _⟩ => (disjoint_image' hf (d_0_6 h)).symm
  | ⟨6, _⟩, ⟨1, _⟩ => (disjoint_image' hf (d_1_6 h)).symm
  | ⟨6, _⟩, ⟨2, _⟩ => (disjoint_image' hf (d_2_6 h)).symm
  | ⟨6, _⟩, ⟨3, _⟩ => (disjoint_image' hf (d_3_6 h)).symm
  | ⟨6, _⟩, ⟨4, _⟩ => (disjoint_image' hf (d_4_6 h)).symm
  | ⟨6, _⟩, ⟨5, _⟩ => (disjoint_image' hf (d_5_6 h)).symm
  | ⟨6, _⟩, ⟨6, _⟩ => absurd rfl hab
  | ⟨6, _⟩, ⟨7, _⟩ => dTR hf (d_6_7 h) (subRA h eA eB eR)
  | ⟨6, _⟩, ⟨8, _⟩ => dTR hf (d_6_7 h) (subRB h eA eB eR)
  | ⟨7, _⟩, ⟨0, _⟩ => (dTR hf (d_0_7 h) (subRA h eA eB eR)).symm
  | ⟨7, _⟩, ⟨1, _⟩ => (dTR hf (d_1_7 h) (subRA h eA eB eR)).symm
  | ⟨7, _⟩, ⟨2, _⟩ => (dTR hf (d_2_7 h) (subRA h eA eB eR)).symm
  | ⟨7, _⟩, ⟨3, _⟩ => (dTR hf (d_3_7 h) (subRA h eA eB eR)).symm
  | ⟨7, _⟩, ⟨4, _⟩ => (dTR hf (d_4_7 h) (subRA h eA eB eR)).symm
  | ⟨7, _⟩, ⟨5, _⟩ => (dTR hf (d_5_7 h) (subRA h eA eB eR)).symm
  | ⟨7, _⟩, ⟨6, _⟩ => (dTR hf (d_6_7 h) (subRA h eA eB eR)).symm
  | ⟨7, _⟩, ⟨7, _⟩ => absurd rfl hab
  | ⟨7, _⟩, ⟨8, _⟩ => dRR h eA eB eR
  | ⟨8, _⟩, ⟨0, _⟩ => (dTR hf (d_0_7 h) (subRB h eA eB eR)).symm
  | ⟨8, _⟩, ⟨1, _⟩ => (dTR hf (d_1_7 h) (subRB h eA eB eR)).symm
  | ⟨8, _⟩, ⟨2, _⟩ => (dTR hf (d_2_7 h) (subRB h eA eB eR)).symm
  | ⟨8, _⟩, ⟨3, _⟩ => (dTR hf (d_3_7 h) (subRB h eA eB eR)).symm
  | ⟨8, _⟩, ⟨4, _⟩ => (dTR hf (d_4_7 h) (subRB h eA eB eR)).symm
  | ⟨8, _⟩, ⟨5, _⟩ => (dTR hf (d_5_7 h) (subRB h eA eB eR)).symm
  | ⟨8, _⟩, ⟨6, _⟩ => (dTR hf (d_6_7 h) (subRB h eA eB eR)).symm
  | ⟨8, _⟩, ⟨7, _⟩ => (dRR h eA eB eR).symm
  | ⟨8, _⟩, ⟨8, _⟩ => absurd rfl hab
  | ⟨k + 9, hk⟩, _ => absurd hk (by omega)
  | _, ⟨k + 9, hk⟩ => absurd hk (by omega)

theorem hsub_all : ∀ a : Fin 9, Sset (x := x) (y := y) (z := z) kA lA kB lB a ⊆ (tgt h).carrier := by
  rw [tgt_carrier]
  intro a
  exact match a with
  | ⟨0, _⟩ => Set.image_mono (sub_blue h)
  | ⟨1, _⟩ => Set.image_mono (sub_lg h)
  | ⟨2, _⟩ => Set.image_mono (sub_green h)
  | ⟨3, _⟩ => Set.image_mono (sub_lb h)
  | ⟨4, _⟩ => Set.image_mono (sub_orange h)
  | ⟨5, _⟩ => Set.image_mono (sub_pink h)
  | ⟨6, _⟩ => Set.image_mono (sub_red h)
  | ⟨7, _⟩ => Set.image_mono ((subRA h eA eB eR).trans (sub_rect h))
  | ⟨8, _⟩ => Set.image_mono ((subRB h eA eB eR).trans (sub_rect h))
  | ⟨k + 9, hk⟩ => absurd hk (by omega)

end asm

/-! ### the count and the assembly -/
theorem count_alg (x y z kA lA kB lB : ℝ) (eA : kA + 1 = z * x ^ 4 * bq x y) (eB : kB + 1 = z * x ^ 5 * y)
    (eR : bq x y * (lA + 1) + x * y * (lB + 1) = z * Vp x y) :
    (z * x ^ 3 * y * bq x y) * (z * x ^ 3 * y * bq x y) + (z * x ^ 4 * bq x y) * (z * x ^ 4 * bq x y)
      + (z * x * y * (bq x y) ^ 2) * (z * x * y * (bq x y) ^ 2)
      + (z * x ^ 2 * y ^ 2 * bq x y) * (z * x ^ 2 * y ^ 2 * bq x y) + (z * x ^ 6) * (z * x ^ 6)
      + (z * y ^ 2 * (bq x y) ^ 2) * (z * y ^ 2 * (bq x y) ^ 2) + (z * x ^ 5 * y) * (z * x ^ 5 * y)
      + 2 * (kA + 1) * (lA + 1) + 2 * (kB + 1) * (lB + 1) = z ^ 2 * y ^ 2 * bq x y * (q1 x y) ^ 2 := by
  have key : 2 * (kA + 1) * (lA + 1) + 2 * (kB + 1) * (lB + 1) = 2 * z * x ^ 4 * (z * Vp x y) := by
    rw [eA, eB]; linear_combination (2 * z * x ^ 4) * eR
  have e : (z * x ^ 3 * y * bq x y) * (z * x ^ 3 * y * bq x y) + (z * x ^ 4 * bq x y) * (z * x ^ 4 * bq x y)
      + (z * x * y * (bq x y) ^ 2) * (z * x * y * (bq x y) ^ 2)
      + (z * x ^ 2 * y ^ 2 * bq x y) * (z * x ^ 2 * y ^ 2 * bq x y) + (z * x ^ 6) * (z * x ^ 6)
      + (z * y ^ 2 * (bq x y) ^ 2) * (z * y ^ 2 * (bq x y) ^ 2) + (z * x ^ 5 * y) * (z * x ^ 5 * y)
      + 2 * z * x ^ 4 * (z * Vp x y) = z ^ 2 * y ^ 2 * bq x y * (q1 x y) ^ 2 := by
    simp only [Vp, bq, q1]; ring
  linarith

theorem laczReal {x y z : ℝ} (h : LP x y z) (k0 k1 k2 k3 k4 k5 k6 kA lA kB lB : ℕ)
    (p0 : 0 < k0) (p1 : 0 < k1) (p2 : 0 < k2) (p3 : 0 < k3) (p4 : 0 < k4) (p5 : 0 < k5) (p6 : 0 < k6)
    (e0 : (k0 : ℝ) = z * x ^ 3 * y * bq x y) (e1 : (k1 : ℝ) = z * x ^ 4 * bq x y)
    (e2 : (k2 : ℝ) = z * x * y * (bq x y) ^ 2) (e3 : (k3 : ℝ) = z * x ^ 2 * y ^ 2 * bq x y)
    (e4 : (k4 : ℝ) = z * x ^ 6) (e5 : (k5 : ℝ) = z * y ^ 2 * (bq x y) ^ 2) (e6 : (k6 : ℝ) = z * x ^ 5 * y)
    (eA : (kA : ℝ) + 1 = z * x ^ 4 * bq x y) (eB : (kB : ℝ) + 1 = z * x ^ 5 * y)
    (eR : bq x y * ((lA : ℝ) + 1) + x * y * ((lB : ℝ) + 1) = z * Vp x y) :
    ∃ D : CongruentDissection (k0 * k0 + k1 * k1 + k2 * k2 + k3 * k3 + k4 * k4 + k5 * k5 + k6 * k6
        + 2 * (kA + 1) * (lA + 1) + 2 * (kB + 1) * (lB + 1)),
      D.model = Mod h ∧ D.target = tgt h := by
  have R : ∀ a : Fin 9, RTiling (Sset (x := x) (y := y) (z := z) kA lA kB lB a) (Mod h)
      (cntS k0 k1 k2 k3 k4 k5 k6 kA lA kB lB a) := fun a => match a with
    | ⟨0, _⟩ => R_bl h k0 p0 e0
    | ⟨1, _⟩ => R_lg h k1 p1 e1
    | ⟨2, _⟩ => R_gr h k2 p2 e2
    | ⟨3, _⟩ => R_lb h k3 p3 e3
    | ⟨4, _⟩ => R_or h k4 p4 e4
    | ⟨5, _⟩ => R_pk h k5 p5 e5
    | ⟨6, _⟩ => R_rd h k6 p6 e6
    | ⟨7, _⟩ => GA h kA lA
    | ⟨8, _⟩ => GB h kB lB lA
    | ⟨k + 9, hk⟩ => absurd hk (by omega)
  have hsum : ∑ a, cntS k0 k1 k2 k3 k4 k5 k6 kA lA kB lB a
      = k0 * k0 + k1 * k1 + k2 * k2 + k3 * k3 + k4 * k4 + k5 * k5 + k6 * k6
        + 2 * (kA + 1) * (lA + 1) + 2 * (kB + 1) * (lB + 1) := by
    simp [Fin.sum_univ_succ, cntS]
    ring
  have key := pack_exists (M := Mod h) (T := tgt h) (Sset (x := x) (y := y) (z := z) kA lA kB lB)
    (cntS k0 k1 k2 k3 k4 k5 k6 kA lA kB lB) R (hS_all h eA eB eR) (hsub_all h eA eB eR)
    (hvol_all h _ (by
      rw [hsum]
      push_cast
      rw [e0, e1, e2, e3, e4, e5, e6]
      exact count_alg x y z kA lA kB lB eA eB eR))
  rw [hsum] at key
  exact key


/-! ### the natural-number statements -/
open Erdos634.Draft.TileCountFamilies (TileCount tileCount_scale)

/-- `g₀(u,v) = v (u⁴ - u²v² + v⁴)`, written without subtraction: `v ((v²-u²)² + u²v²)`. -/
def g0 (u v : ℕ) : ℕ := v * ((v ^ 2 - u ^ 2) ^ 2 + u ^ 2 * v ^ 2)

theorem lacz_family_b (u v K b xx yy : ℕ) (hu : 0 < u) (huv : u < v) (hv2 : v < 2 * u) (hK : 0 < K)
    (hxx : 0 < xx) (hyy : 0 < yy) (hb : b + u ^ 2 = v ^ 2)
    (hV : K * (b ^ 3 * v ^ 2) = K * u ^ 8 + (u * v * xx + b * yy)) :
    TileCount (b * (K * (v * (b ^ 2 + u ^ 2 * v ^ 2))) ^ 2) := by
  have hu2 : u ^ 2 < v ^ 2 := Nat.pow_lt_pow_left huv (by norm_num)
  have hbpos : 0 < b := by omega
  have hv : 0 < v := by omega
  have hbR : (b : ℝ) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    have : ((b + u ^ 2 : ℕ) : ℝ) = ((v ^ 2 : ℕ) : ℝ) := by rw [hb]
    push_cast at this; linarith
  have hx : (0 : ℝ) < u := by exact_mod_cast hu
  have hy : (0 : ℝ) < v := by exact_mod_cast hv
  have hz : (0 : ℝ) < K := by exact_mod_cast hK
  have hxy : (u : ℝ) < v := by exact_mod_cast huv
  have hy2 : (v : ℝ) < 2 * u := by exact_mod_cast hv2
  have hbq : bq (u : ℝ) v = b := by unfold bq; rw [hbR]
  have hVp : 0 < Vp (u : ℝ) v := by
    have h1 : ((K * (b ^ 3 * v ^ 2) : ℕ) : ℝ) = ((K * u ^ 8 + (u * v * xx + b * yy) : ℕ) : ℝ) := by rw [hV]
    push_cast at h1
    have hxxR : (0 : ℝ) < xx := by exact_mod_cast hxx
    have hyyR : (0 : ℝ) < yy := by exact_mod_cast hyy
    have hbR' : (0 : ℝ) < b := by exact_mod_cast hbpos
    have e : Vp (u : ℝ) v = (b : ℝ) ^ 3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 8 := by
      unfold Vp; rw [hbq]
    rw [e]
    have hpos : 0 < (K : ℝ) * ((b : ℝ) ^ 3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 8) := by
      have : 0 < (u : ℝ) * v * xx + b * yy := by positivity
      nlinarith
    exact (mul_pos_iff_of_pos_left hz).1 hpos
  have h := LP.mk' (z := (K : ℝ)) hx hy hz hxy hy2 hVp
  -- the scales
  obtain ⟨kA, hkA⟩ : ∃ kA, K * u ^ 4 * b = kA + 1 := ⟨K * u ^ 4 * b - 1, by
    have : 0 < K * u ^ 4 * b := by positivity
    omega⟩
  obtain ⟨kB, hkB⟩ : ∃ kB, K * u ^ 5 * v = kB + 1 := ⟨K * u ^ 5 * v - 1, by
    have : 0 < K * u ^ 5 * v := by positivity
    omega⟩
  obtain ⟨lA, hlA⟩ : ∃ lA, yy = lA + 1 := ⟨yy - 1, by omega⟩
  obtain ⟨lB, hlB⟩ : ∃ lB, xx = lB + 1 := ⟨xx - 1, by omega⟩
  have eA : (kA : ℝ) + 1 = (K : ℝ) * (u : ℝ) ^ 4 * bq (u : ℝ) v := by
    rw [hbq]; exact_mod_cast hkA.symm
  have eB : (kB : ℝ) + 1 = (K : ℝ) * (u : ℝ) ^ 5 * v := by exact_mod_cast hkB.symm
  have eR : bq (u : ℝ) v * ((lA : ℝ) + 1) + (u : ℝ) * v * ((lB : ℝ) + 1) = (K : ℝ) * Vp (u : ℝ) v := by
    have h1 : ((K * (b ^ 3 * v ^ 2) : ℕ) : ℝ) = ((K * u ^ 8 + (u * v * xx + b * yy) : ℕ) : ℝ) := by rw [hV]
    push_cast at h1
    have hyyR : (yy : ℝ) = (lA : ℝ) + 1 := by exact_mod_cast hlA
    have hxxR : (xx : ℝ) = (lB : ℝ) + 1 := by exact_mod_cast hlB
    have e : Vp (u : ℝ) v = (b : ℝ) ^ 3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 8 := by
      unfold Vp; rw [hbq]
    rw [e, hbq, ← hyyR, ← hxxR]
    linarith
  have hbpos' : 0 < bq (u : ℝ) v := by rw [hbq]; exact_mod_cast hbpos
  obtain ⟨D, -, -⟩ := laczReal h (K * u ^ 3 * v * b) (K * u ^ 4 * b) (K * u * v * b ^ 2) (K * u ^ 2 * v ^ 2 * b)
    (K * u ^ 6) (K * v ^ 2 * b ^ 2) (K * u ^ 5 * v) kA lA kB lB
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by rw [hbq]; push_cast; ring) (by rw [hbq]; push_cast; ring) (by rw [hbq]; push_cast; ring)
    (by rw [hbq]; push_cast; ring) (by push_cast; ring) (by rw [hbq]; push_cast; ring) (by push_cast; ring)
    eA eB eR
  refine ⟨?_⟩
  have hN : K * u ^ 3 * v * b * (K * u ^ 3 * v * b) + K * u ^ 4 * b * (K * u ^ 4 * b) + K * u * v * b ^ 2 * (K * u * v * b ^ 2)
      + K * u ^ 2 * v ^ 2 * b * (K * u ^ 2 * v ^ 2 * b) + K * u ^ 6 * (K * u ^ 6) + K * v ^ 2 * b ^ 2 * (K * v ^ 2 * b ^ 2)
      + K * u ^ 5 * v * (K * u ^ 5 * v) + 2 * (kA + 1) * (lA + 1) + 2 * (kB + 1) * (lB + 1)
      = b * (K * (v * (b ^ 2 + u ^ 2 * v ^ 2))) ^ 2 := by
    have := count_alg (u : ℝ) v K kA lA kB lB eA eB eR
    rw [hbq] at this
    have h2 : (q1 (u : ℝ) v) = (b : ℝ) ^ 2 + (u : ℝ) ^ 2 * (v : ℝ) ^ 2 := by
      unfold q1; rw [hbR]; ring
    rw [h2] at this
    apply Nat.cast_injective (R := ℝ)
    push_cast
    linear_combination this
  rw [hN] at D
  exact D


/-- **Laczkovich's family, representable form.**  If `u < v < 2u` and `K (b³v² - u⁸) = uv·x + b·y` with `b = v²-u²`
and `x, y ≥ 1` (the parallelogram `U × V` is a union of `b × c` and `c × b` bricks), the isosceles triangle with base
angles `α` is tiled by `b (K g₀)²` copies of the tile `(u², v²-u², uv)`, `g₀ = v (u⁴ - u²v² + v⁴)`. -/
theorem lacz_family (u v K xx yy : ℕ) (hu : 0 < u) (huv : u < v) (hv2 : v < 2 * u) (hK : 0 < K)
    (hxx : 0 < xx) (hyy : 0 < yy)
    (hV : K * ((v ^ 2 - u ^ 2) ^ 3 * v ^ 2) = K * u ^ 8 + (u * v * xx + (v ^ 2 - u ^ 2) * yy)) :
    TileCount ((v ^ 2 - u ^ 2) * (K * g0 u v) ^ 2) := by
  have hu2 : u ^ 2 ≤ v ^ 2 := (Nat.pow_lt_pow_left huv (by norm_num)).le
  exact lacz_family_b u v K (v ^ 2 - u ^ 2) xx yy hu huv hv2 hK hxx hyy (Nat.sub_add_cancel hu2) hV

/-- **Unconditional form** (`K = 2 b u v`): whenever `(v²-u²)³ v² > u⁸`,
`b (2 b u v g₀)²` is a tile count. -/
theorem lacz_family_uncond (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv2 : v < 2 * u)
    (hV : u ^ 8 < (v ^ 2 - u ^ 2) ^ 3 * v ^ 2) :
    TileCount ((v ^ 2 - u ^ 2) * (2 * (v ^ 2 - u ^ 2) * u * v * g0 u v) ^ 2) := by
  have hu2 : u ^ 2 < v ^ 2 := Nat.pow_lt_pow_left huv (by norm_num)
  obtain ⟨b, hb⟩ : ∃ b, b = v ^ 2 - u ^ 2 := ⟨_, rfl⟩
  obtain ⟨Vn, hVn, hVn0⟩ : ∃ Vn, b ^ 3 * v ^ 2 = u ^ 8 + Vn ∧ 0 < Vn :=
    ⟨b ^ 3 * v ^ 2 - u ^ 8, by rw [hb]; omega, by rw [hb]; omega⟩
  have hbpos : 0 < b := by omega
  have hv : 0 < v := by omega
  rw [← hb]
  have := lacz_family u v (2 * b * u * v) (b * Vn) (u * v * Vn) hu huv hv2 (by positivity) (by positivity)
    (by positivity) (by rw [← hb, hVn]; ring)
  rw [← hb] at this
  convert this using 2

/-- the scaling: every multiple. -/
theorem lacz_family_scale (u v K xx yy m : ℕ) (hu : 0 < u) (huv : u < v) (hv2 : v < 2 * u) (hK : 0 < K)
    (hxx : 0 < xx) (hyy : 0 < yy)
    (hV : K * ((v ^ 2 - u ^ 2) ^ 3 * v ^ 2) = K * u ^ 8 + (u * v * xx + (v ^ 2 - u ^ 2) * yy)) (hm : 0 < m) :
    TileCount ((v ^ 2 - u ^ 2) * (m * K * g0 u v) ^ 2) := by
  have := tileCount_scale (lacz_family u v K xx yy hu huv hv2 hK hxx hyy hV) hm
  convert this using 1
  ring

/-! ### instances -/
/-- control: `(u,v) = (2,3)`, the tile `(4,5,6)`, `N = 5 · 183² = 167445` (a known tile count, `tab` of the paper). -/
theorem tileCount_167445_laczkovich : TileCount 167445 := by
  have := lacz_family 2 3 1 4 169 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [g0] at this
  exact this

/-- **new**: `(u,v) = (3,5)`, the tile `(9,16,15)`, `N = 16 · 2405² = 92,544,400`. -/
theorem tileCount_92544400 : TileCount 92544400 := by
  have := lacz_family 3 5 1 1 5989 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [g0] at this
  exact this

/-- `(u,v) = (4,7)`, tile `(16,33,28)`, `N = 33 · 13111²`. -/
theorem tileCount_4_7 : TileCount (33 * 13111 ^ 2) := by
  have := lacz_family 4 7 1 26 51353 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [g0] at this
  exact this

/-- `(u,v) = (5,7)`, tile `(25,24,35)`, `N = 24 · 12607²`. -/
theorem tileCount_5_7 : TileCount (24 * 12607 ^ 2) := by
  have := lacz_family 5 7 1 13 11929 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [g0] at this
  exact this

end Erdos634.Draft.LaczFamily

#print axioms Erdos634.Draft.LaczFamily.laczReal
#print axioms Erdos634.Draft.LaczFamily.lacz_family
#print axioms Erdos634.Draft.LaczFamily.lacz_family_uncond
#print axioms Erdos634.Draft.LaczFamily.tileCount_92544400
