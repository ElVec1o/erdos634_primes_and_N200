/-
Draft/HerdtReal.lean — assembly of the Herdt 11-piece macro-dissection: for real `(x, y) = (u, v)` with `LP x y 1`
(`u < v < 2u`, `(v²-u²)³v² > u⁸`) and positive reals `mh yh qh lh`, the isosceles triangle `tgt` with base angles `α`
(tile `(u², v²-u², uv)`, `γ = 2α`) is tiled by `b g²` copies of the tile, `g = v (D + τ v)`, `b = v²-u²`, whenever the seven
triangle scales and the four brick grids have integral side counts (`herdtReal`).  Generated (private/ROOM/DISCOVERY/l6);
the template is Herdt's 1125-tiling (Beeson, Tilings of an isosceles triangle, Fig. 23).  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.HerdtTile
import Erdos634.Draft.LaczFamily
import Erdos634.Draft.HerdtSep1
import Erdos634.Draft.HerdtSep2
import Erdos634.Draft.HerdtSep3
import Erdos634.Draft.HerdtSep4

open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast)

namespace Erdos634.Draft.HerdtFamily
open Erdos634.Draft.LaczFamily Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.S2L (pack_exists)

theorem det_T {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) :
    Erdos634.Draft.LaczFamily.cross ((0 : ℝ), (0 : ℝ)) (TCx x y mh yh qh lh, (0 : ℝ)) ((0 : ℝ), -TBy x y mh yh qh lh) ≠ 0 := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  have e : Erdos634.Draft.LaczFamily.cross ((0 : ℝ), (0 : ℝ)) (TCx x y mh yh qh lh, (0 : ℝ)) ((0 : ℝ), -TBy x y mh yh qh lh)
      = -(TCx x y mh yh qh lh * TBy x y mh yh qh lh) := by unfold Erdos634.Draft.LaczFamily.cross; ring
  rw [e]
  exact neg_ne_zero.mpr (mul_pos hC hB).ne'

/-- the target triangle. -/
noncomputable def tgt {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : Tri :=
  triC (fr x y) (hfr h.lp) ((0 : ℝ), (0 : ℝ)) (TCx x y mh yh qh lh, (0 : ℝ)) ((0 : ℝ), -TBy x y mh yh qh lh)
    (fun hh => det_T h (by unfold Erdos634.Draft.LaczFamily.cross; linarith))

theorem tgt_carrier {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) :
    (tgt h).carrier = Phi (fr x y) '' (Tset x y mh yh qh lh) :=
  carrier_triC _ _ _ _ _ _

open MeasureTheory in
theorem volTgt {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) :
    volume (tgt h).carrier = ENNReal.ofReal (|sD (fr x y) / (2 * fr x y)| * (TCx x y mh yh qh lh * TBy x y mh yh qh lh))
      * volume Erdos634.AreaDet.stdCarrier := by
  have hg := gg_pos h
  have hxx := h.lp.hx
  have hyy := h.lp.hy
  have hbb := h.lp.hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  unfold tgt
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hX : 0 < TCx x y mh yh qh lh * TBy x y mh yh qh lh := mul_pos hC hB
  rw [← abs_of_pos hX, ← abs_neg]
  congr 1
  simp only
  ring

open MeasureTheory in
theorem hvol_all {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (N : ℕ)
    (hN : (N : ℝ) = (gg x y mh yh qh lh) ^ 2 * bq x y) :
    (N : ENNReal) * volume (Mod h.lp).carrier = volume (tgt h).carrier := by
  have hg := gg_pos h
  have hxx := h.lp.hx
  have hyy := h.lp.hy
  rw [volMod h.lp, volTgt h, ← mul_assoc, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 2
  rw [hN]
  unfold TCx TBy bq
  ring

theorem dTR {f : ℝ} (hf : 1 < 4 * f ^ 2) {A R R' : Set (ℝ × ℝ)} (hd : Disjoint (interior A) (interior R'))
    (hsub : R ⊆ R') : Disjoint (interior (Phi f '' A)) (interior (Phi f '' R)) :=
  (disjoint_image' hf hd).mono_right (interior_mono (Set.image_mono hsub))



/-- the eleven regions. -/
noncomputable def Sset {x y mh yh qh lh : ℝ} (_h : HP x y mh yh qh lh) : Fin 11 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (fr x y) '' ((Sred x y mh yh qh lh))
  | ⟨1, _⟩ => Phi (fr x y) '' ((Sora x y mh yh qh lh))
  | ⟨2, _⟩ => Phi (fr x y) '' ((Slgr x y mh yh qh lh))
  | ⟨3, _⟩ => Phi (fr x y) '' ((Sgre x y mh yh qh lh))
  | ⟨4, _⟩ => Phi (fr x y) '' ((Scya x y mh yh qh lh))
  | ⟨5, _⟩ => Phi (fr x y) '' ((Slbg x y mh yh qh lh))
  | ⟨6, _⟩ => Phi (fr x y) '' ((Spbg x y mh yh qh lh))
  | ⟨7, _⟩ => Phi (fr x y) '' ((Syel x y mh yh qh lh))
  | ⟨8, _⟩ => Phi (fr x y) '' ((Smar x y mh yh qh lh))
  | ⟨9, _⟩ => Phi (fr x y) '' ((Sllw x y mh yh qh lh))
  | ⟨10, _⟩ => Phi (fr x y) '' ((Splw x y mh yh qh lh))
  | ⟨k + 11, hk⟩ => absurd hk (by omega)

def cntS (kr ko kl kg kc kb kp k1 l1 k2 l2 k3 l3 k4 l4 : ℕ) : Fin 11 → ℕ := fun i => match i with
  | ⟨0, _⟩ => kr * kr
  | ⟨1, _⟩ => ko * ko
  | ⟨2, _⟩ => kl * kl
  | ⟨3, _⟩ => kg * kg
  | ⟨4, _⟩ => kc * kc
  | ⟨5, _⟩ => kb * kb
  | ⟨6, _⟩ => kp * kp
  | ⟨7, _⟩ => 2 * (k1 + 1) * (l1 + 1)
  | ⟨8, _⟩ => 2 * (k2 + 1) * (l2 + 1)
  | ⟨9, _⟩ => 2 * (k3 + 1) * (l3 + 1)
  | ⟨10, _⟩ => 2 * (k4 + 1) * (l4 + 1)
  | ⟨k + 11, hk⟩ => absurd hk (by omega)


theorem hS_all {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ∀ a b : Fin 11, a ≠ b →
    Disjoint (interior (Sset h a)) (interior (Sset h b)) := by
  have hf := hfr h.lp
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => disjoint_image' hf (dsep_red_orange h)
  | ⟨0, _⟩, ⟨2, _⟩ => disjoint_image' hf (dsep_red_lgreen h)
  | ⟨0, _⟩, ⟨3, _⟩ => disjoint_image' hf (dsep_red_green h)
  | ⟨0, _⟩, ⟨4, _⟩ => disjoint_image' hf (dsep_red_cyan h)
  | ⟨0, _⟩, ⟨5, _⟩ => disjoint_image' hf (dsep_red_lav_big h)
  | ⟨0, _⟩, ⟨6, _⟩ => disjoint_image' hf (dsep_red_pink_big h)
  | ⟨0, _⟩, ⟨7, _⟩ => disjoint_image' hf (dsep_red_yellow h)
  | ⟨0, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_red_maroon h)
  | ⟨0, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_red_lav_low h)
  | ⟨0, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_red_pink_low h)
  | ⟨1, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_orange h)).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => disjoint_image' hf (dsep_orange_lgreen h)
  | ⟨1, _⟩, ⟨3, _⟩ => disjoint_image' hf (dsep_orange_green h)
  | ⟨1, _⟩, ⟨4, _⟩ => disjoint_image' hf (dsep_orange_cyan h)
  | ⟨1, _⟩, ⟨5, _⟩ => disjoint_image' hf (dsep_orange_lav_big h)
  | ⟨1, _⟩, ⟨6, _⟩ => disjoint_image' hf (dsep_orange_pink_big h)
  | ⟨1, _⟩, ⟨7, _⟩ => disjoint_image' hf (dsep_orange_yellow h)
  | ⟨1, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_orange_maroon h)
  | ⟨1, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_orange_lav_low h)
  | ⟨1, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_orange_pink_low h)
  | ⟨2, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_lgreen h)).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_lgreen h)).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => disjoint_image' hf (dsep_lgreen_green h)
  | ⟨2, _⟩, ⟨4, _⟩ => disjoint_image' hf (dsep_lgreen_cyan h)
  | ⟨2, _⟩, ⟨5, _⟩ => disjoint_image' hf (dsep_lgreen_lav_big h)
  | ⟨2, _⟩, ⟨6, _⟩ => disjoint_image' hf (dsep_lgreen_pink_big h)
  | ⟨2, _⟩, ⟨7, _⟩ => disjoint_image' hf (dsep_lgreen_yellow h)
  | ⟨2, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_lgreen_maroon h)
  | ⟨2, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_lgreen_lav_low h)
  | ⟨2, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_lgreen_pink_low h)
  | ⟨3, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_green h)).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_green h)).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_green h)).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => disjoint_image' hf (dsep_green_cyan h)
  | ⟨3, _⟩, ⟨5, _⟩ => disjoint_image' hf (dsep_green_lav_big h)
  | ⟨3, _⟩, ⟨6, _⟩ => disjoint_image' hf (dsep_green_pink_big h)
  | ⟨3, _⟩, ⟨7, _⟩ => disjoint_image' hf (dsep_green_yellow h)
  | ⟨3, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_green_maroon h)
  | ⟨3, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_green_lav_low h)
  | ⟨3, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_green_pink_low h)
  | ⟨4, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_cyan h)).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_cyan h)).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_cyan h)).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (disjoint_image' hf (dsep_green_cyan h)).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨4, _⟩, ⟨5, _⟩ => disjoint_image' hf (dsep_cyan_lav_big h)
  | ⟨4, _⟩, ⟨6, _⟩ => disjoint_image' hf (dsep_cyan_pink_big h)
  | ⟨4, _⟩, ⟨7, _⟩ => disjoint_image' hf (dsep_cyan_yellow h)
  | ⟨4, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_cyan_maroon h)
  | ⟨4, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_cyan_lav_low h)
  | ⟨4, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_cyan_pink_low h)
  | ⟨5, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_lav_big h)).symm
  | ⟨5, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_lav_big h)).symm
  | ⟨5, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_lav_big h)).symm
  | ⟨5, _⟩, ⟨3, _⟩ => (disjoint_image' hf (dsep_green_lav_big h)).symm
  | ⟨5, _⟩, ⟨4, _⟩ => (disjoint_image' hf (dsep_cyan_lav_big h)).symm
  | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hab
  | ⟨5, _⟩, ⟨6, _⟩ => disjoint_image' hf (dsep_lav_big_pink_big h)
  | ⟨5, _⟩, ⟨7, _⟩ => disjoint_image' hf (dsep_lav_big_yellow h)
  | ⟨5, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_lav_big_maroon h)
  | ⟨5, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_lav_big_lav_low h)
  | ⟨5, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_lav_big_pink_low h)
  | ⟨6, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_pink_big h)).symm
  | ⟨6, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_pink_big h)).symm
  | ⟨6, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_pink_big h)).symm
  | ⟨6, _⟩, ⟨3, _⟩ => (disjoint_image' hf (dsep_green_pink_big h)).symm
  | ⟨6, _⟩, ⟨4, _⟩ => (disjoint_image' hf (dsep_cyan_pink_big h)).symm
  | ⟨6, _⟩, ⟨5, _⟩ => (disjoint_image' hf (dsep_lav_big_pink_big h)).symm
  | ⟨6, _⟩, ⟨6, _⟩ => absurd rfl hab
  | ⟨6, _⟩, ⟨7, _⟩ => disjoint_image' hf (dsep_pink_big_yellow h)
  | ⟨6, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_pink_big_maroon h)
  | ⟨6, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_pink_big_lav_low h)
  | ⟨6, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_pink_big_pink_low h)
  | ⟨7, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_yellow h)).symm
  | ⟨7, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_yellow h)).symm
  | ⟨7, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_yellow h)).symm
  | ⟨7, _⟩, ⟨3, _⟩ => (disjoint_image' hf (dsep_green_yellow h)).symm
  | ⟨7, _⟩, ⟨4, _⟩ => (disjoint_image' hf (dsep_cyan_yellow h)).symm
  | ⟨7, _⟩, ⟨5, _⟩ => (disjoint_image' hf (dsep_lav_big_yellow h)).symm
  | ⟨7, _⟩, ⟨6, _⟩ => (disjoint_image' hf (dsep_pink_big_yellow h)).symm
  | ⟨7, _⟩, ⟨7, _⟩ => absurd rfl hab
  | ⟨7, _⟩, ⟨8, _⟩ => disjoint_image' hf (dsep_yellow_maroon h)
  | ⟨7, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_yellow_lav_low h)
  | ⟨7, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_yellow_pink_low h)
  | ⟨8, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_maroon h)).symm
  | ⟨8, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_maroon h)).symm
  | ⟨8, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_maroon h)).symm
  | ⟨8, _⟩, ⟨3, _⟩ => (disjoint_image' hf (dsep_green_maroon h)).symm
  | ⟨8, _⟩, ⟨4, _⟩ => (disjoint_image' hf (dsep_cyan_maroon h)).symm
  | ⟨8, _⟩, ⟨5, _⟩ => (disjoint_image' hf (dsep_lav_big_maroon h)).symm
  | ⟨8, _⟩, ⟨6, _⟩ => (disjoint_image' hf (dsep_pink_big_maroon h)).symm
  | ⟨8, _⟩, ⟨7, _⟩ => (disjoint_image' hf (dsep_yellow_maroon h)).symm
  | ⟨8, _⟩, ⟨8, _⟩ => absurd rfl hab
  | ⟨8, _⟩, ⟨9, _⟩ => disjoint_image' hf (dsep_maroon_lav_low h)
  | ⟨8, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_maroon_pink_low h)
  | ⟨9, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_lav_low h)).symm
  | ⟨9, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_lav_low h)).symm
  | ⟨9, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_lav_low h)).symm
  | ⟨9, _⟩, ⟨3, _⟩ => (disjoint_image' hf (dsep_green_lav_low h)).symm
  | ⟨9, _⟩, ⟨4, _⟩ => (disjoint_image' hf (dsep_cyan_lav_low h)).symm
  | ⟨9, _⟩, ⟨5, _⟩ => (disjoint_image' hf (dsep_lav_big_lav_low h)).symm
  | ⟨9, _⟩, ⟨6, _⟩ => (disjoint_image' hf (dsep_pink_big_lav_low h)).symm
  | ⟨9, _⟩, ⟨7, _⟩ => (disjoint_image' hf (dsep_yellow_lav_low h)).symm
  | ⟨9, _⟩, ⟨8, _⟩ => (disjoint_image' hf (dsep_maroon_lav_low h)).symm
  | ⟨9, _⟩, ⟨9, _⟩ => absurd rfl hab
  | ⟨9, _⟩, ⟨10, _⟩ => disjoint_image' hf (dsep_lav_low_pink_low h)
  | ⟨10, _⟩, ⟨0, _⟩ => (disjoint_image' hf (dsep_red_pink_low h)).symm
  | ⟨10, _⟩, ⟨1, _⟩ => (disjoint_image' hf (dsep_orange_pink_low h)).symm
  | ⟨10, _⟩, ⟨2, _⟩ => (disjoint_image' hf (dsep_lgreen_pink_low h)).symm
  | ⟨10, _⟩, ⟨3, _⟩ => (disjoint_image' hf (dsep_green_pink_low h)).symm
  | ⟨10, _⟩, ⟨4, _⟩ => (disjoint_image' hf (dsep_cyan_pink_low h)).symm
  | ⟨10, _⟩, ⟨5, _⟩ => (disjoint_image' hf (dsep_lav_big_pink_low h)).symm
  | ⟨10, _⟩, ⟨6, _⟩ => (disjoint_image' hf (dsep_pink_big_pink_low h)).symm
  | ⟨10, _⟩, ⟨7, _⟩ => (disjoint_image' hf (dsep_yellow_pink_low h)).symm
  | ⟨10, _⟩, ⟨8, _⟩ => (disjoint_image' hf (dsep_maroon_pink_low h)).symm
  | ⟨10, _⟩, ⟨9, _⟩ => (disjoint_image' hf (dsep_lav_low_pink_low h)).symm
  | ⟨10, _⟩, ⟨10, _⟩ => absurd rfl hab
  | ⟨k + 11, hk⟩, _ => absurd hk (by omega)
  | _, ⟨k + 11, hk⟩ => absurd hk (by omega)


theorem hsub_all {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ∀ a : Fin 11, Sset h a ⊆ (tgt h).carrier := by
  rw [tgt_carrier]
  intro a
  exact match a with
  | ⟨0, _⟩ => Set.image_mono (subT_red h)
  | ⟨1, _⟩ => Set.image_mono (subT_orange h)
  | ⟨2, _⟩ => Set.image_mono (subT_lgreen h)
  | ⟨3, _⟩ => Set.image_mono (subT_green h)
  | ⟨4, _⟩ => Set.image_mono (subT_cyan h)
  | ⟨5, _⟩ => Set.image_mono (subT_lav_big h)
  | ⟨6, _⟩ => Set.image_mono (subT_pink_big h)
  | ⟨7, _⟩ => Set.image_mono (subT_yellow h)
  | ⟨8, _⟩ => Set.image_mono (subT_maroon h)
  | ⟨9, _⟩ => Set.image_mono (subT_lav_low h)
  | ⟨10, _⟩ => Set.image_mono (subT_pink_low h)
  | ⟨k + 11, hk⟩ => absurd hk (by omega)



end Erdos634.Draft.HerdtFamily
