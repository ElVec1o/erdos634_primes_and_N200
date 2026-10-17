/-
Draft/HerdtTile.lean — the tilings of the eleven pieces of the Herdt macro-dissection: seven triangles by `lad`
(scaled copies of the tile `Mod`), two parallelograms by the brick grids `GA`/`GB0`, and two by the reflected grids
(`reflTiling`).  Generated (private/ROOM/DISCOVERY/l6).  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.HerdtSub

open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast)

namespace Erdos634.Draft.HerdtFamily
open Erdos634.Draft.LaczFamily Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.BrickGridF (shift_rect)


noncomputable def R_red {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k : ℕ) (hk0 : 0 < k)
    (hk : (k : ℝ) = x * y * Df x y mh yh qh lh) :
    RTiling (Phi (fr x y) '' ((Sred x y mh yh qh lh))) (Mod h.lp) (k * k) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hdet : cross (P1 x y mh yh qh lh) (P0 x y mh yh qh lh) (P2 x y mh yh qh lh) ≠ 0 := by
    obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
    have hpos : 0 < (1 : ℝ) * cross (P1 x y mh yh qh lh) (P0 x y mh yh qh lh) (P2 x y mh yh qh lh) :=
      pos_of_eq (G := y^3*x^11*(y - x)*(x + y)*mh^2 + 2*y^3*x^11*(y - x)*(x + y)*mh*yh + 2*y^4*x^7*(y - x)^3*(x + y)^3*mh*qh + 2*y^4*x^7*(y - x)^3*(x + y)^3*mh*lh + y^3*x^11*(y - x)*(x + y)*yh^2 + 2*y^4*x^7*(y - x)^3*(x + y)^3*yh*qh + 2*y^4*x^7*(y - x)^3*(x + y)^3*yh*lh + x^3*y^5*(y - x)^5*(x + y)^5*qh^2 + 2*x^3*y^5*(y - x)^5*(x + y)^5*qh*lh + x^3*y^5*(y - x)^5*(x + y)^5*lh^2) (by hug2; ring) (by positivity)
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have R0 := lad h.lp (P1 x y mh yh qh lh) (P0 x y mh yh qh lh) (P2 x y mh yh qh lh) k hk0 hdet
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
  exact RTiling.cast (by rw [Set.insert_comm]) R0

noncomputable def R_ora {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k : ℕ) (hk0 : 0 < k)
    (hk : (k : ℝ) = x ^ 2 * Df x y mh yh qh lh) :
    RTiling (Phi (fr x y) '' ((Sora x y mh yh qh lh))) (Mod h.lp) (k * k) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hdet : cross (P2 x y mh yh qh lh) (P1 x y mh yh qh lh) (P3 x y mh yh qh lh) ≠ 0 := by
    obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
    have hpos : 0 < (-1 : ℝ) * cross (P2 x y mh yh qh lh) (P1 x y mh yh qh lh) (P3 x y mh yh qh lh) :=
      pos_of_eq (G := y*x^13*(y - x)*(x + y)*mh^2 + 2*y*x^13*(y - x)*(x + y)*mh*yh + 2*y^2*x^9*(y - x)^3*(x + y)^3*mh*qh + 2*y^2*x^9*(y - x)^3*(x + y)^3*mh*lh + y*x^13*(y - x)*(x + y)*yh^2 + 2*y^2*x^9*(y - x)^3*(x + y)^3*yh*qh + 2*y^2*x^9*(y - x)^3*(x + y)^3*yh*lh + y^3*x^5*(y - x)^5*(x + y)^5*qh^2 + 2*y^3*x^5*(y - x)^5*(x + y)^5*qh*lh + y^3*x^5*(y - x)^5*(x + y)^5*lh^2) (by hug2; ring) (by positivity)
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have R0 := lad h.lp (P2 x y mh yh qh lh) (P1 x y mh yh qh lh) (P3 x y mh yh qh lh) k hk0 hdet
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
  exact RTiling.cast (by rw [Set.insert_comm]) R0

noncomputable def R_lgr {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k : ℕ) (hk0 : 0 < k)
    (hk : (k : ℝ) = bq x y * Df x y mh yh qh lh) :
    RTiling (Phi (fr x y) '' ((Slgr x y mh yh qh lh))) (Mod h.lp) (k * k) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hdet : cross (P3 x y mh yh qh lh) (P4 x y mh yh qh lh) (P1 x y mh yh qh lh) ≠ 0 := by
    obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
    have hpos : 0 < (1 : ℝ) * cross (P3 x y mh yh qh lh) (P4 x y mh yh qh lh) (P1 x y mh yh qh lh) :=
      pos_of_eq (G := y*x^9*(y - x)^3*(x + y)^3*mh^2 + 2*y*x^9*(y - x)^3*(x + y)^3*mh*yh + 2*y^2*x^5*(y - x)^5*(x + y)^5*mh*qh + 2*y^2*x^5*(y - x)^5*(x + y)^5*mh*lh + y*x^9*(y - x)^3*(x + y)^3*yh^2 + 2*y^2*x^5*(y - x)^5*(x + y)^5*yh*qh + 2*y^2*x^5*(y - x)^5*(x + y)^5*yh*lh + x*y^3*(y - x)^7*(x + y)^7*qh^2 + 2*x*y^3*(y - x)^7*(x + y)^7*qh*lh + x*y^3*(y - x)^7*(x + y)^7*lh^2) (by hug2; ring) (by positivity)
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have R0 := lad h.lp (P3 x y mh yh qh lh) (P4 x y mh yh qh lh) (P1 x y mh yh qh lh) k hk0 hdet
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
  exact RTiling.cast (by rw [Set.insert_comm]) R0

noncomputable def R_gre {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k : ℕ) (hk0 : 0 < k)
    (hk : (k : ℝ) = tauf x y mh yh qh lh * x * bq x y) :
    RTiling (Phi (fr x y) '' ((Sgre x y mh yh qh lh))) (Mod h.lp) (k * k) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hdet : cross (P6 x y mh yh qh lh) (P5 x y mh yh qh lh) (P7 x y mh yh qh lh) ≠ 0 := by
    obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
    have hpos : 0 < (-1 : ℝ) * cross (P6 x y mh yh qh lh) (P5 x y mh yh qh lh) (P7 x y mh yh qh lh) :=
      pos_of_eq (G := x^3*y^3*(y - x)^5*(x + y)^5*mh^2 + 2*x^3*y^3*(y - x)^5*(x + y)^5*mh*yh + 2*y^2*x^7*(y - x)^4*(x + y)^4*mh*qh + 2*y^2*x^7*(y - x)^4*(x + y)^4*mh*lh + x^3*y^3*(y - x)^5*(x + y)^5*yh^2 + 2*y^2*x^7*(y - x)^4*(x + y)^4*yh*qh + 2*y^2*x^7*(y - x)^4*(x + y)^4*yh*lh + y*x^11*(y - x)^3*(x + y)^3*qh^2 + 2*y*x^11*(y - x)^3*(x + y)^3*qh*lh + y*x^11*(y - x)^3*(x + y)^3*lh^2) (by hug2; ring) (by positivity)
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have R0 := lad h.lp (P6 x y mh yh qh lh) (P5 x y mh yh qh lh) (P7 x y mh yh qh lh) k hk0 hdet
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
  exact RTiling.cast (by rw [Set.insert_comm]) R0

noncomputable def R_cya {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k : ℕ) (hk0 : 0 < k)
    (hk : (k : ℝ) = tauf x y mh yh qh lh * x ^ 3) :
    RTiling (Phi (fr x y) '' ((Scya x y mh yh qh lh))) (Mod h.lp) (k * k) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hdet : cross (P3 x y mh yh qh lh) (P7 x y mh yh qh lh) (P6 x y mh yh qh lh) ≠ 0 := by
    obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
    have hpos : 0 < (1 : ℝ) * cross (P3 x y mh yh qh lh) (P7 x y mh yh qh lh) (P6 x y mh yh qh lh) :=
      pos_of_eq (G := y^3*x^7*(y - x)^3*(x + y)^3*mh^2 + 2*y^3*x^7*(y - x)^3*(x + y)^3*mh*yh + 2*y^2*x^11*(y - x)^2*(x + y)^2*mh*qh + 2*y^2*x^11*(y - x)^2*(x + y)^2*mh*lh + y^3*x^7*(y - x)^3*(x + y)^3*yh^2 + 2*y^2*x^11*(y - x)^2*(x + y)^2*yh*qh + 2*y^2*x^11*(y - x)^2*(x + y)^2*yh*lh + y*x^15*(y - x)*(x + y)*qh^2 + 2*y*x^15*(y - x)*(x + y)*qh*lh + y*x^15*(y - x)*(x + y)*lh^2) (by hug2; ring) (by positivity)
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have R0 := lad h.lp (P3 x y mh yh qh lh) (P7 x y mh yh qh lh) (P6 x y mh yh qh lh) k hk0 hdet
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
  exact RTiling.cast (by rw [Set.insert_comm]) R0

noncomputable def R_lbg {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k : ℕ) (hk0 : 0 < k)
    (hk : (k : ℝ) = tauf x y mh yh qh lh * x ^ 2 * y) :
    RTiling (Phi (fr x y) '' ((Slbg x y mh yh qh lh))) (Mod h.lp) (k * k) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hdet : cross (P7 x y mh yh qh lh) (P8 x y mh yh qh lh) (P3 x y mh yh qh lh) ≠ 0 := by
    obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
    have hpos : 0 < (-1 : ℝ) * cross (P7 x y mh yh qh lh) (P8 x y mh yh qh lh) (P3 x y mh yh qh lh) :=
      pos_of_eq (G := x^5*y^5*(y - x)^3*(x + y)^3*mh^2 + 2*x^5*y^5*(y - x)^3*(x + y)^3*mh*yh + 2*y^4*x^9*(y - x)^2*(x + y)^2*mh*qh + 2*y^4*x^9*(y - x)^2*(x + y)^2*mh*lh + x^5*y^5*(y - x)^3*(x + y)^3*yh^2 + 2*y^4*x^9*(y - x)^2*(x + y)^2*yh*qh + 2*y^4*x^9*(y - x)^2*(x + y)^2*yh*lh + y^3*x^13*(y - x)*(x + y)*qh^2 + 2*y^3*x^13*(y - x)*(x + y)*qh*lh + y^3*x^13*(y - x)*(x + y)*lh^2) (by hug2; ring) (by positivity)
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have R0 := lad h.lp (P7 x y mh yh qh lh) (P8 x y mh yh qh lh) (P3 x y mh yh qh lh) k hk0 hdet
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
  exact RTiling.cast (by rw [Set.insert_comm]) R0

noncomputable def R_pbg {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k : ℕ) (hk0 : 0 < k)
    (hk : (k : ℝ) = tauf x y mh yh qh lh * y * bq x y) :
    RTiling (Phi (fr x y) '' ((Spbg x y mh yh qh lh))) (Mod h.lp) (k * k) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hdet : cross (P8 x y mh yh qh lh) (P9 x y mh yh qh lh) (P3 x y mh yh qh lh) ≠ 0 := by
    obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
    have hpos : 0 < (-1 : ℝ) * cross (P8 x y mh yh qh lh) (P9 x y mh yh qh lh) (P3 x y mh yh qh lh) :=
      pos_of_eq (G := x*y^5*(y - x)^5*(x + y)^5*mh^2 + 2*x*y^5*(y - x)^5*(x + y)^5*mh*yh + 2*y^4*x^5*(y - x)^4*(x + y)^4*mh*qh + 2*y^4*x^5*(y - x)^4*(x + y)^4*mh*lh + x*y^5*(y - x)^5*(x + y)^5*yh^2 + 2*y^4*x^5*(y - x)^4*(x + y)^4*yh*qh + 2*y^4*x^5*(y - x)^4*(x + y)^4*yh*lh + y^3*x^9*(y - x)^3*(x + y)^3*qh^2 + 2*y^3*x^9*(y - x)^3*(x + y)^3*qh*lh + y^3*x^9*(y - x)^3*(x + y)^3*lh^2) (by hug2; ring) (by positivity)
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have R0 := lad h.lp (P8 x y mh yh qh lh) (P9 x y mh yh qh lh) (P3 x y mh yh qh lh) k hk0 hdet
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
    (by rw [hk]; simp only [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, fr, bq, Df, tauf, Vp]; field_simp; ring)
  exact RTiling.cast (by rw [Set.insert_comm]) R0

theorem neg_one_div_fr {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : -1 / fr x y = y / x := by
  unfold fr; field_simp

noncomputable def R_yel {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k l : ℕ)
    (hk : x * y * ((k : ℝ) + 1) = Vp x y * yh) (hl : bq x y * ((l : ℝ) + 1) = x * y * bq x y * Df x y mh yh qh lh) :
    RTiling (Phi (fr x y) '' ((Syel x y mh yh qh lh))) (Mod h.lp) (2 * (k + 1) * (l + 1)) :=
  shift_rect (GA h.lp k l) ((yelA x y mh yh qh lh)) ((yelC x y mh yh qh lh)) ((yelB x y mh yh qh lh)) ((yelD x y mh yh qh lh))
    (by rw [hk]; simp only [yelA, yelB, Vp, bq]; ring) (by rw [hl]; simp only [yelC, yelD, Df, bq]; ring)

noncomputable def R_mar {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k l : ℕ)
    (hk : bq x y * ((k : ℝ) + 1) = Vp x y * mh) (hl : x * y * ((l : ℝ) + 1) = x * y * bq x y * Df x y mh yh qh lh) :
    RTiling (Phi (fr x y) '' ((Smar x y mh yh qh lh))) (Mod h.lp) (2 * (k + 1) * (l + 1)) :=
  shift_rect (GB0 h.lp k l) ((marA x y mh yh qh lh)) ((marC x y mh yh qh lh)) ((marB x y mh yh qh lh)) ((marD x y mh yh qh lh))
    (by rw [hk]; simp only [marA, marB, Vp, bq]; ring) (by rw [hl]; simp only [marC, marD, Df, bq]; ring)

noncomputable def R_llw {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k l : ℕ)
    (hk : bq x y * ((k : ℝ) + 1) = x ^ 2 * y * bq x y * tauf x y mh yh qh lh)
    (hl : x * y * ((l : ℝ) + 1) = x * Vp x y * lh) :
    RTiling (Phi (fr x y) '' ((Sllw x y mh yh qh lh))) (Mod h.lp) (2 * (k + 1) * (l + 1)) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hf0 : fr x y ≠ 0 := by unfold fr; exact div_ne_zero (neg_ne_zero.mpr hx0) hy0
  have R0 := shift_rect (GB0 h.lp k l) ((llwA x y mh yh qh lh)) ((llwC x y mh yh qh lh)) ((llwB x y mh yh qh lh)) ((llwD x y mh yh qh lh))
    (by rw [hk]; simp only [llwA, llwB, Vp, bq, tauf]; ring) (by rw [hl]; simp only [llwC, llwD, Vp, bq]; ring)
  exact RTiling.cast (by rw [neg_one_div_fr hx0 hy0]) (reflTiling hf0 R0)

noncomputable def R_plw {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) (k l : ℕ)
    (hk : x * y * ((k : ℝ) + 1) = x ^ 2 * y * bq x y * tauf x y mh yh qh lh)
    (hl : bq x y * ((l : ℝ) + 1) = x * Vp x y * qh) :
    RTiling (Phi (fr x y) '' ((Splw x y mh yh qh lh))) (Mod h.lp) (2 * (k + 1) * (l + 1)) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  have hy0 : y ≠ 0 := h.lp.hy.ne'
  have hf0 : fr x y ≠ 0 := by unfold fr; exact div_ne_zero (neg_ne_zero.mpr hx0) hy0
  have R0 := shift_rect (GA h.lp k l) ((plwA x y mh yh qh lh)) ((plwC x y mh yh qh lh)) ((plwB x y mh yh qh lh)) ((plwD x y mh yh qh lh))
    (by rw [hk]; simp only [plwA, plwB, Vp, bq, tauf]; ring) (by rw [hl]; simp only [plwC, plwD, Vp, bq]; ring)
  exact RTiling.cast (by rw [neg_one_div_fr hx0 hy0]) (reflTiling hf0 R0)


end Erdos634.Draft.HerdtFamily
