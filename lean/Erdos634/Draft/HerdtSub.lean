/-
Draft/HerdtSub.lean — containment of the eleven pieces of the Herdt macro-dissection in the target triangle
`Tset = hull {(0,0), (Cx,0), (0,-By)}`, `Cx = g v b`, `By = g u b`, `g = v (D + τ v)` (`gg`), where
`D = Df = u⁴(mh+yh) + v b²(qh+lh)`, `τ = tauf = v b (mh+yh) + u⁴(qh+lh)`.  Generated (private/ROOM/DISCOVERY/l6).
UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.HerdtPts

open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect)

namespace Erdos634.Draft.HerdtFamily
open Erdos634.Draft.LaczFamily
open Erdos634.Draft.S2L (rect_subset)

def Df (x y mh yh qh lh : ℝ) : ℝ := x ^ 4 * (mh + yh) + y * (bq x y) ^ 2 * (qh + lh)
def tauf (x y mh yh qh lh : ℝ) : ℝ := y * bq x y * (mh + yh) + x ^ 4 * (qh + lh)
def gg (x y mh yh qh lh : ℝ) : ℝ := y * (Df x y mh yh qh lh + tauf x y mh yh qh lh * y)
def TCx (x y mh yh qh lh : ℝ) : ℝ := gg x y mh yh qh lh * y * bq x y
def TBy (x y mh yh qh lh : ℝ) : ℝ := gg x y mh yh qh lh * x * bq x y
abbrev Tset (x y mh yh qh lh : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (TCx x y mh yh qh lh, 0), (0, -TBy x y mh yh qh lh)} : Set (ℝ × ℝ))

macro "hug2" : tactic => `(tactic| simp only [Erdos634.Draft.LaczFamily.cross, P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, yelA, yelB, yelC, yelD, marA, marB, marC, marD, llwA, llwB, llwC, llwD, plwA, plwB, plwC, plwD, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, Df, tauf, gg, TCx, TBy, bq])

theorem gg_pos {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : 0 < gg x y mh yh qh lh := by
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  unfold gg Df tauf; positivity


theorem memT_P0 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P0 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*mh + (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P0 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P0 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x^3*(a03 x y)*mh + x^3*(a03 x y)*yh + x*y^3*(y - x)*(x + y)*(a04 x y)*qh + x*y^3*(y - x)*(x + y)*(a04 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P1 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P1 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (y - x)*(x + y)*(a06 x y)*mh + (y - x)*(x + y)*(a06 x y)*yh + x^2*y^3*(y - x)^2*(x + y)^2*qh + x^2*y^3*(y - x)^2*(x + y)^2*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P1 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P1 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x^3*(y - x)^2*(x + y)^2*(a01 x y)*mh + x^3*(y - x)^2*(x + y)^2*(a01 x y)*yh + x*y^3*(y - x)*(x + y)*(a05 x y)*qh + x*y^3*(y - x)*(x + y)*(a05 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P2 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P2 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*mh + (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P2 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P2 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x^3*(a06 x y)*mh + x^3*(a06 x y)*yh + y^3*x^5*(y - x)*(x + y)*qh + y^3*x^5*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P3 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P3 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := y^2*(y - x)^3*(x + y)^3*mh + y^2*(y - x)^3*(x + y)^3*yh + y*x^4*(y - x)^2*(x + y)^2*qh + y*x^4*(y - x)^2*(x + y)^2*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P3 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P3 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (y^2*x^3*(y - x)^2*(x + y)^2*mh + y^2*x^3*(y - x)^2*(x + y)^2*yh + y*x^7*(y - x)*(x + y)*qh + y*x^7*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P4 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P4 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := y^2*(y - x)*(x + y)*(a04 x y)*mh + y^2*(y - x)*(x + y)*(a04 x y)*yh + y*(y - x)^2*(x + y)^2*(a02 x y)*qh + y*(y - x)^2*(x + y)^2*(a02 x y)*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P4 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P4 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (y^2*x^3*(y - x)^2*(x + y)^2*mh + y^2*x^3*(y - x)^2*(x + y)^2*yh + y*x^7*(y - x)*(x + y)*qh + y*x^7*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P5 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P5 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := y^2*(y - x)*(x + y)*(a02 x y)*mh + y^2*(y - x)*(x + y)*(a02 x y)*yh + y*x^4*(a02 x y)*qh + y*x^4*(a02 x y)*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := x*(a18 x y)*qh + x*(a18 x y)*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P5 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P5 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (0)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P6 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P6 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := y^2*(y - x)*(x + y)*(a04 x y)*mh + y^2*(y - x)*(x + y)*(a04 x y)*yh + y*x^4*(a04 x y)*qh + y*x^4*(a04 x y)*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := x*(a18 x y)*qh + x*(a18 x y)*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P6 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P6 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (y^2*x^3*(y - x)^2*(x + y)^2*mh + y^2*x^3*(y - x)^2*(x + y)^2*yh + y*x^7*(y - x)*(x + y)*qh + y*x^7*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P7 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P7 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := x^2*y^4*(y - x)*(x + y)*mh + x^2*y^4*(y - x)*(x + y)*yh + y^3*x^6*qh + y^3*x^6*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := x*y*(y - x)^3*(x + y)^3*mh + x*y*(y - x)^3*(x + y)^3*yh + x*y^2*(a10 x y)*qh + x*y^2*(a10 x y)*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P7 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P7 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (0)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P8 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P8 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · exact (nonneg_of_eq (G := x*y*(y - x)*(x + y)*(a02 x y)*mh + x*y*(y - x)*(x + y)*(a02 x y)*yh + x*y^2*(y - x)*(x + y)*(a04 x y)*qh + x*y^2*(y - x)*(x + y)*(a04 x y)*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P8 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P8 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (0)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P9 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P9 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P9 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P9 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^4*(y - x)^2*(x + y)^2*mh + x*y^4*(y - x)^2*(x + y)^2*yh + y^3*x^5*(y - x)*(x + y)*qh + y^3*x^5*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P10 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P10 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P10 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P10 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^2*(y - x)*(x + y)*(a02 x y)*mh + x*y^2*(y - x)*(x + y)*(a02 x y)*yh + x*y^3*(y - x)*(x + y)*(a04 x y)*qh + x*y^3*(y - x)*(x + y)*(a04 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P11 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P11 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P11 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P11 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^2*(y - x)*(x + y)*(a02 x y)*mh + x^3*(a03 x y)*yh + x*y^3*(y - x)*(x + y)*(a04 x y)*qh + x*y^3*(y - x)*(x + y)*(a04 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P12 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P12 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P12 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P12 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^4*(y - x)^2*(x + y)^2*mh + x^3*(a06 x y)*yh + y^3*x^5*(y - x)*(x + y)*qh + y^3*x^5*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P13 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P13 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := y^2*(y - x)*(x + y)*(a02 x y)*mh + y^2*(y - x)*(x + y)*(a02 x y)*yh + y^3*(y - x)*(x + y)*(a04 x y)*qh + y^3*(y - x)*(x + y)*(a04 x y)*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P13 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P13 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (0)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P14 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P14 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := y^2*(y - x)*(x + y)*(a02 x y)*mh + y^2*(y - x)*(x + y)*(a02 x y)*yh + y^3*(y - x)*(x + y)*(a04 x y)*qh + y*x^4*(a02 x y)*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := x*(a18 x y)*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P14 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P14 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (0)) (by hug2; ring) (by positivity)
    linarith

theorem memT_P15 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (P15 x y mh yh qh lh) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := y^2*(y - x)*(x + y)*(a04 x y)*mh + y^2*(y - x)*(x + y)*(a04 x y)*yh + y*(y - x)^2*(x + y)^2*(a02 x y)*qh + y*x^4*(a04 x y)*lh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := x*(a18 x y)*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - (((P15 x y mh yh qh lh)).1 * TBy x y mh yh qh lh + (-((P15 x y mh yh qh lh)).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (y^2*x^3*(y - x)^2*(x + y)^2*mh + y^2*x^3*(y - x)^2*(x + y)^2*yh + y*x^7*(y - x)*(x + y)*qh + y*x^7*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_yel_00 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((yelA x y mh yh qh lh), (yelC x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((yelA x y mh yh qh lh), (yelC x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((yelA x y mh yh qh lh), (yelC x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^4*(y - x)^2*(x + y)^2*mh + x*y^4*(y - x)^2*(x + y)^2*yh + y^3*x^5*(y - x)*(x + y)*qh + y^3*x^5*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_yel_10 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((yelB x y mh yh qh lh), (yelC x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((yelB x y mh yh qh lh), (yelC x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((yelB x y mh yh qh lh), (yelC x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^4*(y - x)^2*(x + y)^2*mh + x^3*(a06 x y)*yh + y^3*x^5*(y - x)*(x + y)*qh + y^3*x^5*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_yel_01 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((yelA x y mh yh qh lh), (yelD x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((yelA x y mh yh qh lh), (yelD x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((yelA x y mh yh qh lh), (yelD x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^2*(y - x)*(x + y)*(a02 x y)*mh + x*y^2*(y - x)*(x + y)*(a02 x y)*yh + x*y^3*(y - x)*(x + y)*(a04 x y)*qh + x*y^3*(y - x)*(x + y)*(a04 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_yel_11 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((yelB x y mh yh qh lh), (yelD x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((yelB x y mh yh qh lh), (yelD x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((yelB x y mh yh qh lh), (yelD x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^2*(y - x)*(x + y)*(a02 x y)*mh + x^3*(a03 x y)*yh + x*y^3*(y - x)*(x + y)*(a04 x y)*qh + x*y^3*(y - x)*(x + y)*(a04 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_mar_00 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((marA x y mh yh qh lh), (marC x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((marA x y mh yh qh lh), (marC x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((marA x y mh yh qh lh), (marC x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^4*(y - x)^2*(x + y)^2*mh + x^3*(a06 x y)*yh + y^3*x^5*(y - x)*(x + y)*qh + y^3*x^5*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_mar_10 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((marB x y mh yh qh lh), (marC x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*mh + (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := y*x^5*(y - x)*(x + y)*mh + y*x^5*(y - x)*(x + y)*yh + x*y^2*(y - x)^3*(x + y)^3*qh + x*y^2*(y - x)^3*(x + y)^3*lh) (by hug2; ring) (by positivity))
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((marB x y mh yh qh lh), (marC x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((marB x y mh yh qh lh), (marC x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x^3*(a06 x y)*mh + x^3*(a06 x y)*yh + y^3*x^5*(y - x)*(x + y)*qh + y^3*x^5*(y - x)*(x + y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_mar_01 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((marA x y mh yh qh lh), (marD x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((marA x y mh yh qh lh), (marD x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((marA x y mh yh qh lh), (marD x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x*y^2*(y - x)*(x + y)*(a02 x y)*mh + x^3*(a03 x y)*yh + x*y^3*(y - x)*(x + y)*(a04 x y)*qh + x*y^3*(y - x)*(x + y)*(a04 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem memT_mar_11 {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : ((marB x y mh yh qh lh), (marD x y mh yh qh lh)) ∈ (Tset x y mh yh qh lh) := by
  have hg := gg_pos h
  obtain ⟨⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩, ⟨hdd, hss, t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26⟩, hmh, hyh, hqh, hlh⟩ := h
  have hbb : 0 < bq x y := hb
  have hC : 0 < TCx x y mh yh qh lh := by unfold TCx; positivity
  have hB : 0 < TBy x y mh yh qh lh := by unfold TBy; positivity
  refine mem_tri0 hC hB ?_ ?_ ?_
  · exact (nonneg_of_eq (G := (a18 x y)*mh + (a18 x y)*yh) (by hug2; ring) (by positivity))
  · exact (nonneg_of_eq (G := 0) (by first | (hug2; ring) | hug2) le_rfl)
  · have e : 0 ≤ TCx x y mh yh qh lh * TBy x y mh yh qh lh - ((((marB x y mh yh qh lh), (marD x y mh yh qh lh))).1 * TBy x y mh yh qh lh + (-(((marB x y mh yh qh lh), (marD x y mh yh qh lh))).2) * TCx x y mh yh qh lh) := by
      exact nonneg_of_eq (G := (gg x y mh yh qh lh) * (bq x y) * (x^3*(a03 x y)*mh + x^3*(a03 x y)*yh + x*y^3*(y - x)*(x + y)*(a04 x y)*qh + x*y^3*(y - x)*(x + y)*(a04 x y)*lh)) (by hug2; ring) (by positivity)
    linarith

theorem subT_red {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Sred x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  sub_tri3 (convex_convexHull ℝ _) (memT_P0 h) (memT_P1 h) (memT_P2 h)

theorem subT_orange {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Sora x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  sub_tri3 (convex_convexHull ℝ _) (memT_P1 h) (memT_P2 h) (memT_P3 h)

theorem subT_lgreen {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Slgr x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  sub_tri3 (convex_convexHull ℝ _) (memT_P4 h) (memT_P3 h) (memT_P1 h)

theorem subT_green {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Sgre x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  sub_tri3 (convex_convexHull ℝ _) (memT_P5 h) (memT_P6 h) (memT_P7 h)

theorem subT_cyan {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Scya x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  sub_tri3 (convex_convexHull ℝ _) (memT_P7 h) (memT_P3 h) (memT_P6 h)

theorem subT_lav_big {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Slbg x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  sub_tri3 (convex_convexHull ℝ _) (memT_P8 h) (memT_P7 h) (memT_P3 h)

theorem subT_pink_big {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Spbg x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  sub_tri3 (convex_convexHull ℝ _) (memT_P9 h) (memT_P8 h) (memT_P3 h)

theorem subT_yellow {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Syel x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  rect_subset (convex_convexHull ℝ _) (yel_ab h) (yel_cd h) (memT_yel_00 h) (memT_yel_10 h) (memT_yel_01 h) (memT_yel_11 h)

theorem subT_maroon {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Smar x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) :=
  rect_subset (convex_convexHull ℝ _) (mar_ab h) (mar_cd h) (memT_mar_00 h) (memT_mar_10 h) (memT_mar_01 h) (memT_mar_11 h)

theorem subT_lav_low {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Sllw x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  exact par_subset (convex_convexHull ℝ _) (llw_ab h) (llw_cd h)
    (by rw [kc_llw_0 hx0]; exact memT_P14 h)
    (by rw [kc_llw_1 hx0]; exact memT_P15 h)
    (by rw [kc_llw_2 hx0]; exact memT_P13 h)
    (by rw [kc_llw_3 hx0]; exact memT_P4 h)

theorem subT_pink_low {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh) : (Splw x y mh yh qh lh) ⊆ (Tset x y mh yh qh lh) := by
  have hx0 : x ≠ 0 := h.lp.hx.ne'
  exact par_subset (convex_convexHull ℝ _) (plw_ab h) (plw_cd h)
    (by rw [kc_plw_0 hx0]; exact memT_P5 h)
    (by rw [kc_plw_1 hx0]; exact memT_P6 h)
    (by rw [kc_plw_2 hx0]; exact memT_P14 h)
    (by rw [kc_plw_3 hx0]; exact memT_P15 h)


end Erdos634.Draft.HerdtFamily
