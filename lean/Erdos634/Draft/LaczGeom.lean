/-
Draft/LaczGeom.lean — the GEOMETRY of Laczkovich's macro-dissection of the isosceles triangle with base angles `α`
(tile `(a, b, c) = (u², v² - u², u v)`, `γ = 2α`, `u < v < 2u`) into seven triangles similar to the tile and one
parallelogram (Lead 1 of private/ROOM/DISCOVERY/leads4.md; reconstruction `rust/g3g/src/bin/recon.rs`; macro-dissection
due to M. Laczkovich, as reported in Beeson's "Tilings of an isosceles triangle", sec. 9).

Frame.  The skew frame `Φ_f`, `f = -u/v` (basis angle `π - α`), with the parallelogram axis-aligned.  All ten
vertices `P0 … P9` have INTEGER-polynomial coordinates in `(x, y, z) = (u, v, K)` (`K ≥ 1` the scale multiplier;
`K = 1` gives scales `u⁵v, u⁶, u⁴b, u³vb, uvb², u²v²b, v²b²`, `b = v² - u²`).  The seven triangles are
`Hbl Hlg Hgr Hlb Hor Hpk Hrd`, the parallelogram is the rectangle `Rw = [0, U] × [0, V]`,
`U = K u⁵ v b`, `V = K ((v²-u²)³ v² - u⁸)`; the target is `HT = hull {P5, P4, P9}`.
This file proves (for real `x y z` with `0 < x < y < 2x`, `z > 0`, `Vp = (y²-x²)³y² - x⁸ > 0`): the 28 pairwise
interior-disjointness statements and the containment of every piece in `HT`.  Every sign condition is a polynomial
identity (`ring`) against a product of manifestly positive atoms (`bq, q1..q5, Vp`); `lb`-`or`, `lb`-`rd` need the case
split `y² ≤ 2x²` / `y² ≥ 2x²`.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.LaczBase

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect)

namespace Erdos634.Draft.LaczFamily
open Erdos634.Draft.S2L (mem_hull3' rect_subset)

def bq (x y : ℝ) : ℝ := y ^ 2 - x ^ 2
def q1 (x y : ℝ) : ℝ := x ^ 4 - x ^ 2 * y ^ 2 + y ^ 4
def q2 (x y : ℝ) : ℝ := 2 * x ^ 4 - 2 * x ^ 2 * y ^ 2 + y ^ 4
def q3 (x y : ℝ) : ℝ := x ^ 6 + x ^ 4 * y ^ 2 - 2 * x ^ 2 * y ^ 4 + y ^ 6
def q4 (x y : ℝ) : ℝ := 3 * x ^ 4 - 3 * x ^ 2 * y ^ 2 + y ^ 4
def q5 (x y : ℝ) : ℝ := x ^ 6 - x ^ 2 * y ^ 4 + y ^ 6
def Vp (x y : ℝ) : ℝ := (bq x y) ^ 3 * y ^ 2 - x ^ 8
def n2 (x y : ℝ) : ℝ := 2 * x ^ 2 - y ^ 2
def m2 (x y : ℝ) : ℝ := y ^ 2 - 2 * x ^ 2
def t3 (x y : ℝ) : ℝ := 3 * x ^ 2 - y ^ 2
def q6 (x y : ℝ) : ℝ := 3 * x ^ 6 - 5 * x ^ 4 * y ^ 2 + 4 * x ^ 2 * y ^ 4 - y ^ 6
def Ub (x y z : ℝ) : ℝ := z * x ^ 5 * y * bq x y
def Vb (x y z : ℝ) : ℝ := z * Vp x y

def P0 (x y z : ℝ) : ℝ × ℝ := (z*x*y*(bq x y)^3, -(z*(x^8 + x^6*y^2 - 4*x^4*y^4 + 4*x^2*y^6 - y^8)))
def P1 (x y z : ℝ) : ℝ × ℝ := (0, -(z*x^4*q1 x y))
def P2 (x y z : ℝ) : ℝ × ℝ := (Ub x y z, -(z*x^8))
def P3 (x y z : ℝ) : ℝ × ℝ := (0, -(z*x^6*y^2))
def P4 (x y z : ℝ) : ℝ × ℝ := (0, -(z*x^2*q5 x y))
def P5 (x y z : ℝ) : ℝ × ℝ := (z*x*y*bq x y*q1 x y, Vb x y z)
def P6 (x y z : ℝ) : ℝ × ℝ := (Ub x y z, 0)
def P7 (x y z : ℝ) : ℝ × ℝ := (Ub x y z, Vb x y z)
def P8 (x y z : ℝ) : ℝ × ℝ := (0, 0)
def P9 (x y z : ℝ) : ℝ × ℝ := (0, Vb x y z)

macro "ug" : tactic => `(tactic| simp only [cross, bq, q1, q2, q3, q4, q5, Vp, n2, m2, t3, q6, Ub, Vb,
  P0, P1, P2, P3, P4, P5, P6, P7, P8, P9])

/-- the standing hypotheses. -/
structure LP (x y z : ℝ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : x < y
  hy2 : y < 2 * x
  hb : 0 < bq x y
  hq1 : 0 < q1 x y
  hq2 : 0 < q2 x y
  hq3 : 0 < q3 x y
  hq4 : 0 < q4 x y
  hq5 : 0 < q5 x y
  hV : 0 < Vp x y

theorem LP.mk' {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x < y) (hy2 : y < 2 * x)
    (hV : 0 < Vp x y) : LP x y z where
  hx := hx
  hy := hy
  hz := hz
  hxy := hxy
  hy2 := hy2
  hb := by unfold bq; nlinarith
  hq1 := by unfold q1; nlinarith [sq_nonneg (x ^ 2 - y ^ 2), mul_pos (pow_pos hx 2) (pow_pos hy 2)]
  hq2 := by unfold q2; nlinarith [sq_nonneg (x ^ 2 - y ^ 2), pow_pos hx 4]
  hq3 := by
    unfold q3
    have : 0 < y ^ 2 * (x ^ 2 - y ^ 2) ^ 2 + x ^ 6 := by positivity
    nlinarith
  hq4 := by unfold q4; nlinarith [sq_nonneg (y ^ 2 - 3 / 2 * x ^ 2), pow_pos hx 4]
  hq5 := by
    unfold q5
    have h1 : 0 < y ^ 2 - x ^ 2 := by nlinarith
    have : 0 < y ^ 4 * (y ^ 2 - x ^ 2) + x ^ 6 := by positivity
    nlinarith
  hV := hV

/-- the pieces. -/
abbrev Hbl (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P2 x y z, P0 x y z, P1 x y z} : Set (ℝ × ℝ))
abbrev Hlg (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P2 x y z, P1 x y z, P3 x y z} : Set (ℝ × ℝ))
abbrev Hgr (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P1 x y z, P4 x y z, P0 x y z} : Set (ℝ × ℝ))
abbrev Hlb (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P0 x y z, P5 x y z, P2 x y z} : Set (ℝ × ℝ))
abbrev Hor (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P6 x y z, P3 x y z, P2 x y z} : Set (ℝ × ℝ))
abbrev Hpk (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P5 x y z, P7 x y z, P2 x y z} : Set (ℝ × ℝ))
abbrev Hrd (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P3 x y z, P8 x y z, P6 x y z} : Set (ℝ × ℝ))
abbrev Rw (x y z : ℝ) : Set (ℝ × ℝ) := Rect 0 (Ub x y z) 0 (Vb x y z)
abbrev HT (x y z : ℝ) : Set (ℝ × ℝ) := convexHull ℝ ({P5 x y z, P4 x y z, P9 x y z} : Set (ℝ × ℝ))

theorem d_0_1 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hbl x y z)) (interior (Hlg x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P1 x y z) (P2 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (Or.inr (Or.inr (pos_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity))))

theorem d_0_2 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hbl x y z)) (interior (Hgr x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P0 x y z) (P1 x y z) (1 : ℝ) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^3*y^3*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inr (Or.inl (pos_of_eq (G := z^2*x^3*y^3*(bq x y)^5) (by ug; ring) (by positivity))))

theorem d_0_3 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hbl x y z)) (interior (Hlb x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P2 x y z) (P0 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inr (Or.inl (pos_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity))))

theorem d_0_4 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hbl x y z)) (interior (Hor x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P1 x y z) (P2 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inl (pos_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)))

theorem d_0_5 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hbl x y z)) (interior (Hpk x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact (sep33 (P2 x y z) (P5 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (Or.inr (Or.inl (pos_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity))))).symm

theorem d_0_6 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hbl x y z)) (interior (Hrd x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P1 x y z) (P2 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)*(q1 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)))

theorem d_0_7 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hbl x y z)) (interior (Rw x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hU : 0 < Ub x y z := by unfold Ub; positivity
  have hV' : 0 < Vb x y z := by unfold Vb; positivity
  exact sep3R (hU) (hV') (P1 x y z) (P2 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)*(q1 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^2*(q2 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := y*z^2*x^9*(bq x y)*(q1 x y)) (by ug; ring) (by positivity)))

theorem d_1_2 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlg x y z)) (interior (Hgr x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P2 x y z) (P1 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (Or.inr (Or.inl (pos_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity))))

theorem d_1_3 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlg x y z)) (interior (Hlb x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P2 x y z) (P1 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inl (pos_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)))

theorem d_1_4 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlg x y z)) (interior (Hor x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P3 x y z) (P2 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inl (pos_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)))

theorem d_1_5 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlg x y z)) (interior (Hpk x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact (sep33 (P7 x y z) (P2 x y z) (-1 : ℝ) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (Or.inr (Or.inl (pos_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity))))).symm

theorem d_1_6 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlg x y z)) (interior (Hrd x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P3 x y z) (P2 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (Or.inr (Or.inl (pos_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity))))

theorem d_1_7 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlg x y z)) (interior (Rw x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hU : 0 < Ub x y z := by unfold Ub; positivity
  have hV' : 0 < Vb x y z := by unfold Vb; positivity
  exact sep3R (hU) (hV') (P3 x y z) (P2 x y z) (1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^9*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)^2*(q3 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity)))

theorem d_2_3 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hgr x y z)) (interior (Hlb x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P0 x y z) (P1 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^3*y^3*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (Or.inr (Or.inl (pos_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity))))

theorem d_2_4 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hgr x y z)) (interior (Hor x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P0 x y z) (P1 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^3*y^3*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^7*(bq x y)^3*(x^2+y^2)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := y*z^2*x^7*(bq x y)^3*(x^2+y^2)) (by ug; ring) (by positivity)))

theorem d_2_5 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hgr x y z)) (interior (Hpk x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P0 x y z) (P1 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^3*y^3*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^3*(q4 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^7*(bq x y)^3) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)))

theorem d_2_6 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hgr x y z)) (interior (Hrd x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P0 x y z) (P1 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^3*y^3*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)^3*(q1 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^7*(bq x y)^3*(x^2+y^2)) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := y*z^2*x^5*(bq x y)^5) (by ug; ring) (by positivity)))

theorem d_2_7 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hgr x y z)) (interior (Rw x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hU : 0 < Ub x y z := by unfold Ub; positivity
  have hV' : 0 < Vb x y z := by unfold Vb; positivity
  exact sep3R (hU) (hV') (P0 x y z) (P1 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^3*y^3*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)^3*(q1 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^7*(bq x y)^3*(x^2+y^2)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := x*z^2*y^3*(bq x y)^4*(q2 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^3*(q4 x y)) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := y*z^2*x^5*(bq x y)^3*(q1 x y)) (by ug; ring) (by positivity)))

theorem d_3_4_A {x y z : ℝ} (h : LP x y z) (hc : 2 * x ^ 2 ≤ y ^ 2) : Disjoint (interior (Hlb x y z)) (interior (Hor x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hm2 : 0 ≤ m2 x y := by unfold m2; linarith
  exact sep33 (P5 x y z) (P2 x y z) (-1 : ℝ) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^9*(bq x y)^2) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^3*(m2 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inl (pos_of_eq (G := z^2*y^3*x^9*(bq x y)^2) (by ug; ring) (by positivity)))
theorem d_3_4_B {x y z : ℝ} (h : LP x y z) (hc : y ^ 2 ≤ 2 * x ^ 2) : Disjoint (interior (Hlb x y z)) (interior (Hor x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hn2 : 0 ≤ n2 x y := by unfold n2; linarith
  have ht3 : 0 < t3 x y := by unfold t3; nlinarith
  have hq6 : 0 ≤ q6 x y := by
    have e : q6 x y = x ^ 6 + (bq x y) ^ 2 * n2 x y := by unfold q6 bq n2; ring
    rw [e]; positivity
  exact sep33 (P2 x y z) (P0 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^9*(bq x y)*(n2 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^3*(t3 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inr (Or.inl (pos_of_eq (G := z^2*y^3*x^5*(bq x y)^3*(t3 x y)) (by ug; ring) (by positivity))))
theorem d_3_4 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlb x y z)) (interior (Hor x y z)) := by
  rcases le_total (2 * x ^ 2) (y ^ 2) with hc | hc
  · exact d_3_4_A h hc
  · exact d_3_4_B h hc

theorem d_3_5 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlb x y z)) (interior (Hpk x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P5 x y z) (P2 x y z) (-1 : ℝ) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inr (Or.inl (pos_of_eq (G := x*z^2*y^5*(bq x y)^5) (by ug; ring) (by positivity))))

theorem d_3_6_A {x y z : ℝ} (h : LP x y z) (hc : 2 * x ^ 2 ≤ y ^ 2) : Disjoint (interior (Hlb x y z)) (interior (Hrd x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hm2 : 0 ≤ m2 x y := by unfold m2; linarith
  exact sep33 (P5 x y z) (P2 x y z) (-1 : ℝ) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^3*(m2 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^2*(q2 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^9*(bq x y)^2) (by ug; ring) (by positivity)) (Or.inr (Or.inl (pos_of_eq (G := z^2*y^3*x^5*(bq x y)^2*(q2 x y)) (by ug; ring) (by positivity))))
theorem d_3_6_B {x y z : ℝ} (h : LP x y z) (hc : y ^ 2 ≤ 2 * x ^ 2) : Disjoint (interior (Hlb x y z)) (interior (Hrd x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hn2 : 0 ≤ n2 x y := by unfold n2; linarith
  have ht3 : 0 < t3 x y := by unfold t3; nlinarith
  have hq6 : 0 ≤ q6 x y := by
    have e : q6 x y = x ^ 6 + (bq x y) ^ 2 * n2 x y := by unfold q6 bq n2; ring
    rw [e]; positivity
  exact sep33 (P2 x y z) (P0 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^3*(t3 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)*(q6 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^9*(bq x y)*(n2 x y)) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := z^2*y^3*x^5*(bq x y)^3*(t3 x y)) (by ug; ring) (by positivity)))
theorem d_3_6 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlb x y z)) (interior (Hrd x y z)) := by
  rcases le_total (2 * x ^ 2) (y ^ 2) with hc | hc
  · exact d_3_6_A h hc
  · exact d_3_6_B h hc

theorem d_3_7 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hlb x y z)) (interior (Rw x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hU : 0 < Ub x y z := by unfold Ub; positivity
  have hV' : 0 < Vb x y z := by unfold Vb; positivity
  exact sep3R (hU) (hV') (P5 x y z) (P2 x y z) (-1 : ℝ) (nonneg_of_eq (G := z^2*x^5*y^5*(bq x y)^3) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^2*(q2 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^9*(bq x y)^2) (by ug; ring) (by positivity)) (nonneg_of_eq (G := x*z^2*y^3*(bq x y)^4*(q1 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^5) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := z^2*y^3*x^5*(bq x y)^2*(q2 x y)) (by ug; ring) (by positivity)))

theorem d_4_5 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hor x y z)) (interior (Hpk x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P2 x y z) (P6 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^9*(bq x y)^2) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inl (pos_of_eq (G := z^2*y^3*x^9*(bq x y)^2) (by ug; ring) (by positivity)))

theorem d_4_6 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hor x y z)) (interior (Hrd x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P6 x y z) (P3 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inr (Or.inl (pos_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity))))

theorem d_4_7 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hor x y z)) (interior (Rw x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hU : 0 < Ub x y z := by unfold Ub; positivity
  have hV' : 0 < Vb x y z := by unfold Vb; positivity
  exact sep3R (hU) (hV') (P6 x y z) (P3 x y z) (-1 : ℝ) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^13*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)^2*(q3 x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)*(Vp x y)) (by ug; ring) (by positivity)) (Or.inl (pos_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity)))

theorem d_5_6 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hpk x y z)) (interior (Hrd x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact sep33 (P7 x y z) (P2 x y z) (-1 : ℝ) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inl (pos_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)))

theorem d_5_7 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hpk x y z)) (interior (Rw x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hU : 0 < Ub x y z := by unfold Ub; positivity
  have hV' : 0 < Vb x y z := by unfold Vb; positivity
  exact sep3R (hU) (hV') (P7 x y z) (P2 x y z) (-1 : ℝ) (nonneg_of_eq (G := x*z^2*y^5*(bq x y)^5) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (Or.inl (pos_of_eq (G := z^2*y^3*x^5*(bq x y)^4) (by ug; ring) (by positivity)))

theorem d_6_7 {x y z : ℝ} (h : LP x y z) : Disjoint (interior (Hrd x y z)) (interior (Rw x y z)) := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have hU : 0 < Ub x y z := by unfold Ub; positivity
  have hV' : 0 < Vb x y z := by unfold Vb; positivity
  exact sep3R (hU) (hV') (P8 x y z) (P6 x y z) (1 : ℝ) (nonneg_of_eq (G := z^2*y^3*x^11*(bq x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := 0) (by ug; ring) le_rfl) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)*(Vp x y)) (by ug; ring) (by positivity)) (nonneg_of_eq (G := y*z^2*x^5*(bq x y)*(Vp x y)) (by ug; ring) (by positivity)) (Or.inr (Or.inr (Or.inl (pos_of_eq (G := y*z^2*x^5*(bq x y)*(Vp x y)) (by ug; ring) (by positivity)))))


/-! ### containment in the target `HT = hull {P5, P4, P9}` -/
theorem mem_P0 {x y z : ℝ} (h : LP x y z) : P0 x y z ∈ HT x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact mem_hull3' (A := P5 x y z) (B := P4 x y z) (C := P9 x y z) (x*z^2*y^3*(bq x y)^2*(q1 x y)^2) (x*z^2*y^3*(bq x y)^4*(q1 x y)) (z^2*x^3*y^5*(bq x y)^2*(q1 x y)) (0)
    (by positivity) (by positivity) (by positivity) (le_refl _) (by ug; ring) _ (by ug; ring) (by ug; ring)

theorem mem_P1 {x y z : ℝ} (h : LP x y z) : P1 x y z ∈ HT x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact mem_hull3' (A := P5 x y z) (B := P4 x y z) (C := P9 x y z) (x*z^2*y^3*(bq x y)^2*(q1 x y)^2) (0) (x*z^2*y^3*(bq x y)^2*(q1 x y)*(q2 x y)) (z^2*x^3*y^3*(bq x y)^3*(q1 x y))
    (by positivity) (le_refl _) (by positivity) (by positivity) (by ug; ring) _ (by ug; ring) (by ug; ring)

theorem mem_P2 {x y z : ℝ} (h : LP x y z) : P2 x y z ∈ HT x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact mem_hull3' (A := P5 x y z) (B := P4 x y z) (C := P9 x y z) (x*z^2*y^3*(bq x y)^2*(q1 x y)^2) (z^2*y^3*x^5*(bq x y)^2*(q1 x y)) (x*z^2*y^3*(bq x y)^4*(q1 x y)) (z^2*x^3*y^3*(bq x y)^3*(q1 x y))
    (by positivity) (by positivity) (by positivity) (by positivity) (by ug; ring) _ (by ug; ring) (by ug; ring)

theorem mem_P3 {x y z : ℝ} (h : LP x y z) : P3 x y z ∈ HT x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact mem_hull3' (A := P5 x y z) (B := P4 x y z) (C := P9 x y z) (x*z^2*y^3*(bq x y)^2*(q1 x y)^2) (0) (x*y*z^2*(bq x y)^2*(q1 x y)*(q3 x y)) (y*z^2*x^3*(bq x y)^3*(x^2+y^2)*(q1 x y))
    (by positivity) (le_refl _) (by positivity) (by positivity) (by ug; ring) _ (by ug; ring) (by ug; ring)

theorem mem_P6 {x y z : ℝ} (h : LP x y z) : P6 x y z ∈ HT x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact mem_hull3' (A := P5 x y z) (B := P4 x y z) (C := P9 x y z) (x*z^2*y^3*(bq x y)^2*(q1 x y)^2) (z^2*y^3*x^5*(bq x y)^2*(q1 x y)) (x*y*z^2*(bq x y)*(q1 x y)*(Vp x y)) (y*z^2*x^3*(bq x y)*(q1 x y)*(q3 x y))
    (by positivity) (by positivity) (by positivity) (by positivity) (by ug; ring) _ (by ug; ring) (by ug; ring)

theorem mem_P7 {x y z : ℝ} (h : LP x y z) : P7 x y z ∈ HT x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact mem_hull3' (A := P5 x y z) (B := P4 x y z) (C := P9 x y z) (x*z^2*y^3*(bq x y)^2*(q1 x y)^2) (z^2*y^3*x^5*(bq x y)^2*(q1 x y)) (0) (x*z^2*y^5*(bq x y)^3*(q1 x y))
    (by positivity) (by positivity) (le_refl _) (by positivity) (by ug; ring) _ (by ug; ring) (by ug; ring)

theorem mem_P8 {x y z : ℝ} (h : LP x y z) : P8 x y z ∈ HT x y z := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  exact mem_hull3' (A := P5 x y z) (B := P4 x y z) (C := P9 x y z) (x*z^2*y^3*(bq x y)^2*(q1 x y)^2) (0) (x*y*z^2*(bq x y)*(q1 x y)*(Vp x y)) (y*z^2*x^3*(bq x y)*(q1 x y)*(q5 x y))
    (by positivity) (le_refl _) (by positivity) (by positivity) (by ug; ring) _ (by ug; ring) (by ug; ring)

theorem mem_P5 {x y z : ℝ} : P5 x y z ∈ HT x y z := subset_convexHull ℝ _ (by simp)
theorem mem_P4 {x y z : ℝ} : P4 x y z ∈ HT x y z := subset_convexHull ℝ _ (by simp)
theorem mem_P9 {x y z : ℝ} : P9 x y z ∈ HT x y z := subset_convexHull ℝ _ (by simp)

theorem sub_tri {x y z : ℝ} {a b c : ℝ × ℝ} (ha : a ∈ HT x y z) (hb : b ∈ HT x y z) (hc : c ∈ HT x y z) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) ⊆ HT x y z := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem sub_blue {x y z : ℝ} (h : LP x y z) : Hbl x y z ⊆ HT x y z :=
  sub_tri (mem_P2 h) (mem_P0 h) (mem_P1 h)

theorem sub_lg {x y z : ℝ} (h : LP x y z) : Hlg x y z ⊆ HT x y z :=
  sub_tri (mem_P2 h) (mem_P1 h) (mem_P3 h)

theorem sub_green {x y z : ℝ} (h : LP x y z) : Hgr x y z ⊆ HT x y z :=
  sub_tri (mem_P1 h) (mem_P4) (mem_P0 h)

theorem sub_lb {x y z : ℝ} (h : LP x y z) : Hlb x y z ⊆ HT x y z :=
  sub_tri (mem_P0 h) (mem_P5) (mem_P2 h)

theorem sub_orange {x y z : ℝ} (h : LP x y z) : Hor x y z ⊆ HT x y z :=
  sub_tri (mem_P6 h) (mem_P3 h) (mem_P2 h)

theorem sub_pink {x y z : ℝ} (h : LP x y z) : Hpk x y z ⊆ HT x y z :=
  sub_tri (mem_P5) (mem_P7 h) (mem_P2 h)

theorem sub_red {x y z : ℝ} (h : LP x y z) : Hrd x y z ⊆ HT x y z :=
  sub_tri (mem_P3 h) (mem_P8 h) (mem_P6 h)

theorem sub_rect {x y z : ℝ} (h : LP x y z) : Rw x y z ⊆ HT x y z := by
  have hU : 0 < Ub x y z := by obtain ⟨hx, hy, hz, hxy, hy2, hb, -⟩ := h; unfold Ub; positivity
  have hV' : 0 < Vb x y z := by obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h; unfold Vb; positivity
  exact rect_subset (convex_convexHull ℝ _) hU hV' (mem_P8 h) (mem_P6 h) (mem_P9) (mem_P7 h)

end Erdos634.Draft.LaczFamily
