/-
Draft/ResidueStrips.lean -- the strips of the hexagon of the residue seed (member `(u, v)`, scale `m = v + t`).

Coordinates `(X, Y)` of the frame `Φ_φ`, `φ = φβ u e`; `u = t + r`, `v = t + r + e`, `a = uv`, `c = v²`, `b = v² − u²`.
The strip number `j` lies between the levels `Y = c u j` and `Y = c u (j + 1)` and is, from left to right:

  `SL j` (`j < t`):          `TA` (scale `u`),  `v + q_j` columns of cells `a × c`,  `q_j` columns `c × a`,  `TB` (scale `v`);
  `SM j` (`t ≤ j < J`):      `TB'` (scale `v`), `v + q*` columns `a × c`,            `q*` columns `c × a`,   `TB` (scale `v`);
  `SK`   (`j = J`):          the same, with `TB` at scale `ρ` and a rectangle of `ρ × (v − ρ)` cells `c × a` above it;
  `SU j` (`J < j < w`):      `TB'` (scale `v`), `K` columns `a × c`, `v (w − 1 − j)` columns `c × a`, up to `X = c u m`;
  `STOP`:                    `TA` at scale `K` above the level `c u w`.

Here `J`, `ρ` are given by `u m = v J + ρ`, `q_j = (e − 1) u + e j`, `q* = (e − 1) u + e (t − 1)`, `K = e (u + v + t)`.
For each strip: a tiling (`rt_SL`, …) and the inequalities that hold on it (`SL_bounds`, …): the two levels,
`v Y − u X ≥ 0`, the line of the left boundary, and `X ≤ c u m`.

The construction is due to D. Paliy (2026, unrefereed).  No sorry, no native_decide.
-/
import Erdos634.Draft.ResidueTools

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.Residue
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.CollarG (φβ hφβ ca cb hapos hbpos hvpos hPpos)

theorem mem_OR {x0 x1 y0 y1 : ℝ} {q : ℝ × ℝ} (hq : q ∈ ORect x0 x1 y0 y1) :
    x0 ≤ q.1 ∧ q.1 ≤ x1 ∧ y0 ≤ q.2 ∧ q.2 ≤ y1 := hq.2

/-! ## Real arithmetic: boxes and diagonals -/

theorem box_N {U V X Y xr ylo : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hx : X ≤ xr) (hy : ylo ≤ Y) :
    V * ylo - U * xr ≤ V * Y - U * X := by
  nlinarith [mul_le_mul_of_nonneg_left hx hU, mul_le_mul_of_nonneg_left hy hV]

theorem box_L {U V X Y xl yhi : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hx : xl ≤ X) (hy : Y ≤ yhi) :
    V * xl - U * yhi ≤ V * X - U * Y := by
  nlinarith [mul_le_mul_of_nonneg_left hx hV, mul_le_mul_of_nonneg_left hy hU]

theorem box_M {U V X Y xl yhi : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hx : xl ≤ X) (hy : Y ≤ yhi) :
    U * xl - V * yhi ≤ U * X - V * Y := by
  nlinarith [mul_le_mul_of_nonneg_left hx hU, mul_le_mul_of_nonneg_left hy hV]

theorem diag_N {U V X Y x0 y0 : ℝ} (hV : 0 < V) (h : U * V * (X - x0) ≤ V ^ 2 * (Y - y0)) :
    V * y0 - U * x0 ≤ V * Y - U * X := by
  refine le_of_mul_le_mul_left ?_ hV
  nlinarith [h]

theorem diag_L {U V X Y x0 y0 : ℝ} (hV : 0 < V) (h : U * V * (Y - y0) ≤ V ^ 2 * (X - x0)) :
    V * x0 - U * y0 ≤ V * X - U * Y := by
  refine le_of_mul_le_mul_left ?_ hV
  nlinarith [h]

theorem diag_M {U V X Y xl y0 : ℝ} (hV : 0 < V) (h : V ^ 2 * (Y - y0) ≤ U * V * (X - xl)) :
    U * xl - V * y0 ≤ U * X - V * Y := by
  refine le_of_mul_le_mul_left ?_ hV
  nlinarith [h]

/-! ## Pieces side by side -/

theorem chain2 {φ : ℝ} (hφ : 1 < 4 * φ ^ 2) {M : Erdos634.Geometry.Tri} {P1 P2 : Set (ℝ × ℝ)} {n1 n2 : ℕ} (x1 : ℝ)
    (R1 : Nonempty (RTiling (Phi φ '' P1) M n1)) (R2 : Nonempty (RTiling (Phi φ '' P2) M n2))
    (a1 : ∀ q ∈ P1, q.1 ≤ x1) (b2 : ∀ q ∈ P2, x1 ≤ q.1) :
    Nonempty (RTiling (Phi φ '' (P1 ∪ P2)) M (n1 + n2)) :=
  unionF hφ R1 R2 (interior_disj_fst x1 a1 b2)

theorem chain3 {φ : ℝ} (hφ : 1 < 4 * φ ^ 2) {M : Erdos634.Geometry.Tri} {P1 P2 P3 : Set (ℝ × ℝ)} {n1 n2 n3 : ℕ}
    (x1 x2 : ℝ) (h12 : x1 ≤ x2)
    (R1 : Nonempty (RTiling (Phi φ '' P1) M n1)) (R2 : Nonempty (RTiling (Phi φ '' P2) M n2))
    (R3 : Nonempty (RTiling (Phi φ '' P3) M n3))
    (a1 : ∀ q ∈ P1, q.1 ≤ x1) (b2 : ∀ q ∈ P2, x1 ≤ q.1) (a2 : ∀ q ∈ P2, q.1 ≤ x2) (b3 : ∀ q ∈ P3, x2 ≤ q.1) :
    Nonempty (RTiling (Phi φ '' (P1 ∪ P2 ∪ P3)) M (n1 + n2 + n3)) := by
  refine unionF hφ (chain2 hφ x1 R1 R2 a1 b2) R3 (interior_disj_fst x2 ?_ b3)
  rintro q (h | h)
  · exact (a1 q h).trans h12
  · exact a2 q h

theorem chain4 {φ : ℝ} (hφ : 1 < 4 * φ ^ 2) {M : Erdos634.Geometry.Tri} {P1 P2 P3 P4 : Set (ℝ × ℝ)}
    {n1 n2 n3 n4 : ℕ} (x1 x2 x3 : ℝ) (h12 : x1 ≤ x2) (h23 : x2 ≤ x3)
    (R1 : Nonempty (RTiling (Phi φ '' P1) M n1)) (R2 : Nonempty (RTiling (Phi φ '' P2) M n2))
    (R3 : Nonempty (RTiling (Phi φ '' P3) M n3)) (R4 : Nonempty (RTiling (Phi φ '' P4) M n4))
    (a1 : ∀ q ∈ P1, q.1 ≤ x1) (b2 : ∀ q ∈ P2, x1 ≤ q.1) (a2 : ∀ q ∈ P2, q.1 ≤ x2) (b3 : ∀ q ∈ P3, x2 ≤ q.1)
    (a3 : ∀ q ∈ P3, q.1 ≤ x3) (b4 : ∀ q ∈ P4, x3 ≤ q.1) :
    Nonempty (RTiling (Phi φ '' (P1 ∪ P2 ∪ P3 ∪ P4)) M (n1 + n2 + n3 + n4)) := by
  refine unionF hφ (chain3 hφ x1 x2 h12 R1 R2 R3 a1 b2 a2 b3) R4 (interior_disj_fst x3 ?_ b4)
  rintro q ((h | h) | h)
  · exact ((a1 q h).trans h12).trans h23
  · exact (a2 q h).trans h23
  · exact a3 q h

/-! ## Coordinates of the strips -/

/-- the level `c u j` -/
def lvl (t r e j : ℝ) : ℝ := (t + r + e) ^ 2 * (t + r) * j
/-- left end of the rectangle of the lower strip `j` -/
def XL (t r e j : ℝ) : ℝ := (t + r) * (t + r + e) * ((t + r) * (j + 1) - ((t + r + e) ^ 2 - (t + r) ^ 2))
/-- left end of the rectangle of the middle strip `j` -/
def XM (t r e j : ℝ) : ℝ :=
  -((t + r) * (t + r + e) * ((t + r + e) ^ 2 - (t + r) ^ 2)) + (t + r) * (t + r + e) * (t + r) * t
    + (t + r + e) ^ 2 * (t + r + e) * (j + 1 - t)
def qL (t r e j : ℝ) : ℝ := (e - 1) * (t + r) + e * j
def qS (t r e : ℝ) : ℝ := (e - 1) * (t + r) + e * (t - 1)
def cK (t r e : ℝ) : ℝ := e * ((t + r) + (t + r + e) + t)

def SL (t r e j : ℝ) : Set (ℝ × ℝ) :=
  TA (t + r) e (XL t r e j - (t + r) * ca (t + r) e) (lvl t r e j) (t + r)
    ∪ Rect (XL t r e j) (XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j)) (lvl t r e j) (lvl t r e (j + 1))
    ∪ ORect (XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j)) ((t + r + e) ^ 2 * (t + r + e) * j)
        (lvl t r e j) (lvl t r e (j + 1))
    ∪ TB (t + r) e ((t + r + e) ^ 2 * (t + r + e) * j) (lvl t r e j) (t + r + e)

def SM (t r e j : ℝ) : Set (ℝ × ℝ) :=
  TB' (t + r) e (XM t r e j) (lvl t r e j) (t + r + e)
    ∪ Rect (XM t r e j) (XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e)) (lvl t r e j) (lvl t r e (j + 1))
    ∪ ORect (XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e)) ((t + r + e) ^ 2 * (t + r + e) * j)
        (lvl t r e j) (lvl t r e (j + 1))
    ∪ TB (t + r) e ((t + r + e) ^ 2 * (t + r + e) * j) (lvl t r e j) (t + r + e)

def SK (t r e J ρ : ℝ) : Set (ℝ × ℝ) :=
  TB' (t + r) e (XM t r e J) (lvl t r e J) (t + r + e)
    ∪ Rect (XM t r e J) (XM t r e J + ca (t + r) e * ((t + r + e) + qS t r e)) (lvl t r e J) (lvl t r e (J + 1))
    ∪ ORect (XM t r e J + ca (t + r) e * ((t + r + e) + qS t r e)) ((t + r + e) ^ 2 * (t + r + e) * J)
        (lvl t r e J) (lvl t r e (J + 1))
    ∪ (TB (t + r) e ((t + r + e) ^ 2 * (t + r + e) * J) (lvl t r e J) ρ
        ∪ Rect ((t + r + e) ^ 2 * (t + r + e) * J) ((t + r + e) ^ 2 * (t + r + e) * J + (t + r + e) ^ 2 * ρ)
            (lvl t r e J + ρ * ca (t + r) e) (lvl t r e (J + 1)))

def SU (t r e j : ℝ) : Set (ℝ × ℝ) :=
  TB' (t + r) e (XM t r e j) (lvl t r e j) (t + r + e)
    ∪ Rect (XM t r e j) (XM t r e j + ca (t + r) e * cK t r e) (lvl t r e j) (lvl t r e (j + 1))
    ∪ ORect (XM t r e j + ca (t + r) e * cK t r e) ((t + r + e) ^ 2 * (t + r) * (t + r + e + t))
        (lvl t r e j) (lvl t r e (j + 1))

def STOP (t r e : ℝ) : Set (ℝ × ℝ) :=
  TA (t + r) e (ca (t + r) e * (t + r) * (t + r + t)) (lvl t r e (t + r + t)) (cK t r e)

/-! ## Parameter facts -/

theorem hB_ge {t r e : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) :
    t + r ≤ (t + r + e) ^ 2 - (t + r) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (by linarith : (0 : ℝ) ≤ t + r), sq_nonneg (e - 1)]

theorem hCB {t r e : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) :
    (t + r + e) ^ 2 ≤ ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) := by
  have hB := hB_ge ht hr he
  have h0 : (0 : ℝ) ≤ t + r := by linarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (t + r + e) ^ 2 - (t + r) ^ 2) (sub_nonneg.mpr ht),
    mul_nonneg h0 (sub_nonneg.mpr hB)]

theorem lvl_succ (t r e j : ℝ) : lvl t r e (j + 1) = lvl t r e j + (t + r + e) ^ 2 * (t + r) := by
  simp only [lvl]; ring

theorem lvl_mono {t r e : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) {i j : ℝ} (h : i ≤ j) :
    lvl t r e i ≤ lvl t r e j := by
  simp only [lvl]
  have : (0 : ℝ) ≤ (t + r + e) ^ 2 * (t + r) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h this]

/-! ## The inequalities on the strips -/

set_option maxHeartbeats 1000000 in
/-- lower strips -/
theorem SL_bounds {t r e j : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) (hj0 : 0 ≤ j) (hjt : j + 1 ≤ t)
    (hq0 : 0 ≤ qL t r e j) {q : ℝ × ℝ} (hq : q ∈ SL t r e j) :
    lvl t r e j ≤ q.2 ∧ q.2 ≤ lvl t r e (j + 1) ∧ 0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧
      -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))
        ≤ (t + r + e) * q.1 - (t + r) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
  have hu : 0 < t + r := by linarith
  have he0 : 0 < e := by linarith
  have hV : 0 < t + r + e := by linarith
  have hB := hB_ge ht hr he
  have hB0 : 0 ≤ (t + r + e) ^ 2 - (t + r) ^ 2 := by linarith only [hB, hu]
  have hC : 0 < (t + r + e) ^ 2 := by positivity
  have hA : 0 < (t + r) * (t + r + e) := by positivity
  have hw : XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j) + (t + r + e) ^ 2 * qL t r e j
      = (t + r + e) ^ 2 * (t + r + e) * j := by simp only [XL, qL, ca]; ring
  have hx2 : XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j) ≤ (t + r + e) ^ 2 * (t + r + e) * j := by
    linarith only [hw, mul_nonneg hC.le hq0]
  have hx1 : XL t r e j ≤ XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j) :=
    le_add_of_nonneg_right (mul_nonneg (hapos hu he0).le (by linarith only [hV, hq0]))
  have k1 : (t + r + e) * lvl t r e j - (t + r) * XL t r e j
      = (t + r) * (t + r + e) * (((t + r + e) ^ 2 - (t + r) ^ 2) * j
          + (t + r) * (((t + r + e) ^ 2 - (t + r) ^ 2) - (t + r))) := by
    simp only [lvl, XL]; ring
  have k1p : 0 ≤ (t + r + e) * lvl t r e j - (t + r) * XL t r e j := by
    rw [k1]
    exact mul_nonneg hA.le (add_nonneg (mul_nonneg hB0 hj0) (mul_nonneg hu.le (by linarith only [hB])))
  have k2 : (t + r + e) * XL t r e j - (t + r) * lvl t r e (j + 1)
      = -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) := by
    simp only [lvl, XL]; ring
  have k3 : (t + r + e) * lvl t r e j - (t + r) * ((t + r + e) ^ 2 * (t + r + e) * j) = 0 := by
    simp only [lvl]; ring
  have k4 := lvl_succ t r e j
  have hstep : (t + r + e) ^ 2 * (t + r + e) * j ≤ (t + r + e) ^ 2 * (t + r + e) * (j + 1) := by
    linarith only [mul_pos hC hV]
  have hcum : (t + r + e) ^ 2 * (t + r + e) * (j + 1) ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
    have h1 : 0 ≤ (t + r) * (t + r + e) - e * t + (t + r + e) * (t - (j + 1)) := by
      linarith only [mul_nonneg he0.le (by linarith only [hr] : (0 : ℝ) ≤ (t + r) - t), mul_nonneg hu.le hu.le,
        mul_nonneg hV.le (sub_nonneg.mpr hjt)]
    linarith only [mul_nonneg hC.le h1]
  rcases hq with ((h | h) | h) | h
  · obtain ⟨m1, m2, m3, m4, m5⟩ := mem_TA hu he0 hu.le h
    simp only [ca] at m2 m5
    have hxr : q.1 ≤ XL t r e j := by linarith only [m2]
    refine ⟨m3, by rw [k4]; linarith only [m4], ?_, ?_, ?_⟩
    · have := box_N hu.le hV.le hxr m3
      linarith only [this, k1p]
    · have h5 := diag_L hV m5
      have k6 : (t + r + e) * (XL t r e j - (t + r) * ((t + r) * (t + r + e))) - (t + r) * lvl t r e j
          = -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)) := by
        simp only [lvl, XL]; ring
      linarith only [h5, k6]
    · linarith only [hxr, hx1, hx2, hstep, hcum]
  · obtain ⟨m1, m2, m3, m4⟩ := h
    refine ⟨m3, m4, ?_, ?_, ?_⟩
    · have := box_N hu.le hV.le (m2.trans hx2) m3
      linarith only [this, k3]
    · have := box_L hu.le hV.le m1 m4
      linarith only [this, k2]
    · linarith only [m2, hx2, hstep, hcum]
  · obtain ⟨m1, m2, m3, m4⟩ := mem_OR h
    refine ⟨m3, m4, ?_, ?_, ?_⟩
    · have := box_N hu.le hV.le m2 m3
      linarith only [this, k3]
    · have := box_L hu.le hV.le (hx1.trans m1) m4
      linarith only [this, k2]
    · linarith only [m2, hstep, hcum]
  · obtain ⟨m1, m2, m3, m4, m5⟩ := mem_TB hu he0 hV.le h
    simp only [ca] at m4 m5
    refine ⟨m3, by rw [k4]; linarith only [m4], ?_, ?_, ?_⟩
    · have := diag_N hV m5
      linarith only [this, k3]
    · have h5 := box_L hu.le hV.le m1 m4
      have k7 : (t + r + e) * ((t + r + e) ^ 2 * (t + r + e) * j)
          - (t + r) * (lvl t r e j + (t + r + e) * ((t + r) * (t + r + e)))
          + (t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2)
          = (t + r + e) ^ 2 * (((t + r + e) ^ 2 - (t + r) ^ 2) * j)
            + (t + r + e) ^ 2 * ((t + r) * (((t + r + e) ^ 2 - (t + r) ^ 2) - (t + r))) := by
        simp only [lvl]; ring
      have k7p : 0 ≤ (t + r + e) ^ 2 * (((t + r + e) ^ 2 - (t + r) ^ 2) * j)
            + (t + r + e) ^ 2 * ((t + r) * (((t + r + e) ^ 2 - (t + r) ^ 2) - (t + r))) :=
        add_nonneg (mul_nonneg hC.le (mul_nonneg hB0 hj0)) (mul_nonneg hC.le (mul_nonneg hu.le (by linarith only [hB])))
      linarith only [h5, k7, k7p]
    · have : (t + r + e) ^ 2 * (t + r + e) * j + (t + r + e) * (t + r + e) ^ 2
          = (t + r + e) ^ 2 * (t + r + e) * (j + 1) := by ring
      linarith only [m2, this, hcum]

set_option maxHeartbeats 1000000 in
/-- the three left pieces of a middle strip (also of the strip with the kink) -/
theorem SM_left {t r e j : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) (hqS : 0 ≤ qS t r e) {q : ℝ × ℝ}
    (hq : q ∈ TB' (t + r) e (XM t r e j) (lvl t r e j) (t + r + e)
      ∪ Rect (XM t r e j) (XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e)) (lvl t r e j) (lvl t r e (j + 1))
      ∪ ORect (XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e)) ((t + r + e) ^ 2 * (t + r + e) * j)
          (lvl t r e j) (lvl t r e (j + 1))) :
    lvl t r e j ≤ q.2 ∧ q.2 ≤ lvl t r e (j + 1) ∧ 0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧
      -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t))
        ≤ (t + r) * q.1 - (t + r + e) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r + e) * j := by
  have hu : 0 < t + r := by linarith
  have he0 : 0 < e := by linarith
  have hV : 0 < t + r + e := by linarith
  have hcb := hCB ht hr he
  have hC : 0 < (t + r + e) ^ 2 := by positivity
  have hA : 0 < (t + r) * (t + r + e) := by positivity
  have hw : XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e) + (t + r + e) ^ 2 * qS t r e
      = (t + r + e) ^ 2 * (t + r + e) * j := by simp only [XM, qS, ca]; ring
  have hx2 : XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e) ≤ (t + r + e) ^ 2 * (t + r + e) * j := by
    linarith only [hw, mul_nonneg hC.le hqS]
  have hx1 : XM t r e j ≤ XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e) :=
    le_add_of_nonneg_right (mul_nonneg (hapos hu he0).le (by linarith only [hV, hqS]))
  have kM1 : (t + r + e) * lvl t r e j - (t + r) * XM t r e j
      = (t + r) * (t + r + e) * (((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - (t + r + e) ^ 2) := by
    simp only [lvl, XM]; ring
  have kM1p : 0 ≤ (t + r + e) * lvl t r e j - (t + r) * XM t r e j := by
    rw [kM1]; exact mul_nonneg hA.le (by linarith only [hcb])
  have kM2 : (t + r) * (XM t r e j - (t + r + e) * (t + r + e) ^ 2) - (t + r + e) * lvl t r e j
      = -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) := by
    simp only [lvl, XM]; ring
  have kM3 : (t + r) * XM t r e j - (t + r + e) * lvl t r e (j + 1)
      = -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) := by
    simp only [lvl, XM]; ring
  have k3 : (t + r + e) * lvl t r e j - (t + r) * ((t + r + e) ^ 2 * (t + r + e) * j) = 0 := by
    simp only [lvl]; ring
  have k4 := lvl_succ t r e j
  rcases hq with (h | h) | h
  · obtain ⟨m1, m2, m3, m4, m5⟩ := mem_TB' hu he0 hV.le h
    simp only [ca] at m4 m5
    refine ⟨m3, by rw [k4]; linarith only [m4], ?_, ?_, by linarith only [m2, hx1, hx2]⟩
    · have := box_N hu.le hV.le m2 m3
      linarith only [this, kM1p]
    · have := diag_M hV m5
      linarith only [this, kM2]
  · obtain ⟨m1, m2, m3, m4⟩ := h
    refine ⟨m3, m4, ?_, ?_, by linarith only [m2, hx2]⟩
    · have := box_N hu.le hV.le (m2.trans hx2) m3
      linarith only [this, k3]
    · have := box_M hu.le hV.le m1 m4
      linarith only [this, kM3]
  · obtain ⟨m1, m2, m3, m4⟩ := mem_OR h
    refine ⟨m3, m4, ?_, ?_, m2⟩
    · have := box_N hu.le hV.le m2 m3
      linarith only [this, k3]
    · have := box_M hu.le hV.le (hx1.trans m1) m4
      linarith only [this, kM3]

set_option maxHeartbeats 1000000 in
/-- middle strips below the kink: `v (j + 1) ≤ u m` -/
theorem SM_bounds {t r e j : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) (hj0 : 0 ≤ j) (hqS : 0 ≤ qS t r e)
    (hjm : (t + r + e) * (j + 1) ≤ (t + r) * (t + r + e + t)) {q : ℝ × ℝ} (hq : q ∈ SM t r e j) :
    lvl t r e j ≤ q.2 ∧ q.2 ≤ lvl t r e (j + 1) ∧ 0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧
      -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t))
        ≤ (t + r) * q.1 - (t + r + e) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
  have hu : 0 < t + r := by linarith
  have he0 : 0 < e := by linarith
  have hV : 0 < t + r + e := by linarith
  have hcb := hCB ht hr he
  have hC : 0 < (t + r + e) ^ 2 := by positivity
  have hA : 0 < (t + r) * (t + r + e) := by positivity
  have hstep : (t + r + e) ^ 2 * (t + r + e) * j ≤ (t + r + e) ^ 2 * (t + r + e) * (j + 1) := by
    linarith only [mul_pos hC hV]
  have hcum : (t + r + e) ^ 2 * (t + r + e) * (j + 1) ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
    linarith only [mul_le_mul_of_nonneg_left hjm hC.le]
  have k3 : (t + r + e) * lvl t r e j - (t + r) * ((t + r + e) ^ 2 * (t + r + e) * j) = 0 := by
    simp only [lvl]; ring
  have k4 := lvl_succ t r e j
  rcases hq with h | h
  · obtain ⟨b1, b2, b3, b4, b5⟩ := SM_left ht hr he hqS h
    exact ⟨b1, b2, b3, b4, by linarith only [b5, hstep, hcum]⟩
  · obtain ⟨m1, m2, m3, m4, m5⟩ := mem_TB hu he0 hV.le h
    simp only [ca] at m4 m5
    refine ⟨m3, by rw [k4]; linarith only [m4], ?_, ?_, ?_⟩
    · have := diag_N hV m5
      linarith only [this, k3]
    · have h5 := box_M hu.le hV.le m1 m4
      have kM4 : (t + r) * ((t + r + e) ^ 2 * (t + r + e) * j)
          - (t + r + e) * (lvl t r e j + (t + r + e) * ((t + r) * (t + r + e)))
          + ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)
          = (t + r) * (t + r + e) * (((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - (t + r + e) ^ 2) := by
        simp only [lvl]; ring
      have kM4p : 0 ≤ (t + r) * (t + r + e) * (((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - (t + r + e) ^ 2) :=
        mul_nonneg hA.le (by linarith only [hcb])
      linarith only [h5, kM4, kM4p]
    · have : (t + r + e) ^ 2 * (t + r + e) * j + (t + r + e) * (t + r + e) ^ 2
          = (t + r + e) ^ 2 * (t + r + e) * (j + 1) := by ring
      linarith only [m2, this, hcum]

set_option maxHeartbeats 1000000 in
/-- the strip with the kink: `u m = v J + ρ`, `0 ≤ ρ ≤ v` -/
theorem SK_bounds {t r e J ρ : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) (hJ0 : 0 ≤ J) (hqS : 0 ≤ qS t r e)
    (hJ : (t + r) * (t + r + e + t) = (t + r + e) * J + ρ) (hρ0 : 0 ≤ ρ) (hρv : ρ ≤ t + r + e) {q : ℝ × ℝ}
    (hq : q ∈ SK t r e J ρ) :
    lvl t r e J ≤ q.2 ∧ q.2 ≤ lvl t r e (J + 1) ∧ 0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧
      -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t))
        ≤ (t + r) * q.1 - (t + r + e) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
  have hu : 0 < t + r := by linarith
  have he0 : 0 < e := by linarith
  have hV : 0 < t + r + e := by linarith
  have hcb := hCB ht hr he
  have hC : 0 < (t + r + e) ^ 2 := by positivity
  have hA : 0 < (t + r) * (t + r + e) := by positivity
  have hJC : (t + r + e) ^ 2 * ((t + r) * (t + r + e + t)) = (t + r + e) ^ 2 * ((t + r + e) * J + ρ) := by rw [hJ]
  have hCρ : 0 ≤ (t + r + e) ^ 2 * ρ := mul_nonneg hC.le hρ0
  have k3 : (t + r + e) * lvl t r e J - (t + r) * ((t + r + e) ^ 2 * (t + r + e) * J) = 0 := by
    simp only [lvl]; ring
  have k4 := lvl_succ t r e J
  have kM4 : (t + r) * ((t + r + e) ^ 2 * (t + r + e) * J) - (t + r + e) * lvl t r e (J + 1)
      + ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)
      = (t + r) * (t + r + e) * (((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - (t + r + e) ^ 2) := by
    simp only [lvl]; ring
  have kM4p : 0 ≤ (t + r) * (t + r + e) * (((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - (t + r + e) ^ 2) :=
    mul_nonneg hA.le (by linarith only [hcb])
  rcases hq with h | (h | h)
  · obtain ⟨b1, b2, b3, b4, b5⟩ := SM_left ht hr he hqS h
    exact ⟨b1, b2, b3, b4, by linarith only [b5, hJC, hCρ]⟩
  · obtain ⟨m1, m2, m3, m4, m5⟩ := mem_TB hu he0 hρ0 h
    simp only [ca] at m4 m5
    have hρA : ρ * ((t + r) * (t + r + e)) ≤ (t + r + e) * ((t + r) * (t + r + e)) :=
      mul_le_mul_of_nonneg_right hρv hA.le
    refine ⟨m3, by rw [k4]; linarith only [m4, hρA], ?_, ?_, by linarith only [m2, hJC]⟩
    · have := diag_N hV m5
      linarith only [this, k3]
    · have h5 := box_M hu.le hV.le m1 m4
      have kM5 : (t + r) * ((t + r + e) ^ 2 * (t + r + e) * J)
          - (t + r + e) * (lvl t r e J + (t + r + e) * ((t + r) * (t + r + e)))
          + ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)
          = (t + r) * (t + r + e) * (((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) - (t + r + e) ^ 2) := by
        simp only [lvl]; ring
      linarith only [h5, kM5, kM4p, mul_le_mul_of_nonneg_left hρA hV.le]
  · obtain ⟨m1, m2, m3, m4⟩ := h
    simp only [ca] at m3
    have hρA0 : 0 ≤ ρ * ((t + r) * (t + r + e)) := mul_nonneg hρ0 hA.le
    refine ⟨by linarith only [m3, hρA0], m4, ?_, ?_, by linarith only [m2, hJC]⟩
    · have h5 := box_N hu.le hV.le m2 m3
      have kKR : (t + r + e) * (lvl t r e J + ρ * ((t + r) * (t + r + e)))
          - (t + r) * ((t + r + e) ^ 2 * (t + r + e) * J + (t + r + e) ^ 2 * ρ) = 0 := by
        simp only [lvl]; ring
      linarith only [h5, kKR]
    · have h5 := box_M hu.le hV.le m1 m4
      linarith only [h5, kM4, kM4p]

set_option maxHeartbeats 1000000 in
/-- strips above the kink -/
theorem SU_bounds {t r e J ρ j : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e)
    (hJ : (t + r) * (t + r + e + t) = (t + r + e) * J + ρ) (hρv : ρ ≤ t + r + e)
    (hJj : J + 1 ≤ j) (hjw : j + 1 ≤ t + r + t) {q : ℝ × ℝ} (hq : q ∈ SU t r e j) :
    lvl t r e j ≤ q.2 ∧ q.2 ≤ lvl t r e (j + 1) ∧ 0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧
      -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t))
        ≤ (t + r) * q.1 - (t + r + e) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
  have hu : 0 < t + r := by linarith
  have he0 : 0 < e := by linarith
  have hV : 0 < t + r + e := by linarith
  have hC : 0 < (t + r + e) ^ 2 := by positivity
  have hA : 0 < (t + r) * (t + r + e) := by positivity
  have hK0 : 0 ≤ cK t r e := by simp only [cK]; positivity
  have hw : XM t r e j + ca (t + r) e * cK t r e + (t + r + e) ^ 2 * ((t + r + e) * ((t + r + t) - 1 - j))
      = (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by simp only [XM, cK, ca]; ring
  have hx2 : XM t r e j + ca (t + r) e * cK t r e ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
    linarith only [hw, mul_nonneg hC.le (mul_nonneg hV.le (by linarith only [hjw] : (0 : ℝ) ≤ (t + r + t) - 1 - j))]
  have hx1 : XM t r e j ≤ XM t r e j + ca (t + r) e * cK t r e :=
    le_add_of_nonneg_right (mul_nonneg (hapos hu he0).le hK0)
  have kU : (t + r + e) * lvl t r e (J + 1) - (t + r) * ((t + r + e) ^ 2 * (t + r) * (t + r + e + t))
      = (t + r + e) ^ 2 * (t + r) * ((t + r + e) - ρ) := by
    simp only [lvl]; linear_combination (-((t + r + e) ^ 2 * (t + r))) * hJ
  have kUp : 0 ≤ (t + r + e) * lvl t r e (J + 1) - (t + r) * ((t + r + e) ^ 2 * (t + r) * (t + r + e + t)) := by
    rw [kU]; exact mul_nonneg (mul_nonneg hC.le hu.le) (by linarith only [hρv])
  have hl : lvl t r e (J + 1) ≤ lvl t r e j := lvl_mono ht hr he hJj
  have hVl : (t + r + e) * lvl t r e (J + 1) ≤ (t + r + e) * lvl t r e j := mul_le_mul_of_nonneg_left hl hV.le
  have kM2 : (t + r) * (XM t r e j - (t + r + e) * (t + r + e) ^ 2) - (t + r + e) * lvl t r e j
      = -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) := by
    simp only [lvl, XM]; ring
  have kM3 : (t + r) * XM t r e j - (t + r + e) * lvl t r e (j + 1)
      = -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t)) := by
    simp only [lvl, XM]; ring
  have k4 := lvl_succ t r e j
  rcases hq with (h | h) | h
  · obtain ⟨m1, m2, m3, m4, m5⟩ := mem_TB' hu he0 hV.le h
    simp only [ca] at m4 m5
    refine ⟨m3, by rw [k4]; linarith only [m4], ?_, ?_, by linarith only [m2, hx1, hx2]⟩
    · have := box_N hu.le hV.le (m2.trans (hx1.trans hx2)) m3
      linarith only [this, kUp, hVl]
    · have := diag_M hV m5
      linarith only [this, kM2]
  · obtain ⟨m1, m2, m3, m4⟩ := h
    refine ⟨m3, m4, ?_, ?_, by linarith only [m2, hx2]⟩
    · have := box_N hu.le hV.le (m2.trans hx2) m3
      linarith only [this, kUp, hVl]
    · have := box_M hu.le hV.le m1 m4
      linarith only [this, kM3]
  · obtain ⟨m1, m2, m3, m4⟩ := mem_OR h
    refine ⟨m3, m4, ?_, ?_, m2⟩
    · have := box_N hu.le hV.le m2 m3
      linarith only [this, kUp, hVl]
    · have := box_M hu.le hV.le (hx1.trans m1) m4
      linarith only [this, kM3]

set_option maxHeartbeats 1000000 in
/-- the triangle on top -/
theorem STOP_bounds {t r e : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) (he : 1 ≤ e) {q : ℝ × ℝ} (hq : q ∈ STOP t r e) :
    lvl t r e (t + r + t) ≤ q.2 ∧ q.2 ≤ (t + r + e) ^ 2 * (t + r + e) * (t + r + e + t) ∧
      0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧ 0 ≤ (t + r + e) * q.1 - (t + r) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
  have hu : 0 < t + r := by linarith
  have he0 : 0 < e := by linarith
  have hV : 0 < t + r + e := by linarith
  have hC : 0 < (t + r + e) ^ 2 := by positivity
  have hK0 : 0 ≤ cK t r e := by simp only [cK]; positivity
  obtain ⟨m1, m2, m3, m4, m5⟩ := mem_TA hu he0 hK0 hq
  simp only [ca] at m1 m2 m5
  have kT1 : lvl t r e (t + r + t) + cK t r e * (t + r + e) ^ 2
      = (t + r + e) ^ 2 * (t + r + e) * (t + r + e + t) := by simp only [lvl, cK]; ring
  have kT2 : (t + r) * (t + r + e) * (t + r) * (t + r + t) + cK t r e * ((t + r) * (t + r + e))
      = (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by simp only [cK]; ring
  have kT3 : (t + r + e) * lvl t r e (t + r + t) - (t + r) * ((t + r + e) ^ 2 * (t + r) * (t + r + e + t))
      = (t + r + e) ^ 2 * (t + r) * (e * t) := by simp only [lvl]; ring
  have kT3p : 0 ≤ (t + r + e) ^ 2 * (t + r) * (e * t) := by positivity
  have kT4 : (t + r + e) * ((t + r) * (t + r + e) * (t + r) * (t + r + t)) - (t + r) * lvl t r e (t + r + t) = 0 := by
    simp only [lvl]; ring
  refine ⟨m3, by linarith only [m4, kT1], ?_, ?_, by linarith only [m2, kT2]⟩
  · have := box_N hu.le hV.le (show q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) by linarith only [m2, kT2]) m3
    linarith only [this, kT3, kT3p]
  · have := diag_L hV m5
    linarith only [this, kT4]

/-! ## The tilings of the strips -/
section tilings
variable {t r e : ℝ} (hu : 0 < t + r) (he : 0 < e)
include hu he

theorem rt_SL (j : ℝ) (un vn qn : ℕ) (hun : 0 < un) (hvn : 0 < vn) (eu : t + r = un) (ev : t + r + e = vn)
    (eq : qL t r e j = qn) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' SL t r e j) (ModC hu he)
      (un * un + 2 * (vn + qn) * un + 2 * qn * vn + vn * vn)) := by
  have hA := hapos hu he
  have hC := hc2 hu he
  have hV := hvpos hu he
  have hq0 : (0 : ℝ) ≤ qL t r e j := by rw [eq]; exact Nat.cast_nonneg _
  have hx3 : (t + r + e) ^ 2 * (t + r + e) * j
      = XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j) + (t + r + e) ^ 2 * (qn : ℝ) := by
    rw [← eq]; simp only [XL, qL, ca]; ring
  have R1 := rtTA hu he (XL t r e j - (t + r) * ca (t + r) e) (lvl t r e j) (t + r) un hun eu
  have R2 := rtRA hu he (XL t r e j) (XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j)) (lvl t r e j)
    (lvl t r e (j + 1)) (vn + qn) un (by omega) hun (by rw [ev, eq, Nat.cast_add])
    (by rw [lvl_succ, ← eu])
  have R3 := rtOC hu he (XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j))
    ((t + r + e) ^ 2 * (t + r + e) * j) (lvl t r e j) (lvl t r e (j + 1)) qn vn hvn hx3
    (by rw [lvl_succ, ← ev]; simp only [ca]; ring)
  have R4 := rtTB hu he ((t + r + e) ^ 2 * (t + r + e) * j) (lvl t r e j) (t + r + e) vn hvn ev
  refine chain4 (hφβ hu he) (XL t r e j) (XL t r e j + ca (t + r) e * ((t + r + e) + qL t r e j))
    ((t + r + e) ^ 2 * (t + r + e) * j) (le_add_of_nonneg_right (mul_nonneg hA.le (by linarith)))
    (by rw [hx3]; exact le_add_of_nonneg_right (mul_nonneg hC.le (Nat.cast_nonneg _))) R1 R2 R3 R4
    (fun q hq => by have := (mem_TA hu he hu.le hq).2.1; linarith) (fun q hq => hq.1) (fun q hq => hq.2.1)
    (fun q hq => (mem_OR hq).1) (fun q hq => (mem_OR hq).2.1) (fun q hq => (mem_TB hu he hV.le hq).1)

theorem rt_SM (j : ℝ) (un vn qn : ℕ) (hun : 0 < un) (hvn : 0 < vn) (eu : t + r = un) (ev : t + r + e = vn)
    (eq : qS t r e = qn) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' SM t r e j) (ModC hu he)
      (vn * vn + 2 * (vn + qn) * un + 2 * qn * vn + vn * vn)) := by
  have hA := hapos hu he
  have hC := hc2 hu he
  have hV := hvpos hu he
  have hq0 : (0 : ℝ) ≤ qS t r e := by rw [eq]; exact Nat.cast_nonneg _
  have hx3 : (t + r + e) ^ 2 * (t + r + e) * j
      = XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e) + (t + r + e) ^ 2 * (qn : ℝ) := by
    rw [← eq]; simp only [XM, qS, ca]; ring
  have R1 := rtTB' hu he (XM t r e j) (lvl t r e j) (t + r + e) vn hvn ev
  have R2 := rtRA hu he (XM t r e j) (XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e)) (lvl t r e j)
    (lvl t r e (j + 1)) (vn + qn) un (by omega) hun (by rw [ev, eq, Nat.cast_add])
    (by rw [lvl_succ, ← eu])
  have R3 := rtOC hu he (XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e))
    ((t + r + e) ^ 2 * (t + r + e) * j) (lvl t r e j) (lvl t r e (j + 1)) qn vn hvn hx3
    (by rw [lvl_succ, ← ev]; simp only [ca]; ring)
  have R4 := rtTB hu he ((t + r + e) ^ 2 * (t + r + e) * j) (lvl t r e j) (t + r + e) vn hvn ev
  refine chain4 (hφβ hu he) (XM t r e j) (XM t r e j + ca (t + r) e * ((t + r + e) + qS t r e))
    ((t + r + e) ^ 2 * (t + r + e) * j) (le_add_of_nonneg_right (mul_nonneg hA.le (by linarith)))
    (by rw [hx3]; exact le_add_of_nonneg_right (mul_nonneg hC.le (Nat.cast_nonneg _))) R1 R2 R3 R4
    (fun q hq => (mem_TB' hu he hV.le hq).2.1) (fun q hq => hq.1) (fun q hq => hq.2.1)
    (fun q hq => (mem_OR hq).1) (fun q hq => (mem_OR hq).2.1) (fun q hq => (mem_TB hu he hV.le hq).1)

theorem rt_SK (J ρ : ℝ) (un vn qn ρn dn : ℕ) (hun : 0 < un) (hvn : 0 < vn) (hρn : 0 < ρn) (hdn : 0 < dn)
    (eu : t + r = un) (ev : t + r + e = vn) (eq : qS t r e = qn) (eρ : ρ = ρn) (ed : t + r + e = ρ + dn) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' SK t r e J ρ) (ModC hu he)
      (vn * vn + 2 * (vn + qn) * un + 2 * qn * vn + (ρn * ρn + 2 * ρn * dn))) := by
  have hA := hapos hu he
  have hC := hc2 hu he
  have hV := hvpos hu he
  have hρ0 : (0 : ℝ) ≤ ρ := by rw [eρ]; exact Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ qS t r e := by rw [eq]; exact Nat.cast_nonneg _
  have hx3 : (t + r + e) ^ 2 * (t + r + e) * J
      = XM t r e J + ca (t + r) e * ((t + r + e) + qS t r e) + (t + r + e) ^ 2 * (qn : ℝ) := by
    rw [← eq]; simp only [XM, qS, ca]; ring
  have R1 := rtTB' hu he (XM t r e J) (lvl t r e J) (t + r + e) vn hvn ev
  have R2 := rtRA hu he (XM t r e J) (XM t r e J + ca (t + r) e * ((t + r + e) + qS t r e)) (lvl t r e J)
    (lvl t r e (J + 1)) (vn + qn) un (by omega) hun (by rw [ev, eq, Nat.cast_add])
    (by rw [lvl_succ, ← eu])
  have R3 := rtOC hu he (XM t r e J + ca (t + r) e * ((t + r + e) + qS t r e))
    ((t + r + e) ^ 2 * (t + r + e) * J) (lvl t r e J) (lvl t r e (J + 1)) qn vn hvn hx3
    (by rw [lvl_succ, ← ev]; simp only [ca]; ring)
  have R4a := rtTB hu he ((t + r + e) ^ 2 * (t + r + e) * J) (lvl t r e J) ρ ρn hρn eρ
  have R4b := rtRC hu he ((t + r + e) ^ 2 * (t + r + e) * J)
    ((t + r + e) ^ 2 * (t + r + e) * J + (t + r + e) ^ 2 * ρ) (lvl t r e J + ρ * ca (t + r) e)
    (lvl t r e (J + 1)) ρn dn hρn hdn (by rw [eρ])
    (by rw [lvl_succ, show (dn : ℝ) = t + r + e - ρ by linarith]; simp only [ca]; ring)
  have R4 := unionF (hφβ hu he) R4a R4b (interior_disj_snd (lvl t r e J + ρ * ca (t + r) e)
    (fun q hq => (mem_TB hu he hρ0 hq).2.2.2.1) (fun q hq => hq.2.2.1))
  refine chain4 (hφβ hu he) (XM t r e J) (XM t r e J + ca (t + r) e * ((t + r + e) + qS t r e))
    ((t + r + e) ^ 2 * (t + r + e) * J) (le_add_of_nonneg_right (mul_nonneg hA.le (by linarith)))
    (by rw [hx3]; exact le_add_of_nonneg_right (mul_nonneg hC.le (Nat.cast_nonneg _))) R1 R2 R3 R4
    (fun q hq => (mem_TB' hu he hV.le hq).2.1) (fun q hq => hq.1) (fun q hq => hq.2.1)
    (fun q hq => (mem_OR hq).1) (fun q hq => (mem_OR hq).2.1) ?_
  rintro q (hq | hq)
  · exact (mem_TB hu he hρ0 hq).1
  · exact hq.1

theorem rt_SU (j : ℝ) (un vn Kn yn : ℕ) (hun : 0 < un) (hvn : 0 < vn) (hKn : 0 < Kn) (eu : t + r = un)
    (ev : t + r + e = vn) (eK : cK t r e = Kn)
    (ey : (t + r + e) ^ 2 * (t + r) * (t + r + e + t)
      = XM t r e j + ca (t + r) e * cK t r e + (t + r + e) ^ 2 * (yn : ℝ)) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' SU t r e j) (ModC hu he) (vn * vn + 2 * Kn * un + 2 * yn * vn)) := by
  have hA := hapos hu he
  have hC := hc2 hu he
  have hV := hvpos hu he
  have hK0 : (0 : ℝ) ≤ cK t r e := by rw [eK]; exact Nat.cast_nonneg _
  have R1 := rtTB' hu he (XM t r e j) (lvl t r e j) (t + r + e) vn hvn ev
  have R2 := rtRA hu he (XM t r e j) (XM t r e j + ca (t + r) e * cK t r e) (lvl t r e j)
    (lvl t r e (j + 1)) Kn un hKn hun (by rw [eK]) (by rw [lvl_succ, ← eu])
  have R3 := rtOC hu he (XM t r e j + ca (t + r) e * cK t r e)
    ((t + r + e) ^ 2 * (t + r) * (t + r + e + t)) (lvl t r e j) (lvl t r e (j + 1)) yn vn hvn ey
    (by rw [lvl_succ, ← ev]; simp only [ca]; ring)
  exact chain3 (hφβ hu he) (XM t r e j) (XM t r e j + ca (t + r) e * cK t r e)
    (le_add_of_nonneg_right (mul_nonneg hA.le hK0)) R1 R2 R3
    (fun q hq => (mem_TB' hu he hV.le hq).2.1) (fun q hq => hq.1) (fun q hq => hq.2.1)
    (fun q hq => (mem_OR hq).1)

theorem rt_STOP (Kn : ℕ) (hKn : 0 < Kn) (eK : cK t r e = Kn) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' STOP t r e) (ModC hu he) (Kn * Kn)) :=
  rtTA hu he (ca (t + r) e * (t + r) * (t + r + t)) (lvl t r e (t + r + t)) (cK t r e) Kn hKn eK

end tilings

end Erdos634.Draft.Residue

#print axioms Erdos634.Draft.Residue.SL_bounds
#print axioms Erdos634.Draft.Residue.SK_bounds
#print axioms Erdos634.Draft.Residue.SU_bounds
#print axioms Erdos634.Draft.Residue.rt_SK
