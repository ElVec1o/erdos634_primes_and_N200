import Mathlib.Tactic
import Erdos634.Draft.ThmDRowFrontier

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1)): the corner context from the normalised frame

In a `SetupT` frame (`Q = (0,0)`, `B = (L,0)`, apex `(ax, ay)`) whose corner at `Q` has `cos = v/(2u)` (`2u ax = v d2`, `ax² + ay² = d2²`,
`d2 = |QA|`), the lattice points `P_w = lpT u v 1 0 0 w` (`ε = 1`, `x = 0`) lie on the ray `QA` at distance `w b` from `Q` (`b = v² - u²`).
If `w < v` and `d2 > v b` then `P_w` is in the open side `QA`: a frontier point of the target, not a vertex, with `gA = 0`, `gB > 0`
(the hypotheses `hPf` of `lemmaK2_final`), and `P_w ∈ target`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

/-- `P_w = (w b / d2) • A` -/
theorem lp0w_ray {u v : ℝ} (hu : 0 < u) (hv0 : 0 < v) (hv : v < 2 * u) {ax ay d2 : ℝ} (hd2 : 0 < d2)
    (hax : 2 * u * ax = v * d2) (hay : 0 < ay) (hsq : ax ^ 2 + ay ^ 2 = d2 ^ 2) (w : ℝ) :
    lpT u v 1 0 0 w = mkPt ((w * (v ^ 2 - u ^ 2) / d2) * ax) ((w * (v ^ 2 - u ^ 2) / d2) * ay) := by
  have hrt := rtT_pos hu hv hv0
  have hrt2 := rtT_sq hu hv hv0
  have hu2 : (2 * u : ℝ) ≠ 0 := by positivity
  have hay' : ay = d2 * rtT u v / (2 * u) := by
    have h1 : (2 * u * ay) ^ 2 = (d2 * rtT u v) ^ 2 := by
      have : (2 * u * ax) ^ 2 = (v * d2) ^ 2 := by rw [hax]
      nlinarith [hsq, hrt2, this]
    have hpos : 0 < 2 * u * ay := by positivity
    have hpos2 : 0 < d2 * rtT u v := by positivity
    have := (sq_eq_sq₀ hpos.le hpos2.le).mp h1
    field_simp
    linarith
  have hax' : ax = v * d2 / (2 * u) := by field_simp; linarith
  unfold lpT
  apply mkPt_congr
  · have e : (0 : ℝ) + 1 * ((0 + w) * (u * v) - w * uuT u v) = w * (u * v - uuT u v) := by ring
    rw [e, hax']
    unfold uuT
    field_simp
    ring
  · unfold hhT
    rw [hay']
    field_simp

theorem lp0w_facts (S : SetupT D u v α β γ L ax ay) {d2 : ℝ} (hd2 : 0 < d2) (hax : 2 * (u : ℝ) * ax = (v : ℝ) * d2)
    (hsq : ax ^ 2 + ay ^ 2 = d2 ^ 2) (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ≤ d2)
    {w : ℝ} (hw1 : 1 ≤ w) (hwv : w < v) :
    lpT (u : ℝ) (v : ℝ) 1 0 0 w ∈ D.target.carrier ∧ lpT (u : ℝ) (v : ℝ) 1 0 0 w ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) 1 0 0 w ∉ Set.range D.target.pts ∧
      gA ax ay (lpT (u : ℝ) (v : ℝ) 1 0 0 w) = 0 ∧ 0 < gB L ax ay (lpT (u : ℝ) (v : ℝ) 1 0 0 w) ∧
      0 < (lpT (u : ℝ) (v : ℝ) 1 0 0 w) 1 := by
  have hu := S.u0
  have hb := S.b_pos
  have hay := S.hay
  have hL := S.hL
  set t : ℝ := w * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) / d2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hd2]
    nlinarith [S.uv', mul_pos hb (sub_pos.2 hwv), hbig]
  have hray := lp0w_ray hu S.v0 S.v2 hd2 hax hay hsq w
  rw [← ht] at hray
  have hmem : mkPt (t * ax) (t * ay) ∈ D.target.carrier := by
    rw [S.tgt]
    have hconv := Tri.convex (Tg L ax ay S.hL S.hay)
    have hA : mkPt ax ay ∈ (Tg L ax ay S.hL S.hay).carrier :=
      subset_convexHull ℝ _ ⟨2, (Tg_pts2 S.hL S.hay)⟩
    have hQ : mkPt 0 0 ∈ (Tg L ax ay S.hL S.hay).carrier :=
      subset_convexHull ℝ _ ⟨0, (Tg_pts0 S.hL S.hay)⟩
    have := hconv hA hQ ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    convert this using 1
    ext i
    fin_cases i <;> simp [mkPt]
  have hgA : gA ax ay (mkPt (t * ax) (t * ay)) = 0 := by rw [gA_mk]; ring
  have hgB : 0 < gB L ax ay (mkPt (t * ax) (t * ay)) := by
    rw [gB_mk]
    have : ay * (L - t * ax) - (L - ax) * (t * ay) = ay * L * (1 - t) := by ring
    rw [this]
    exact mul_pos (mul_pos hay hL) (by linarith)
  have hy : 0 < (mkPt (t * ax) (t * ay) : Plane) 1 := by rw [mkPt_one]; positivity
  rw [hray]
  refine ⟨hmem, S.frontier_gA0 hmem hgA, ?_, hgA, hgB, hy⟩
  rintro ⟨k, hk⟩
  rw [S.tgt] at hk
  have h1 := congrArg (fun p : Plane => p 1) hk
  have h0 := congrArg (fun p : Plane => p 0) hk
  simp only [mkPt_one, mkPt_zero] at h1 h0
  have hty : 0 < t * ay := by positivity
  fin_cases k
  · have e : (Tg L ax ay S.hL S.hay).pts 0 = mkPt 0 0 := Tg_pts0 _ _
    simp only [Fin.zero_eta, Fin.isValue] at h1
    rw [e, mkPt_one] at h1
    linarith
  · have e : (Tg L ax ay S.hL S.hay).pts 1 = mkPt L 0 := Tg_pts1 _ _
    simp only [Fin.mk_one, Fin.isValue] at h1
    rw [e, mkPt_one] at h1
    linarith
  · have e : (Tg L ax ay S.hL S.hay).pts 2 = mkPt ax ay := Tg_pts2 _ _
    simp only [Fin.reduceFinMk, Fin.isValue] at h1
    rw [e, mkPt_one] at h1
    nlinarith [mul_pos ht0 hay, sub_pos.2 ht1]

#print axioms lp0w_facts
end Erdos634.Draft.ThmDRun
