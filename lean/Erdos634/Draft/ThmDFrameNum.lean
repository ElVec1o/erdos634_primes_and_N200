import Mathlib.Tactic
import Erdos634.Draft.ThmDFrame

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (5)): the numbers of the frame of `T(g)`

For the isosceles target `T(g)` (legs `G u b`, base `G v b`, `b = v² - u²`, `rt = √(4u² - v²)`) in the frame `Q = (0,0)`, `B = (L,0)`, `A = (ax, ay)`:
* S1 (`Q` an `α`-corner, `B` the apex): `ax = G b v²/(2u)`;
* S2 (`Q` the apex, `B` an `α`-corner): `ax = G b (2u² - v²)/(2u)`;
and `ay = G b v rt/(2u)` in both.  The side lengths, the ray data, the apex wedge inequalities and the three corner angles are proved
(`nums_S1`, `nums_S2`).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.MarchKillsFan

theorem rt_sq {u v : ℝ} (hu : 0 < u) (hv : v < 2 * u) (hv0 : 0 < v) : rtT u v ^ 2 = 4 * u ^ 2 - v ^ 2 :=
  rtT_sq hu hv hv0

/-- the SSS computation of a corner angle of the frame triangle -/
theorem Tg_angle_Q {L ax ay d₁ d₂ θ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (hd₂0 : 0 < d₂) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hcos : Real.cos θ = (L ^ 2 + d₂ ^ 2 - d₁ ^ 2) / (2 * L * d₂)) :
    cornerAngle ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 2) = θ := by
  refine cornerAngle_eq_of_cosT (a := L) (b := d₂) (d := d₁) ?_ ?_ ?_ hL hd₂0 hθ0 hθπ hcos
  · show dist (mkPt L 0) (mkPt 0 0) = L
    rw [dist_comm]
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  · show dist (mkPt ax ay) (mkPt 0 0) = d₂
    exact hd₂
  · exact hd₁

theorem Tg_angle_B {L ax ay d₁ d₂ θ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (hd₁0 : 0 < d₁) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hcos : Real.cos θ = (d₁ ^ 2 + L ^ 2 - d₂ ^ 2) / (2 * d₁ * L)) :
    cornerAngle ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 0) = θ := by
  refine cornerAngle_eq_of_cosT (a := d₁) (b := L) (d := d₂) ?_ ?_ ?_ hd₁0 hL hθ0 hθπ hcos
  · show dist (mkPt ax ay) (mkPt L 0) = d₁
    rw [dist_comm]; exact hd₁
  · show dist (mkPt 0 0) (mkPt L 0) = L
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  · show dist (mkPt ax ay) (mkPt 0 0) = d₂
    exact hd₂

theorem Tg_angle_A {L ax ay d₁ d₂ θ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (hd₁0 : 0 < d₁) (hd₂0 : 0 < d₂) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hcos : Real.cos θ = (d₂ ^ 2 + d₁ ^ 2 - L ^ 2) / (2 * d₂ * d₁)) :
    cornerAngle ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 1) = θ := by
  refine cornerAngle_eq_of_cosT (a := d₂) (b := d₁) (d := L) ?_ ?_ ?_ hd₂0 hd₁0 hθ0 hθπ hcos
  · show dist (mkPt 0 0) (mkPt ax ay) = d₂
    rw [dist_comm]; exact hd₂
  · show dist (mkPt L 0) (mkPt ax ay) = d₁
    exact hd₁
  · show dist (mkPt 0 0) (mkPt L 0) = L
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this

theorem cos_apex {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) :
    Real.cos (Real.pi - 2 * alphaT u v) = 1 - v ^ 2 / (2 * u ^ 2) := by
  rw [Real.cos_pi_sub, Real.cos_two_mul, cos_alphaT hu huv hv]
  field_simp
  ring

theorem apex_angle_range {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) :
    0 ≤ Real.pi - 2 * alphaT u v ∧ Real.pi - 2 * alphaT u v ≤ Real.pi := by
  have h1 := alphaT_pos hu hv (by linarith)
  have h2 := alphaT_le_half_pi hu (show 0 < v by linarith)
  constructor <;> linarith

section S1

variable (u v : ℕ) (G : ℝ)

/-- the numbers of the frame, S1 -/
noncomputable def bR : ℝ := (v : ℝ) ^ 2 - (u : ℝ) ^ 2

theorem nums_S1 (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hG : 1 ≤ G) :
    let b : ℝ := (v : ℝ) ^ 2 - (u : ℝ) ^ 2
    let L : ℝ := G * u * b
    let ax : ℝ := G * b * (v : ℝ) ^ 2 / (2 * u)
    let ay : ℝ := G * b * v * rtT (u : ℝ) (v : ℝ) / (2 * u)
    ∃ (hL : 0 < L) (hay : 0 < ay), dist (mkPt L 0) (mkPt ax ay) = G * u * b ∧
      dist (mkPt ax ay) (mkPt 0 0) = G * v * b ∧
      2 * (u : ℝ) * ax = v * (G * v * b) ∧ ax ^ 2 + ay ^ 2 = (G * v * b) ^ 2 ∧ (v : ℝ) * b ≤ G * v * b ∧
      0 < ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - (L - ax) * hhT (u : ℝ) (v : ℝ) ∧
      cornerAngle ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 2) =
        alphaT (u : ℝ) (v : ℝ) ∧
      cornerAngle ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 0) =
        Real.pi - 2 * alphaT (u : ℝ) (v : ℝ) ∧
      cornerAngle ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 1) =
        alphaT (u : ℝ) (v : ℝ) := by
  intro b L ax ay
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hvR : (v : ℝ) < 2 * u := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have hb : 0 < b := by simp only [b]; nlinarith
  have hG0 : 0 < G := by linarith
  have hrt0 : 0 < rtT (u : ℝ) (v : ℝ) := rtT_pos hu0 hvR hv0
  have hrt : rtT (u : ℝ) (v : ℝ) ^ 2 = 4 * (u : ℝ) ^ 2 - (v : ℝ) ^ 2 := rtT_sq hu0 hvR hv0
  have hL : 0 < L := by simp only [L]; positivity
  have hay : 0 < ay := by simp only [ay]; positivity
  have hay2 : ay ^ 2 = (G * b * v) ^ 2 * (4 * (u : ℝ) ^ 2 - (v : ℝ) ^ 2) / (4 * (u : ℝ) ^ 2) := by
    simp only [ay]
    rw [div_pow, mul_pow, hrt]
    ring
  have hd1 : dist (mkPt L 0) (mkPt ax ay) = G * u * b := by
    apply dist_eq_of_sq_eq _ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, show (0 - ay) ^ 2 = ay ^ 2 by ring, hay2]
    simp only [L, ax]
    field_simp
    ring
  have hd2 : dist (mkPt ax ay) (mkPt 0 0) = G * v * b := by
    apply dist_eq_of_sq_eq _ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, show (ay - 0) ^ 2 = ay ^ 2 by ring, hay2]
    simp only [ax]
    field_simp
    ring
  have hax : 2 * (u : ℝ) * ax = v * (G * v * b) := by
    simp only [ax]; field_simp
  have hsq : ax ^ 2 + ay ^ 2 = (G * v * b) ^ 2 := by
    rw [hay2]; simp only [ax]; field_simp; ring
  have hbig : (v : ℝ) * b ≤ G * v * b := by nlinarith [mul_pos hv0 hb]
  have hwedge : 0 < ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - (L - ax) * hhT (u : ℝ) (v : ℝ) := by
    have : ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - (L - ax) * hhT (u : ℝ) (v : ℝ) =
        G * b ^ 3 * rtT (u : ℝ) (v : ℝ) / (2 * (u : ℝ) ^ 2) := by
      simp only [L, ax, ay, uuT, hhT, b]
      field_simp
      ring
    rw [this]; positivity
  have hα0 := alphaT_pos hu0 hvR hv0
  have hαh := alphaT_le_half_pi hu0 hv0
  have hcosα := cos_alphaT hu0 huvR hvR
  have hd10 : 0 < G * u * b := by positivity
  have hd20 : 0 < G * v * b := by positivity
  refine ⟨hL, hay, hd1, hd2, hax, hsq, hbig, hwedge, ?_, ?_, ?_⟩
  · refine Tg_angle_Q hL hay hd1 hd2 hd20 hα0.le (by linarith [Real.pi_pos]) ?_
    rw [hcosα]; simp only [L]; field_simp; ring
  · obtain ⟨h0, h1⟩ := apex_angle_range hu0 huvR hvR
    refine Tg_angle_B hL hay hd1 hd2 hd10 h0 h1 ?_
    rw [cos_apex hu0 huvR hvR]; simp only [L]; field_simp; ring
  · refine Tg_angle_A hL hay hd1 hd2 hd10 hd20 hα0.le (by linarith [Real.pi_pos]) ?_
    rw [hcosα]; simp only [L]; field_simp; ring

end S1

section S2

variable (u v : ℕ) (G : ℝ)

theorem nums_S2 (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hG : 1 ≤ G) :
    let b : ℝ := (v : ℝ) ^ 2 - (u : ℝ) ^ 2
    let L : ℝ := G * u * b
    let ax : ℝ := G * b * (2 * (u : ℝ) ^ 2 - (v : ℝ) ^ 2) / (2 * u)
    let ay : ℝ := G * b * v * rtT (u : ℝ) (v : ℝ) / (2 * u)
    ∃ (hL : 0 < L) (hay : 0 < ay), dist (mkPt L 0) (mkPt ax ay) = G * v * b ∧
      dist (mkPt ax ay) (mkPt 0 0) = G * u * b ∧
      2 * (u : ℝ) * (L - ax) = v * (G * v * b) ∧ (L - ax) ^ 2 + ay ^ 2 = (G * v * b) ^ 2 ∧ (v : ℝ) * b ≤ G * v * b ∧
      0 < ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - ax * hhT (u : ℝ) (v : ℝ) ∧
      cornerAngle ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 2) =
        Real.pi - 2 * alphaT (u : ℝ) (v : ℝ) ∧
      cornerAngle ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 0) =
        alphaT (u : ℝ) (v : ℝ) ∧
      cornerAngle ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 1) =
        alphaT (u : ℝ) (v : ℝ) := by
  intro b L ax ay
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hvR : (v : ℝ) < 2 * u := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have hb : 0 < b := by simp only [b]; nlinarith
  have hG0 : 0 < G := by linarith
  have hrt0 : 0 < rtT (u : ℝ) (v : ℝ) := rtT_pos hu0 hvR hv0
  have hrt : rtT (u : ℝ) (v : ℝ) ^ 2 = 4 * (u : ℝ) ^ 2 - (v : ℝ) ^ 2 := rtT_sq hu0 hvR hv0
  have hL : 0 < L := by simp only [L]; positivity
  have hay : 0 < ay := by simp only [ay]; positivity
  have hay2 : ay ^ 2 = (G * b * v) ^ 2 * (4 * (u : ℝ) ^ 2 - (v : ℝ) ^ 2) / (4 * (u : ℝ) ^ 2) := by
    simp only [ay]
    rw [div_pow, mul_pow, hrt]
    ring
  have hd1 : dist (mkPt L 0) (mkPt ax ay) = G * v * b := by
    apply dist_eq_of_sq_eq _ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, show (0 - ay) ^ 2 = ay ^ 2 by ring, hay2]
    simp only [L, ax]
    field_simp
    ring
  have hd2 : dist (mkPt ax ay) (mkPt 0 0) = G * u * b := by
    apply dist_eq_of_sq_eq _ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, show (ay - 0) ^ 2 = ay ^ 2 by ring, hay2]
    simp only [ax]
    field_simp
    ring
  have hax : 2 * (u : ℝ) * (L - ax) = v * (G * v * b) := by
    simp only [L, ax]; field_simp; ring
  have hsq : (L - ax) ^ 2 + ay ^ 2 = (G * v * b) ^ 2 := by
    rw [hay2]; simp only [L, ax]; field_simp; ring
  have hbig : (v : ℝ) * b ≤ G * v * b := by nlinarith [mul_pos hv0 hb]
  have hwedge : 0 < ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - ax * hhT (u : ℝ) (v : ℝ) := by
    have : ay * ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) - ax * hhT (u : ℝ) (v : ℝ) =
        G * b ^ 3 * rtT (u : ℝ) (v : ℝ) / (2 * (u : ℝ) ^ 2) := by
      simp only [ax, ay, uuT, hhT, b]
      field_simp
      ring
    rw [this]; positivity
  have hα0 := alphaT_pos hu0 hvR hv0
  have hαh := alphaT_le_half_pi hu0 hv0
  have hcosα := cos_alphaT hu0 huvR hvR
  have hd10 : 0 < G * v * b := by positivity
  have hd20 : 0 < G * u * b := by positivity
  refine ⟨hL, hay, hd1, hd2, hax, hsq, hbig, hwedge, ?_, ?_, ?_⟩
  · obtain ⟨h0, h1⟩ := apex_angle_range hu0 huvR hvR
    refine Tg_angle_Q hL hay hd1 hd2 hd20 h0 h1 ?_
    rw [cos_apex hu0 huvR hvR]; simp only [L]; field_simp; ring
  · refine Tg_angle_B hL hay hd1 hd2 hd10 hα0.le (by linarith [Real.pi_pos]) ?_
    rw [hcosα]; simp only [L]; field_simp; ring
  · refine Tg_angle_A hL hay hd1 hd2 hd10 hd20 hα0.le (by linarith [Real.pi_pos]) ?_
    rw [hcosα]; simp only [L]; field_simp; ring

end S2

#print axioms nums_S1
#print axioms nums_S2
#print axioms Tg_angle_Q
#print axioms cos_apex
end Erdos634.Draft.ThmDRun
