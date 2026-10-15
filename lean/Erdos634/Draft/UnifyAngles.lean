import Erdos634.AngleThreshold

/-!
# The three cosines of the tile `(ef, f² − e², f²)` at a general member

The obtuse-angle fact `cos γ = −e/2f < 0` is used at a
general member `(e, f)`; `AngleThreshold.cos_gamma_closed` is the case `e = 1`.  Here are the three
closed forms for real `0 < e < f`, by the law of cosines:

* `cos_alpha_general` : `cos α = (2f² − e²)/(2f²)`  (the corner facing `a = ef`);
* `cos_beta_general`  : `cos β = e(3f² − e²)/(2f³)` (the corner facing `b = f² − e²`);
* `cos_gamma_general` : `cos γ = −e/(2f)`           (the corner facing `c = f²`);
* `gamma_obtuse_general` : `π/2 < γ`, hence `π < 2γ`.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.UnifyAngles

open EuclideanGeometry Erdos634.Geometry Erdos634.AngleThreshold

/-- `cos γ = −e/(2f)`: the corner between the sides `a = ef` and `b = f² − e²`. -/
theorem cos_gamma_general (p q r : Plane) (e f : ℝ) (he : 0 < e) (hef : e < f)
    (ha : dist p q = e * f) (hb : dist r q = f ^ 2 - e ^ 2) (hc : dist p r = f ^ 2) :
    Real.cos (cornerAngle p q r) = -e / (2 * f) := by
  have hf0 : (0:ℝ) < f := lt_trans he hef
  have hb0 : (0:ℝ) < f ^ 2 - e ^ 2 := by nlinarith
  rw [cos_of_sides p q r (by rw [ha]; positivity) (by rw [hb]; exact ne_of_gt hb0), ha, hb, hc]
  field_simp
  ring

/-- `cos β = e(3f² − e²)/(2f³)`: the corner between the sides `a = ef` and `c = f²`. -/
theorem cos_beta_general (p q r : Plane) (e f : ℝ) (he : 0 < e) (hef : e < f)
    (ha : dist p q = e * f) (hc : dist r q = f ^ 2) (hb : dist p r = f ^ 2 - e ^ 2) :
    Real.cos (cornerAngle p q r) = e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3) := by
  have hf0 : (0:ℝ) < f := lt_trans he hef
  rw [cos_of_sides p q r (by rw [ha]; positivity) (by rw [hc]; positivity), ha, hc, hb]
  field_simp
  ring

/-- `cos α = (2f² − e²)/(2f²)`: the corner between the sides `b = f² − e²` and `c = f²`. -/
theorem cos_alpha_general (p q r : Plane) (e f : ℝ) (he : 0 < e) (hef : e < f)
    (hb : dist p q = f ^ 2 - e ^ 2) (hc : dist r q = f ^ 2) (ha : dist p r = e * f) :
    Real.cos (cornerAngle p q r) = (2 * f ^ 2 - e ^ 2) / (2 * f ^ 2) := by
  have hf0 : (0:ℝ) < f := lt_trans he hef
  have hb0 : (0:ℝ) < f ^ 2 - e ^ 2 := by nlinarith
  rw [cos_of_sides p q r (by rw [hb]; exact ne_of_gt hb0) (by rw [hc]; positivity), hb, hc, ha]
  field_simp
  ring

/-- `γ` is obtuse at every member: `π/2 < γ`, so `π < 2γ`. -/
theorem gamma_obtuse_general (p q r : Plane) (e f : ℝ) (he : 0 < e) (hef : e < f)
    (ha : dist p q = e * f) (hb : dist r q = f ^ 2 - e ^ 2) (hc : dist p r = f ^ 2) :
    Real.pi < 2 * cornerAngle p q r := by
  have hf0 : (0:ℝ) < f := lt_trans he hef
  have hcos := cos_gamma_general p q r e f he hef ha hb hc
  have hneg : Real.cos (cornerAngle p q r) < 0 := by
    rw [hcos]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  by_contra hnot
  have hle : cornerAngle p q r ≤ Real.pi / 2 := by linarith
  have h0 : 0 ≤ cornerAngle p q r := EuclideanGeometry.angle_nonneg _ _ _
  have := Real.cos_nonneg_of_mem_Icc
    (⟨by linarith [Real.pi_pos], hle⟩ : cornerAngle p q r ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
  linarith

end Erdos634.Draft.UnifyAngles
