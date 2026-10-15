import Erdos634.AngleThreshold

/-!
# `α` is the sharpest angle of the tile `(f, f² − 1, f²)`

Condition (P4) of the frontier invariant compares the corners of the uncovered region with the tile's own sharpest
angle, `α`.  The three cosines are `AngleThreshold.cos_alpha_closed`, `cos_beta_closed`,
`cos_gamma_closed`; that `α` is the sharpest of the three angles is the statement proved here.

* `alpha_sharpest` : in a triangle `P Q R` with `|QR| = f`, `|PR| = f² − 1`, `|PQ| = f²`, `f ≥ 2`,
  the angles satisfy `∠P < ∠Q < ∠R` (that is `α < β < γ`).

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.SharpestAngle

open EuclideanGeometry Erdos634.Geometry Erdos634.AngleThreshold

theorem alpha_sharpest (P Q R : Plane) (f : ℝ) (hf : 2 ≤ f)
    (ha : dist Q R = f) (hb : dist P R = f ^ 2 - 1) (hc : dist P Q = f ^ 2) :
    cornerAngle R P Q < cornerAngle R Q P ∧ cornerAngle R Q P < cornerAngle Q R P := by
  have hf1 : (1:ℝ) < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hA : Real.cos (cornerAngle R P Q) = (2 * f ^ 2 - 1) / (2 * f ^ 2) :=
    cos_alpha_closed R P Q f hf1 (by rw [dist_comm]; exact hb) (by rw [dist_comm]; exact hc)
      (by rw [dist_comm]; exact ha)
  have hB : Real.cos (cornerAngle R Q P) = (3 * f ^ 2 - 1) / (2 * f ^ 3) :=
    cos_beta_closed R Q P f hf1 (by rw [dist_comm]; exact ha) hc (by rw [dist_comm]; exact hb)
  have hG : Real.cos (cornerAngle Q R P) = -1 / (2 * f) :=
    cos_gamma_closed Q R P f hf1 ha hb (by rw [dist_comm]; exact hc)
  have hmem : ∀ X Y Z : Plane, cornerAngle X Y Z ∈ Set.Icc (0:ℝ) Real.pi := fun X Y Z =>
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hlt : ∀ x y : ℝ, x ∈ Set.Icc (0:ℝ) Real.pi → y ∈ Set.Icc (0:ℝ) Real.pi →
      Real.cos y < Real.cos x → x < y := by
    intro x y hx hy hcos
    by_contra hnot
    have hle : y ≤ x := not_lt.mp hnot
    have := Real.cos_le_cos_of_nonneg_of_le_pi hy.1 hx.2 hle
    linarith
  constructor
  · apply hlt _ _ (hmem R P Q) (hmem R Q P)
    rw [hA, hB, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) (by positivity : (0:ℝ) ≤ 2 * f ^ 2 + f + 1),
      pow_pos hf0 2, pow_pos hf0 3, pow_pos hf0 4]
  · apply hlt _ _ (hmem R Q P) (hmem Q R P)
    rw [hB, hG]
    have h1 : (0:ℝ) < (3 * f ^ 2 - 1) / (2 * f ^ 3) := by
      have : (0:ℝ) < 3 * f ^ 2 - 1 := by nlinarith
      positivity
    have h2 : -1 / (2 * f) < (0:ℝ) := by
      apply div_neg_of_neg_of_pos (by norm_num) (by positivity)
    linarith

end Erdos634.Draft.SharpestAngle
