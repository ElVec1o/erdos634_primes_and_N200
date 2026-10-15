import Erdos634.NoRightAngle

namespace Erdos634.Draft.NoRightAngleWrap

open Erdos634.NoRightAngle Erdos634.Geometry Real

theorem nra_angles_ne_pi_div_two {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hγ : γ = 2 * α + β) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    α ≠ Real.pi / 2 ∧ β ≠ Real.pi / 2 ∧ γ ≠ Real.pi / 2 :=
  angles_ne_pi_div_two hrel hγ hirr

theorem nra_no_right_angle_of_congruent {T U : Tri} (h : T.Congruent U) {α β γ : ℝ}
    (hT : ∀ k : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
      ∈ ({α, β, γ} : Finset ℝ))
    (hα : α ≠ Real.pi / 2) (hβ : β ≠ Real.pi / 2) (hγ : γ ≠ Real.pi / 2) (j : Fin 3) :
    cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) ≠ Real.pi / 2 :=
  no_right_angle_of_congruent h hT hα hβ hγ j

theorem nra_no_piece_has_right_angle {T U : Tri} (h : T.Congruent U) {α β γ : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hγ : γ = 2 * α + β)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hT : ∀ k : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
      ∈ ({α, β, γ} : Finset ℝ)) (j : Fin 3) :
    cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) ≠ Real.pi / 2 :=
  no_piece_has_right_angle h hrel hγ hirr hT j

example : True := trivial

#print axioms nra_no_piece_has_right_angle

end Erdos634.Draft.NoRightAngleWrap
