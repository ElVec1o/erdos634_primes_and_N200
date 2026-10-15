import Erdos634.AngleSumScope

/-!
# Angle sum telescoping (mod 2π half): wrapper

Re-exports results of `AngleSumScope`:
- `three_ray_telescope`: three rays around a point telescope to 0 in ℝ/2πℤ
- `four_ray_telescope`: four rays around a point telescope to 0

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AngleSumScopeWrap

open Erdos634.AngleSumScope EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

theorem ass_three_ray_telescope (p p₁ p₂ p₃ : P) (h₁ : p₁ ≠ p) (h₂ : p₂ ≠ p) (h₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 :=
  three_ray_telescope p p₁ p₂ p₃ h₁ h₂ h₃

theorem ass_four_ray_telescope (p p₁ p₂ p₃ p₄ : P)
    (h₁ : p₁ ≠ p) (h₂ : p₂ ≠ p) (h₃ : p₃ ≠ p) (h₄ : p₄ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₄ + ∡ p₄ p p₁ = 0 :=
  four_ray_telescope p p₁ p₂ p₃ p₄ h₁ h₂ h₃ h₄

-- Non-vacuity: three_ray_telescope holds universally
example (p p₁ p₂ p₃ : P) (h₁ : p₁ ≠ p) (h₂ : p₂ ≠ p) (h₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 := ass_three_ray_telescope p p₁ p₂ p₃ h₁ h₂ h₃

#print axioms ass_three_ray_telescope
#print axioms ass_four_ray_telescope

end Erdos634.Draft.AngleSumScopeWrap
