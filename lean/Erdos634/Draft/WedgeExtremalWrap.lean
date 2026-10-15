import Erdos634.WedgeExtremal

namespace Erdos634.Draft.WedgeExtremalWrap
open Erdos634.WedgeExtremal Erdos634.Geometry

theorem wrap_corner_on_wedge_sides (o : Orientation ℝ Plane (Fin 2)) {A P Q u : Plane} {α φ ψ : ℝ}
    (hu : u ≠ 0) (hP : P - A ≠ 0) (hQ : Q - A ≠ 0) (hα : α < Real.pi)
    (hφ : (o.oangle u (P - A)).toReal = φ) (hψ : (o.oangle u (Q - A)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) α) (hψm : ψ ∈ Set.Icc (0:ℝ) α)
    (hcorner : cornerAngle P A Q = α) :
    (φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0) :=
  Dissection.corner_on_wedge_sides o hu hP hQ hα hφ hψ hφm hψm hcorner

example : True := trivial
#check @wrap_corner_on_wedge_sides

end Erdos634.Draft.WedgeExtremalWrap
