import Erdos634.JunctionWedge

namespace Erdos634.Draft.JunctionWedgeWrap
open Erdos634.Geometry
open Erdos634.JunctionWedge

theorem wrap_march_junction_real {N : ℕ} (D : Dissection N) (o : Orientation ℝ Plane (Fin 2))
    {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hβpos : 0 < β) (hαpos : 0 < α)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (iγ : Fin N) (hiγ : (D.tile iγ).localAngle v = γ)
    {P Q u : Plane} {φ ψ : ℝ}
    (hu : u ≠ 0) (hP : P - v ≠ 0) (hQ : Q - v ≠ 0)
    (hφ : (o.oangle u (P - v)).toReal = φ) (hψ : (o.oangle u (Q - v)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) α) (hψm : ψ ∈ Set.Icc (0:ℝ) α)
    (hcorner : cornerAngle P v Q = α) :
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0)
    ∧ ((φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0)) :=
  march_junction_real D o hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hβpos hαpos hv hnv hvals iγ hiγ hu hP hQ hφ hψ hφm hψm hcorner

example : True := trivial
#print axioms wrap_march_junction_real

end Erdos634.Draft.JunctionWedgeWrap
