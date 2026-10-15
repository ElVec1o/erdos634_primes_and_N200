import Erdos634.MarchFlank
namespace Erdos634.Draft.MarchFlankWrap
open Erdos634.MarchFlank
open Erdos634.Geometry Erdos634.TilePlacement

theorem wrap_endpoints_ne_apex : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j :=
  endpoints_ne_apex

theorem wrap_beta_or_gamma {α β γ θ : ℝ} (hmem : θ = α ∨ θ = β ∨ θ = γ) (hne : θ ≠ α) :
    θ = β ∨ θ = γ :=
  beta_or_gamma hmem hne

theorem wrap_flank_is_beta_or_gamma (T : Tri) (j : Fin 3) {α β γ : ℝ}
    (h1 : sideOpp T j < sideOpp T (j + 1)) (h2 : sideOpp T (j + 1) < sideOpp T (j + 2))
    (hapex : angleAt T j = α)
    (hmem1 : angleAt T (j + 1) = α ∨ angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
    (hmem2 : angleAt T (j + 2) = α ∨ angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) :
    (angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
      ∧ (angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) :=
  flank_is_beta_or_gamma T j h1 h2 hapex hmem1 hmem2

example : True := trivial
#print axioms wrap_endpoints_ne_apex
#print axioms wrap_flank_is_beta_or_gamma
end Erdos634.Draft.MarchFlankWrap
