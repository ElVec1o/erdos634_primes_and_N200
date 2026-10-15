import Erdos634.TileAt

namespace Erdos634.Draft.TileAtWrap
open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.TilePlacement

theorem wrap_congruentDissection_hcorners {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ) :
    ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({α, β, γ} : Finset ℝ) :=
  congruentDissection_hcorners D α β γ hα' hβ' hγ'

example : True := trivial
#print axioms wrap_congruentDissection_hcorners

end Erdos634.Draft.TileAtWrap
