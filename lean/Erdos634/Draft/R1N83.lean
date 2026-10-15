-- Concrete instance N = 83 of `R1Final.r1_no_tiling` at (e, f) = (5, 6): no CongruentDissection 83 has
-- target congruent to `baseBetaTarget 5 6` and model congruent to a triangle with sides (30, 11, 36).
import Erdos634.Draft.R1Final

namespace Erdos634.Draft.R1N83
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Draft.R1Final

theorem r1_n83 (D : CongruentDissection 83)
    (htgt : D.target.Congruent (baseBetaTarget ((5 : ℕ) : ℝ) 6 (by norm_num) (by norm_num)))
    (T : Tri) (h0 : sideOpp T 0 = 30) (h1 : sideOpp T 1 = 11) (h2 : sideOpp T 2 = 36)
    (hmod : D.model.Congruent T) : False :=
  r1_no_tiling (N := 83) D (e := 5) (f := 6) (by norm_num) (by norm_num) htgt T
    (by rw [h0]; norm_num) (by rw [h1]; norm_num) (by rw [h2]; norm_num) hmod
#print axioms r1_n83
end Erdos634.Draft.R1N83
