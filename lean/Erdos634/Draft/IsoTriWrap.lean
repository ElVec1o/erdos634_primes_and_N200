import Erdos634.IsoTri

namespace Erdos634.Draft.IsoTriWrap

open Erdos634.IsoTri Erdos634.Geometry

theorem it_dist01 (L h : ℝ) (hL : 0 ≤ L) : dist (isoPts L h 0) (isoPts L h 1) = L :=
  dist01 L h hL

theorem it_not_collinear (L h : ℝ) (hL : L ≠ 0) (hh : h ≠ 0) :
    ¬ Collinear ℝ {isoPts L h 0, isoPts L h 1, isoPts L h 2} :=
  not_collinear L h hL hh

example : it_dist01 1 1 (by norm_num) = dist01 1 1 (by norm_num) := rfl

#print axioms it_dist01
#print axioms it_not_collinear

end Erdos634.Draft.IsoTriWrap
