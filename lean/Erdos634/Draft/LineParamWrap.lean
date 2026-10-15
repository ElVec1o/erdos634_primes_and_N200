import Erdos634.LineParam
namespace Erdos634.Draft.LineParamWrap
open Erdos634.LineParam
open Erdos634.Geometry

theorem wrap_dist_lineMap_lineMap (u v : Plane) (s t : ℝ) :
    dist (AffineMap.lineMap u v s) (AffineMap.lineMap u v t) = |s - t| * dist u v :=
  Erdos634.LineParam.dist_lineMap_lineMap u v s t

theorem wrap_lineMap_injective_of_ne {u v : Plane} (huv : u ≠ v) :
    Function.Injective (AffineMap.lineMap u v : ℝ → Plane) :=
  lineMap_injective_of_ne huv

theorem wrap_lineMap_lineMap_comb (u v : Plane) (p q t : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap u v p) (AffineMap.lineMap u v q) t
      = AffineMap.lineMap u v (p + t * (q - p)) :=
  lineMap_lineMap_comb u v p q t

theorem wrap_isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) :=
  isCompact_segment x y

theorem wrap_lineChain_param_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain f c,
        (max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
          - min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
      = 1 :=
  lineChain_param_sum D f hf c u v huv hS hint hwall

example : True := trivial
#print axioms wrap_dist_lineMap_lineMap
end Erdos634.Draft.LineParamWrap
