import Erdos634.RouteOneBoundaryA

namespace Erdos634.Draft.RouteOneBoundaryAWrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
open Erdos634.RouteOneBoundaryA

theorem wrap_flank_at_route1uniform {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (htgt : D.target = baseBetaTarget e f (by linarith) hef)
    (j : Fin N) (mj : Fin 3)
    (hjseg : openSegment ℝ (mkPt (escapeV e f).1 (escapeV e f).2)
        (mkPt (sideA e f).1 (sideA e f).2)
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier →
      0 ≤ (q - mkPt (escapeV e f).1 (escapeV e f).2) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier →
      (q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧
        0 < (q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∧
        0 < (q - mkPt (escapeV e f).1 (escapeV e f).2) 1 ∧
        dist q (mkPt (escapeV e f).1 (escapeV e f).2) < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier →
        0 ≤ (q - mkPt (escapeV e f).1 (escapeV e f).2) 1) :
    ∃ (i : Fin N) (m : Fin 3),
      (D.tile i).pts m = mkPt (escapeV e f).1 (escapeV e f).2 ∧
      ((((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 0) ∨
       (((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 0)) :=
  flank_at_route1uniform D he hef hf2 htgt j mj hjseg habovej hjleft hwall

example : True := trivial
#print axioms wrap_flank_at_route1uniform

end Erdos634.Draft.RouteOneBoundaryAWrap
