import Erdos634.RouteOneCrossing

namespace Erdos634.Draft.RouteOneCrossingWrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
open Erdos634.RouteOneCrossing

theorem wrap_flank_of_no_crossing_of_congruent {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (g : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3))
    (hg : ∀ k, g (D.target.pts k) = (baseBetaTarget e f (by linarith) hef).pts (σ k))
    (j : Fin N) (mj : Fin 3)
    (hjseg : openSegment ℝ (mkPt (escapeV e f).1 (escapeV e f).2)
        (mkPt (sideA e f).1 (sideA e f).2)
      ⊆ openSegment ℝ (g ((D.tile j).pts (mj + 1))) (g ((D.tile j).pts (mj + 2))))
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier →
      0 ≤ (g q - mkPt (escapeV e f).1 (escapeV e f).2) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier →
      (g q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ≤ 0)
    (hcross : ∀ k : Fin N,
      ¬ ((∃ a, yHeight (g ((D.tile k).pts a)) < (mkPt (escapeV e f).1 (escapeV e f).2) 1) ∧
         (∃ b, (mkPt (escapeV e f).1 (escapeV e f).2) 1 < yHeight (g ((D.tile k).pts b))))) :
    ∃ (i : Fin N) (m : Fin 3),
      g ((D.tile i).pts m) = mkPt (escapeV e f).1 (escapeV e f).2 ∧
      ((g ((D.tile i).pts (m + 1)) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < (g ((D.tile i).pts (m + 1)) - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∨
        (g ((D.tile i).pts (m + 2)) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < (g ((D.tile i).pts (m + 2)) - mkPt (escapeV e f).1 (escapeV e f).2) 0) :=
  flank_of_no_crossing_of_congruent D he hef hf2 g σ hg j mj hjseg habovej hjleft hcross

example : True := trivial
#print axioms wrap_flank_of_no_crossing_of_congruent

end Erdos634.Draft.RouteOneCrossingWrap
