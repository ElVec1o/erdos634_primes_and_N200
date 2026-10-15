import Erdos634.PickPointNode2

namespace Erdos634.Draft.PickPointNode2Wrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LemmaPNode2
open Erdos634.ThickBlockingLemmas

theorem wrap_node2_blocked_arcs_pick_d2 :
    0 < cross (w1t0.pts 2 - v2) (w1t0.pts 0 - v2) ∧
    0 < cross (w1t1.pts 1 - v2) (w1t1.pts 2 - v2) ∧
    (∃ k : ℝ, 0 < k ∧ w1t0.pts 0 - v2 = k • mkPt (-1) 0) ∧
    (∃ k : ℝ, 0 < k ∧ w1t1.pts 1 - v2 = k • mkPt 1 0) ∧
    w1t1.pts 2 - v2 = (5 : ℝ) • d2 ∧
    0 < cross d2 (w1t0.pts 2 - v2) :=
  Erdos634.PickPointNode2.node2_blocked_arcs_pick_d2

example : True := trivial
#print axioms wrap_node2_blocked_arcs_pick_d2

end Erdos634.Draft.PickPointNode2Wrap
