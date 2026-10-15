import Erdos634.TP_hilbert

namespace Erdos634.Draft.TP_hilbertWrap
open Erdos634.TPHilbert Erdos634.Geometry MeasureTheory Set

theorem wrap_lineChain_nondeg_covers_and_injOn {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ)
    (hf : f ≠ 0) (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    (hle : ∀ e ∈ D.lineChain f c, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c) :
    (⋃ e ∈ nondeg (D.lineChain f c)
        (fun e => min (Erdos634.LineParam.edgeParam D f c u v e).1
          (Erdos634.LineParam.edgeParam D f c u v e).2)
        (fun e => max (Erdos634.LineParam.edgeParam D f c u v e).1
          (Erdos634.LineParam.edgeParam D f c u v e).2),
        Icc (min (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2)
          (max (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2))
        = Icc (0:ℝ) 1
      ∧ InjOn (fun e => min (Erdos634.LineParam.edgeParam D f c u v e).1
          (Erdos634.LineParam.edgeParam D f c u v e).2)
        (nondeg (D.lineChain f c)
          (fun e => min (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2)
          (fun e => max (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2)) :=
  lineChain_nondeg_covers_and_injOn D f hf c u v huv hS hint hwall hle

example : True := trivial
#check @wrap_lineChain_nondeg_covers_and_injOn

end Erdos634.Draft.TP_hilbertWrap
