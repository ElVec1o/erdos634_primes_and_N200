import Erdos634.WallChain

namespace Erdos634.Draft.WallChainWrap
open Erdos634.Geometry MeasureTheory

theorem wrap_Dissection_edge_two_sided {N : ℕ} (D : Dissection N) (j : Fin N) (k : Fin 3)
    (hint : openSegment ℝ ((D.tile j).pts k) ((D.tile j).pts (k + 1))
      ⊆ interior D.target.carrier) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ y ∈ (D.tile j).edge k, f y = c) ∧
      (∑ e ∈ D.lineChain f c,
          (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
            ((D.tile e.1).edge e.2 ∩ (D.tile j).edge k)
        = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile j).edge k))
      ∧ (∑ e ∈ D.lineChain (-f) (-c),
          (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
            ((D.tile e.1).edge e.2 ∩ (D.tile j).edge k)
        = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile j).edge k)) :=
  Dissection.edge_two_sided D j k hint

example : True := trivial
#print axioms wrap_Dissection_edge_two_sided

end Erdos634.Draft.WallChainWrap
