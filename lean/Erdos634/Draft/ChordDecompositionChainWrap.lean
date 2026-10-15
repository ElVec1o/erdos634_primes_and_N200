import Erdos634.ChordDecompositionChain
namespace Erdos634.Draft.ChordDecompositionChainWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_decomposition_of_chain {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (hlo : ∃ i, f (D.target.pts i) < c) (hhi : ∃ j, c < f (D.target.pts j)) :
    ∀ (n : ℕ) (g : ℕ → Plane) (tiles : ℕ → Fin N),
      (∀ i, i + 2 ≤ 2 * n + 1 → Wbtw ℝ (g i) (g (i + 1)) (g (i + 2))) →
      (∀ i, i + 1 ≤ 2 * n + 1 → g i ≠ g (i + 1)) →
      (∀ a b, a ≤ 2 * n + 1 → b ≤ 2 * n + 1 → a ≠ b → g a ≠ g b) →
      (∀ i, i ≤ 2 * n + 1 → g i ∈ D.target.carrier ∩ {x | f x = c}) →
      (∀ i, i < n →
        (D.tile (tiles i)).carrier ∩ {x | f x = c} = segment ℝ (g (2 * i + 1)) (g (2 * i + 2))) →
      (∀ i, i ≤ n → ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g (2 * i)) (g (2 * i + 1)),
        y ∉ interior (D.tile k).carrier) →
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ (g 0) (g (2 * n + 1)))
        = (∑ i ∈ Finset.range n,
              (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                (segment ℝ (g (2 * i + 1)) (g (2 * i + 2))))
          + ∑ i ∈ Finset.range (n + 1),
              ∑ e ∈ D.lineChain f c,
                (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
                  ((D.tile e.1).edge e.2 ∩ segment ℝ (g (2 * i)) (g (2 * i + 1))) :=
  chord_decomposition_of_chain D f hf c hlo hhi

example : True := trivial
#print axioms wrap_chord_decomposition_of_chain
end Erdos634.Draft.ChordDecompositionChainWrap
