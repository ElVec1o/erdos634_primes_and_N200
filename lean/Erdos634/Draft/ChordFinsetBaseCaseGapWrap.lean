import Erdos634.ChordFinsetBaseCaseGap

namespace Erdos634.Draft.ChordFinsetBaseCaseGapWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_gap_free_of_all_excluded {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q p : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (hPp : Wbtw ℝ P p Q) (hpQ : p ≠ Q)
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (S k) p) :
    ∀ k : Fin N, ∀ y ∈ openSegment ℝ p Q, y ∉ interior (D.tile k).carrier :=
  gap_free_of_all_excluded D f hf c hPQ hPp hpQ R S hglobal hexcl

example : True := trivial
#print axioms wrap_gap_free_of_all_excluded

end Erdos634.Draft.ChordFinsetBaseCaseGapWrap
