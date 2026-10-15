import Erdos634.ChordAssembly
namespace Erdos634.Draft.ChordAssemblyWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_isSegment {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {x0 : Plane} (hx0 : x0 ∈ D.target.carrier) (hfx0 : f x0 = c) :
    ∃ p q, p ∈ D.target.carrier ∩ {x | f x = c} ∧ q ∈ D.target.carrier ∩ {x | f x = c}
      ∧ D.target.carrier ∩ {x | f x = c} = segment ℝ p q :=
  chord_isSegment D f hf c hx0 hfx0

example : True := trivial
#print axioms wrap_chord_isSegment
end Erdos634.Draft.ChordAssemblyWrap
