import Erdos634.ChordStraddlerSegment

namespace Erdos634.Draft.ChordStraddlerSegmentWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_straddle_trace_nonempty (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {i j : Fin 3} (hi : f (T.pts i) < c) (hj : c < f (T.pts j)) :
    ∃ x ∈ T.carrier, f x = c :=
  straddle_trace_nonempty T f c hi hj

theorem wrap_straddle_trace_isSegment (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {i j : Fin 3} (hi : f (T.pts i) < c) (hj : c < f (T.pts j)) :
    ∃ p q, p ∈ T.carrier ∩ {x | f x = c} ∧ q ∈ T.carrier ∩ {x | f x = c}
      ∧ T.carrier ∩ {x | f x = c} = segment ℝ p q :=
  straddle_trace_isSegment T f hf c hi hj

example : True := trivial
#print axioms wrap_straddle_trace_isSegment

end Erdos634.Draft.ChordStraddlerSegmentWrap
