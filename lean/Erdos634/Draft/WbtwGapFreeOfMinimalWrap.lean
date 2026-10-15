import Erdos634.WbtwGapFreeOfMinimal

namespace Erdos634.Draft.WbtwGapFreeOfMinimalWrap
open Erdos634.ChordTraceReal Erdos634.Geometry

theorem wrap_gap_free_of_minimal {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {p q r s : Plane} {m : Fin N}
    (hp : p ∈ D.target.carrier ∩ {x | f x = c}) (hr : r ∈ D.target.carrier ∩ {x | f x = c})
    (hpr : p ≠ r) (ho : Wbtw ℝ p r s)
    (hmtrace : (D.tile m).carrier ∩ {x | f x = c} = segment ℝ r s)
    (hmin : ∀ k : Fin N, k ≠ m →
      (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      ∀ y ∈ (D.tile k).carrier ∩ {x | f x = c}, Wbtw ℝ p r y) :
    ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier :=
  @gap_free_of_minimal N D f hf c p q r s m hp hr hpr ho hmtrace hmin

example : True := trivial
#check @wrap_gap_free_of_minimal

end Erdos634.Draft.WbtwGapFreeOfMinimalWrap
