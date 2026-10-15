import Erdos634.Eq105Rational

/-!
# No equilateral 105-tiling: rational-angle branch (wrapper)

It is not the case that some triangle tiles an equilateral triangle into 105 congruent copies.

The proof has three branches: the π/3-tile, the 2π/3-tile, and the rational-angle tile.  The rational-angle
branch is excluded by arithmetic (N=105 is not d·k² for any d|6); it is formalized as
`Eq105Rational.eq105_not_rational_branch`.  The other two branches are treated by exhaustive search and
certificates, in `Draft/Eq105.lean`.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.Eq105Wrap

open Erdos634.Eq105Rational

/-- thm:eq105 (rational-angle branch): 105 is not d·k² for any d|6. -/
theorem eq105_rational_branch_out (d k : ℕ) (hd : d ∣ 6) (hd0 : 0 < d) (hk : 0 < k) :
    d * k ^ 2 ≠ 105 :=
  eq105_not_rational_branch d k hd hd0 hk

#print axioms eq105_rational_branch_out

end Erdos634.Draft.Eq105Wrap
