import Erdos634.PgramTiling22
import Erdos634.PgramTiling52

/-!
# Wide parallelograms: two-member certificate

Wide parallelograms exist at all (e,f).  Two certified members:

**f=2 (tile (2,3,4), 22 tiles)**: `PgramTiling22.checkAll = true`; checks (C1)–(C4)
by `decide`, zero axioms.

**f=3 (tile (3,8,9), 52 tiles)**: `PgramTiling52.checkAll = true`; checks (C1)–(C4)
by `decide`, zero axioms (1326 disjoint-interior pairs).

The general statement (all (e,f)) is not covered here.

In All.lean, 0 sorry, zero axioms.
-/

namespace Erdos634.Draft.WideColWrap

/-- The 22-tile parallelogram certificate is valid (congruence, orientation,
    disjoint interiors, area identity — all for the (2,3,4) member, f=2). -/
theorem widecol_22_cert : PgramTiling22.checkAll = true :=
  PgramTiling22.pgram22_certificate

/-- The 52-tile parallelogram certificate is valid (congruence, orientation,
    disjoint interiors, area identity — all for the (3,8,9) member, f=3). -/
theorem widecol_52_cert : PgramTiling52.checkAll = true :=
  PgramTiling52.pgramtiling52_certificate

#print axioms widecol_22_cert
#print axioms widecol_52_cert

end Erdos634.Draft.WideColWrap
