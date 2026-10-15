import Erdos634.CevianTiling28

namespace Erdos634.Draft.CevianTiling28Wrap

open CevianTiling28

-- Re-exports: zero-axiom kernel verification of the 28-tile cevian tiling certificate
-- (28 copies of tile [2,3,4] tile the cevian target; Z[sqrt15] coordinates scaled by 8)

theorem wrap_ceviantiling28_certificate : checkAll = true :=
  ceviantiling28_certificate

example : True := trivial

#print axioms CevianTiling28.ceviantiling28_certificate

end Erdos634.Draft.CevianTiling28Wrap
