/-
Draft/E60Apps.lean: the `π/3` leaf (`GapE60 N`) of the values whose `π/3` pairs are all irrational, of the wrong
parity, or the pin: no certificate.

`E60Irr.gapE60_of_chk_sq` with the empty list: the pair table `E60Irr.Pairs60ChkSq N []` is a kernel check, and every
pair it leaves has a non-square discriminant, hence is excluded by `E60Irr.e60Pair_of_not_isSquare` (the relation
`j a = p b + q c` of `E60Graph.sixty_has_a_relation`).  For `N = 168, 171, 198` this replaces the conjugate-kill
certificates (`Draft/E60N168.lean`, `E60N171.lean`, `E60N198.lean`), which remain valid as independent checks.

No sorry, no native_decide.
-/
import Erdos634.Draft.E60Irr

namespace Erdos634.Draft.E60Apps

open Erdos634.Draft.Chain15 Erdos634.Draft.E60Irr

theorem gapE60_132 : GapE60 132 :=
  gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp)

theorem gapE60_135 : GapE60 135 :=
  gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp)

theorem gapE60_156 : GapE60 156 :=
  gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp)

theorem gapE60_168 : GapE60 168 :=
  gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp)

theorem gapE60_171 : GapE60 171 :=
  gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp)

theorem gapE60_198 : GapE60 198 :=
  gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp)

end Erdos634.Draft.E60Apps

#print axioms Erdos634.Draft.E60Apps.gapE60_132
#print axioms Erdos634.Draft.E60Apps.gapE60_135
#print axioms Erdos634.Draft.E60Apps.gapE60_156
#print axioms Erdos634.Draft.E60Apps.gapE60_171
