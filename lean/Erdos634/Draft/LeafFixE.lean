/-
Draft/LeafFixE.lean -- the corrected equilateral leaf `LeafEsqS`: `LeafEsqN` (NSQMMainZE.lean:29) with `Pairs120Chk N` replaced by
`E120Irr.Pairs120ChkSq N []`.

`Pairs120Chk` (AllNExclusionArith2.lean:109) demands, for EVERY pair `s t = 3N`, both a non-square `(s+t)^2 + 4N` AND `(s+t) ∤ 2N` (and has no parity
escape); `Pairs120ChkSq` (E120Irr.lean:39) demands only parity-mismatch or non-square discriminant, because `E120Irr.e120Pair_of_not_isSquare` excludes
every pair whose discriminant is not a square, for all `N` (Beeson-Zhang Thm 5.2 reproduced; `prop:twopi3rel`).  `gapE120_of_chk_sq` takes the table
with an empty list of "to be certified" pairs.  No new geometry: the closure `leafEsqS_gapE120` just calls it.

Credit: Beeson-Zhang (Thm 5.2 / Lemma 3.5), Laczkovich (the flux invariant).  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.E120Irr
import Erdos634.Draft.E60Irr

set_option maxRecDepth 8000

namespace Erdos634.Draft.LeafFix

open Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr

def LeafEsqS (N : ℕ) : Prop := N % 4 = 2 ∨ (11 ≤ N ∧ Pairs60ChkSq N [] ∧ Pairs120ChkSq N [])

instance (N : ℕ) : Decidable (LeafEsqS N) := by unfold LeafEsqS; infer_instance

theorem leafEsqS_gapE120 (N : ℕ) (h120 : Pairs120ChkSq N []) : Erdos634.Draft.Chain15.GapE120 N :=
  gapE120_of_chk_sq [] h120 (by intro p hp; cases hp)

end Erdos634.Draft.LeafFix

#print axioms Erdos634.Draft.LeafFix.leafEsqS_gapE120
