/-
AllR8.lean -- aggregator for the tilings of D. Paliy's nested-corner layouts that are checked here: the triangle tiled by
345 copies of (7, 8, 13) and by 506 copies of (7, 8, 13), as kernel-checked `CongruentDissection`s (`Draft.N345N506`); and
the three symbolic family theorems `PRevAll.prev_family`, `PF2All.pf2_family`, `PF3All.pf3_family` (every tile with `b < a`,
`b c - a^2` in `<a,b,c>` resp. `a < 2b`), with the 22 instances of the R8 table.  The constructions are D. Paliy's
(nested corners); the formalization is ours.
No search certificate in the import closure.  Build through `code/_bq.sh Erdos634.AllR8`.  Does not import `Erdos634.All`.
-/
import Erdos634.Draft.N345N506
import Erdos634.Draft.PRevAll -- reversed F4 (a > b), Paliy nested corner; generated PRevDefs/Disj/Sub*/Tile/Asm/Real + PCore, PHyp
import Erdos634.Draft.PF2All -- F2 (a > b), same hypotheses
import Erdos634.Draft.PF3All -- ordered F3 (b < a < 2b); PHypG
