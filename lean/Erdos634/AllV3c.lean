/-
AllV3c.lean -- aggregator for the modules added after `AllV3b` in release v3.1.  Does NOT import `Erdos634.All`; no search certificate
`Refl.M*` in the import closure.  Contents:
* `NSQWinAll`    -- `no_dissection_win`: 67 census-excluded values <= 10^5 (including 270, 412, 750, 963) have no congruent dissection (windowed chain `CN'zETWD6`; UNAUDITED);
* `NSQWinCtl6`   -- negative controls of that chain (it must NOT fire on known tile counts such as 63, 72, 143, 320, 375, 540, 1029, 1860, 4185, 7440);
* `CollarFam465` -- 465 g^2 is a tile count for every g >= 2 (seed TM1860, collar layer step);
* `CollarFam59`  -- 7672 g^2 is a tile count for every g >= 2 (seed TM30688, collar layer step; Paliy's up-set already covers K >= 153).
These modules were built in the working repository of the author (one module at a time); they were NOT rebuilt in this repository.
-/
import Erdos634.Draft.NSQWinAll
import Erdos634.Draft.NSQWinCtl6
import Erdos634.Draft.CollarFam465
import Erdos634.Draft.CollarFam59
