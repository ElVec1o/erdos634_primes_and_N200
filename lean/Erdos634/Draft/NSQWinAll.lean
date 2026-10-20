/-
Draft/NSQWinAll.lean -- aggregator of the census-excluded values made FORMAL by the windowed chain `CN'zETWD6` (`NSQWin3`):
the 67 values of `winList` (the the census program `30 s^2`/`t^2(12t^2-1)` values and the S+ thick-W values, all <= 10^5, whose only obstruction was the
kernel memory of the old leaf checks).  `no_dissection_win`: no congruent dissection with `N` tiles for any `N` in `winList`.
Credit: Beeson-Rosu, Paliy, the S+ work, the census program.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWinY270
import Erdos634.Draft.NSQWinY412
import Erdos634.Draft.NSQWinY750
import Erdos634.Draft.NSQWinY963
import Erdos634.Draft.NSQWinY1470
import Erdos634.Draft.NSQWinY2430
import Erdos634.Draft.NSQWinY2524
import Erdos634.Draft.NSQWinY3630
import Erdos634.Draft.NSQWinY4252
import Erdos634.Draft.NSQWinY4336
import Erdos634.Draft.NSQWinY4734
import Erdos634.Draft.NSQWinY5070
import Erdos634.Draft.NSQWinY6750
import Erdos634.Draft.NSQWinY9052
import Erdos634.Draft.NSQWinY9550
import Erdos634.Draft.NSQWinZ10830
import Erdos634.Draft.NSQWinZ12124
import Erdos634.Draft.NSQWinZ12656
import Erdos634.Draft.NSQWinZ13230
import Erdos634.Draft.NSQWinZ15870
import Erdos634.Draft.NSQWinZ15966
import Erdos634.Draft.NSQWinZ17572
import Erdos634.Draft.NSQWinZ18750
import Erdos634.Draft.NSQWinZ19612
import Erdos634.Draft.NSQWinZ19809
import Erdos634.Draft.NSQWinZ21870
import Erdos634.Draft.NSQWinZ24028
import Erdos634.Draft.NSQWinZ24066
import Erdos634.Draft.NSQWinZ25230
import Erdos634.Draft.NSQWinZ25328
import Erdos634.Draft.NSQWinZ26404
import Erdos634.Draft.NSQWinZ28763
import Erdos634.Draft.NSQWinZ28830
import Erdos634.Draft.NSQWinZ28892
import Erdos634.Draft.NSQWinZ32670
import Erdos634.Draft.NSQWinZ33822
import Erdos634.Draft.NSQWinZ34204
import Erdos634.Draft.NSQWinZ36750
import Erdos634.Draft.NSQWinZ39964
import Erdos634.Draft.NSQWinZ41070
import Erdos634.Draft.NSQWinZ42352
import Erdos634.Draft.NSQWinZ45630
import Erdos634.Draft.NSQWinC46172
import Erdos634.Draft.NSQWinC49444
import Erdos634.Draft.NSQWinC50430
import Erdos634.Draft.NSQWinC52672
import Erdos634.Draft.NSQWinC52828
import Erdos634.Draft.NSQWinC52956
import Erdos634.Draft.NSQWinC55150
import Erdos634.Draft.NSQWinC55470
import Erdos634.Draft.NSQWinC59932
import Erdos634.Draft.NSQWinC60750
import Erdos634.Draft.NSQWinC65457
import Erdos634.Draft.NSQWinC66270
import Erdos634.Draft.NSQWinC67484
import Erdos634.Draft.NSQWinC71428
import Erdos634.Draft.NSQWinC72030
import Erdos634.Draft.NSQWinC75484
import Erdos634.Draft.NSQWinC78651
import Erdos634.Draft.NSQWinC81486
import Erdos634.Draft.NSQWinC83932
import Erdos634.Draft.NSQWinC84270
import Erdos634.Draft.NSQWinC88324
import Erdos634.Draft.NSQWinC89406
import Erdos634.Draft.NSQWinC90750
import Erdos634.Draft.NSQWinC92050
import Erdos634.Draft.NSQWinC97470

set_option maxRecDepth 8000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry

def winList : List ℕ := [270, 412, 750, 963, 1470, 2430, 2524, 3630, 4252, 4336, 4734, 5070, 6750, 9052, 9550, 10830, 12124, 12656, 13230, 15870, 15966, 17572, 18750, 19612, 19809, 21870, 24028, 24066, 25230, 25328, 26404, 28763, 28830, 28892, 32670, 33822, 34204, 36750, 39964, 41070, 42352, 45630, 46172, 49444, 50430, 52672, 52828, 52956, 55150, 55470, 59932, 60750, 65457, 66270, 67484, 71428, 72030, 75484, 78651, 81486, 83932, 84270, 88324, 89406, 90750, 92050, 97470]

theorem no_dissection_win (N : ℕ) (hN : N ∈ winList) (D : CongruentDissection N) : False := by
  have h : N = 270 ∨ N = 412 ∨ N = 750 ∨ N = 963 ∨ N = 1470 ∨ N = 2430 ∨ N = 2524 ∨ N = 3630 ∨ N = 4252 ∨ N = 4336 ∨ N = 4734 ∨ N = 5070 ∨ N = 6750 ∨ N = 9052 ∨ N = 9550 ∨ N = 10830 ∨ N = 12124 ∨ N = 12656 ∨ N = 13230 ∨ N = 15870 ∨ N = 15966 ∨ N = 17572 ∨ N = 18750 ∨ N = 19612 ∨ N = 19809 ∨ N = 21870 ∨ N = 24028 ∨ N = 24066 ∨ N = 25230 ∨ N = 25328 ∨ N = 26404 ∨ N = 28763 ∨ N = 28830 ∨ N = 28892 ∨ N = 32670 ∨ N = 33822 ∨ N = 34204 ∨ N = 36750 ∨ N = 39964 ∨ N = 41070 ∨ N = 42352 ∨ N = 45630 ∨ N = 46172 ∨ N = 49444 ∨ N = 50430 ∨ N = 52672 ∨ N = 52828 ∨ N = 52956 ∨ N = 55150 ∨ N = 55470 ∨ N = 59932 ∨ N = 60750 ∨ N = 65457 ∨ N = 66270 ∨ N = 67484 ∨ N = 71428 ∨ N = 72030 ∨ N = 75484 ∨ N = 78651 ∨ N = 81486 ∨ N = 83932 ∨ N = 84270 ∨ N = 88324 ∨ N = 89406 ∨ N = 90750 ∨ N = 92050 ∨ N = 97470 := by simpa [winList] using hN
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_dissection_y270 D
  · exact no_dissection_y412 D
  · exact no_dissection_y750 D
  · exact no_dissection_y963 D
  · exact no_dissection_y1470 D
  · exact no_dissection_y2430 D
  · exact no_dissection_y2524 D
  · exact no_dissection_y3630 D
  · exact no_dissection_y4252 D
  · exact no_dissection_y4336 D
  · exact no_dissection_y4734 D
  · exact no_dissection_y5070 D
  · exact no_dissection_y6750 D
  · exact no_dissection_y9052 D
  · exact no_dissection_y9550 D
  · exact no_dissection_z10830 D
  · exact no_dissection_z12124 D
  · exact no_dissection_z12656 D
  · exact no_dissection_z13230 D
  · exact no_dissection_z15870 D
  · exact no_dissection_z15966 D
  · exact no_dissection_z17572 D
  · exact no_dissection_z18750 D
  · exact no_dissection_z19612 D
  · exact no_dissection_z19809 D
  · exact no_dissection_z21870 D
  · exact no_dissection_z24028 D
  · exact no_dissection_z24066 D
  · exact no_dissection_z25230 D
  · exact no_dissection_z25328 D
  · exact no_dissection_z26404 D
  · exact no_dissection_z28763 D
  · exact no_dissection_z28830 D
  · exact no_dissection_z28892 D
  · exact no_dissection_z32670 D
  · exact no_dissection_z33822 D
  · exact no_dissection_z34204 D
  · exact no_dissection_z36750 D
  · exact no_dissection_z39964 D
  · exact no_dissection_z41070 D
  · exact no_dissection_z42352 D
  · exact no_dissection_z45630 D
  · exact no_dissection_c46172 D
  · exact no_dissection_c49444 D
  · exact no_dissection_c50430 D
  · exact no_dissection_c52672 D
  · exact no_dissection_c52828 D
  · exact no_dissection_c52956 D
  · exact no_dissection_c55150 D
  · exact no_dissection_c55470 D
  · exact no_dissection_c59932 D
  · exact no_dissection_c60750 D
  · exact no_dissection_c65457 D
  · exact no_dissection_c66270 D
  · exact no_dissection_c67484 D
  · exact no_dissection_c71428 D
  · exact no_dissection_c72030 D
  · exact no_dissection_c75484 D
  · exact no_dissection_c78651 D
  · exact no_dissection_c81486 D
  · exact no_dissection_c83932 D
  · exact no_dissection_c84270 D
  · exact no_dissection_c88324 D
  · exact no_dissection_c89406 D
  · exact no_dissection_c90750 D
  · exact no_dissection_c92050 D
  · exact no_dissection_c97470 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_win
