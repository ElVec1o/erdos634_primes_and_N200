/-
AllCert4.lean -- fourth aggregator for theorems that depend on large search certificates.

Kept out of `Erdos634.All` for memory (see `AllCert1.lean`).  Build separately.

* `Refl.MISO184*` (244 data modules, 165,736 nodes) and `Refl.MS4N184*` (108 data modules, 71,173 nodes),
  `Draft.N184Final` (`N184F.not_tile_184`, `not_tileCount_184`, `isoinst_7_8_13_8`, `s4inst_2_2_5`):
  `184` is NOT a tile count.

No module imports this aggregator together with `AllCert1`, `AllCert2` or `AllCert3` (memory; see `AllCert2.lean`).
The statement about all `N ≤ 200` is `Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl` (in `All`); its hypothesis
for `184` is `N184F.not_tileCount_184` here.
-/
import Erdos634.Draft.N184Final
