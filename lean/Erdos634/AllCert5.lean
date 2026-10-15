/-
AllCert5.lean -- fifth aggregator for theorems that depend on large search certificates.

Kept out of `Erdos634.All` for memory (see `AllCert1.lean`).  Build separately.

* `Refl.MEQ135*` (2766 data modules, 1,326,256 exact nodes, 81,629 nogoods, the mirror half tree through
  `Refl.sound_mirror`) and `Draft.N135Final` (`N135F.not_tile_135`, `N135F.not_tileCount_135`): `135` is NOT a tile
  count.  Paliy announced this exclusion; the certificate here is a reproduction with a kernel check.

No module imports this aggregator together with `AllCert1`, `AllCert2`, `AllCert3` or `AllCert4` (memory; see
`AllCert2.lean`).  The statement about all `N ≤ 200` is `Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl` (in
`All`); its six exclusion hypotheses are the theorems of `AllCert1` to `AllCert5`, each kernel-checked in its own
aggregator.
-/
import Erdos634.Draft.N135Final
