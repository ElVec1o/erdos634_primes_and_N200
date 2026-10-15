/-
AllCert2.lean -- second aggregator for theorems that depend on large search certificates.

Kept out of `Erdos634.All` for memory (see `AllCert1.lean`).  Build separately.

* `Refl.MISO132*` (342 modules, 233,117 nodes), `Draft.N132Final` (`N132F.not_tile_132`, `not_tileCount_132`,
  `isoinst_5_3_7_6`): `132` is NOT a tile count.

No module imports this aggregator together with `AllCert1`: a statement assembled from `132`, `154` and `156` at once
peaked at 9.09 GB.  The statement about all `N ≤ 200` is `Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl` (in
`All`), whose hypotheses `¬ TileCount n` are discharged one module at a time: `N132F.not_tileCount_132` here,
`N154F.not_tileCount_154` and `N156.not_tileCount_156` in `AllCert1`.
-/
import Erdos634.Draft.N132Final
