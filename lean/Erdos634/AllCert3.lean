/-
AllCert3.lean -- third aggregator for theorems that depend on large search certificates.

Kept out of `Erdos634.All` for memory (see `AllCert1.lean`).  Build separately.

* `Refl.MS3N161*` (507 data modules, 16 soundness modules, 345,746 nodes in 61,542 pieces),
  `Draft.N161Final` (`N161F.not_tile_161`, `not_tileCount_161`, `s3inst_1_3_4`): `161` is NOT a tile count.

The soundness glue of this certificate is split into parts of 4000 theorems (`code/split_sound.py`; manifest column
`certgenm+split:4000`): Lean aborts with a stack overflow on a single module with 61,542 theorems.

No module imports this aggregator together with `AllCert1` or `AllCert2` (memory; see `AllCert2.lean`).  The statement
about all `N ≤ 200` is `Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl` (in `All`); its hypothesis for `161` is
`N161F.not_tileCount_161` here.
-/
import Erdos634.Draft.N161Final
