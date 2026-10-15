/-
AllCert1.lean -- aggregator for the theorems that depend on large search certificates.

Kept out of `Erdos634.All` so that a single `lean` process stays under about 9 GB (`All` with these imports peaked at
9.0 GB).  Build this module separately.

* `Refl.MS1N156*` (348 modules, 234,239 nodes), `Draft.N156Final` (`N156.not_tile_156`): `156` is NOT a tile count.
* `Refl.MISO154*` (94 modules, 63,895 nodes), `Draft.N154Final` (`N154F.not_tile_154`): `154` is NOT a tile count
  (kernel-checked confirmation of D. Paliy's announcement).
* `Refl.MS4N184*` (108 modules, 71,173 nodes), `Draft.Spectrum200Cond4` (`s4inst_2_2_5`, `decided_154_156`,
  `not_tile_184_of_iso`, `tileCount_iff_le_200_of5`): one of the two instances of `184`; the spectrum up to 200 on
  five instance statements for the four values `132, 135, 161, 184`.

* `Draft.BaseBetaScale2` (`basebeta_scale_two`, `scale_two_1_2_exists`): the base-β targets at scale two of the four
  members with `3 ≤ f ≤ 4` have no tiling (certificates of `104`, `92`, `188`, `156`); the member `(1,2)` has one.

* `Draft.UniformThresholdCert` (`not_betaTilable_two`, `threshold_f3`, `threshold_f3_mul`, `threshold_f4_le_two`):
  the threshold statement of the base-β row at scale two for `f ≤ 4`, and at the scales `1, 2, 3` and the multiples
  of `3` for the two members with `f = 3`.

The other certificate sets (`Refl.MISO132*`, `Refl.MS3N161*`, `Refl.MISO184*`, `Refl.MEQ135*`) have their own
aggregators `AllCert2` to `AllCert5`: one module importing all of them would exceed the memory limit.
-/
import Erdos634.Draft.N156Final
import Erdos634.Draft.N154Final
import Erdos634.Draft.Spectrum200Cond4
import Erdos634.Draft.BaseBetaScale2
import Erdos634.Draft.UniformThresholdCert
