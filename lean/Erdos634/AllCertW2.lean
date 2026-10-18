/-
AllCertW2.lean -- sixth aggregator for the gamma = 2 alpha (W2) search certificates.

Kept OUT of `Erdos634.All` (import closure contains `Refl.M*`; memory rule, see `AllCert1.lean`).  Build separately
through `code/_bq.sh Erdos634.AllCertW2`.

* `Refl.MG204` (504,735 nodes, certgenm): the gamma = 2 alpha pair (u,v) = (7,10), g = 2, tile (49, 51, 70), target
  legs 714, base 1020 [N = 204, pair (M,M') = (6,34)].
* `Refl.MG228` (certgenx, chunked): (u,v) = (8,11), g = 2, tile (64, 57, 88), legs 912, base 1254 [N = 228, pair (6,38)].
* `Draft.N204N228`: `not_tile_204`, `not_tile_228` (CN'zET minus its G leaf + these certificates, as N171).
-/
import Erdos634.Draft.N204N228
