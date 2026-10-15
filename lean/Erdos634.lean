/-
Root of the library `Erdos634`: `lake build` builds `Erdos634.All` (every module whose import closure contains no
search certificate, among them the whole proof of the theorem on primes). The other aggregates,
`Erdos634.AllThreshold`, `Erdos634.AllSpectrum` and `Erdos634.AllCert1` to `Erdos634.AllCert5`, are built by name;
see `lean/README.md`.
-/
import Erdos634.All
