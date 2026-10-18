/-
Axioms of the declarations of release v1.14 whose module lies in the import closure of `Erdos634.AllCertW2` (the certificates
`Refl.MG204`, `Refl.MG228` are regenerated first: `code/regen_cert.sh G204`, `G228`). After building `Erdos634.AllCertW2`, run
from the directory `lean/`:
  lake env lean axioms/AxiomsAllCertW2.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.Draft.N204N228

#print axioms Erdos634.Draft.NSQM.not_tile_204
#print axioms Erdos634.Draft.NSQM.not_tile_228
