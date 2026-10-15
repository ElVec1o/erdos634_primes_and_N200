/-
Axioms of the declarations of the Lean map table of the paper (and of the tilings with 330, 897 and 990
tiles) whose module lies in the import closure of `Erdos634.AllCert2`. After building `Erdos634.AllCert2`, run
from the directory `lean/`:
  lake env lean axioms/AxiomsAllCert2.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.Draft.N132Final

#print axioms Erdos634.Draft.N132F.not_tileCount_132
