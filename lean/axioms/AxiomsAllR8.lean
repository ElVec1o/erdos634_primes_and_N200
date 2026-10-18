/-
Axioms of the tilings of 345 and 506 (D. Paliy's nested-corner layouts, kernel-checked here). After building `Erdos634.AllR8`, run
from the directory `lean/`:
  lake env lean axioms/AxiomsAllR8.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.Draft.N345N506

#print axioms Erdos634.Draft.N345N506.tileCount_345
#print axioms Erdos634.Draft.N345N506.tileCount_506
