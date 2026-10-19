/-
Axioms of D. Paliy's nested-corner family theorems (formalized here) and of the tilings of 345 and 506 (kernel-checked layouts), with the 22
instances of the R8 table. After building `Erdos634.AllR8`, run from the directory `lean/`:
  lake env lean axioms/AxiomsAllR8.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.Draft.N345N506
import Erdos634.Draft.PRevAll
import Erdos634.Draft.PF2All
import Erdos634.Draft.PF3All
import Erdos634.Draft.AllTemplates

#print axioms Erdos634.Draft.N345N506.tileCount_345
#print axioms Erdos634.Draft.N345N506.tileCount_506
#print axioms Erdos634.Draft.PRevAll.prev_family
#print axioms Erdos634.Draft.PRevAll.tileCount_345
#print axioms Erdos634.Draft.PRevAll.tileCount_12922
#print axioms Erdos634.Draft.PRevAll.tileCount_65626
#print axioms Erdos634.Draft.PRevAll.tileCount_135746
#print axioms Erdos634.Draft.PRevAll.tileCount_428978
#print axioms Erdos634.Draft.PRevAll.tileCount_538346
#print axioms Erdos634.Draft.PRevAll.tileCount_686945
#print axioms Erdos634.Draft.PRevAll.tileCount_914529
#print axioms Erdos634.Draft.PF2All.pf2_family
#print axioms Erdos634.Draft.PF2All.tileCount_506
#print axioms Erdos634.Draft.PF2All.tileCount_18602
#print axioms Erdos634.Draft.PF2All.tileCount_57479
#print axioms Erdos634.Draft.PF2All.tileCount_156647
#print axioms Erdos634.Draft.PF2All.tileCount_201122
#print axioms Erdos634.Draft.PF2All.tileCount_388847
#print axioms Erdos634.Draft.PF2All.tileCount_624338
#print axioms Erdos634.Draft.PF2All.tileCount_746327
#print axioms Erdos634.Draft.PF3All.pf3_family
#print axioms Erdos634.Draft.PF3All.tileCount_25179
#print axioms Erdos634.Draft.PF3All.tileCount_35763
#print axioms Erdos634.Draft.PF3All.tileCount_146982
#print axioms Erdos634.Draft.PF3All.tileCount_196251
#print axioms Erdos634.Draft.PF3All.tileCount_247494
#print axioms Erdos634.Draft.PF3All.tileCount_397371
#print axioms Erdos634.Draft.T11625.tileCount_11625
#print axioms Erdos634.Draft.T66960.tileCount_66960
#print axioms Erdos634.Draft.T119040.tileCount_119040
#print axioms Erdos634.Draft.T121765.tileCount_121765
#print axioms Erdos634.Draft.T167865.tileCount_167865
#print axioms Erdos634.Draft.T186000.tileCount_186000
#print axioms Erdos634.Draft.T364560.tileCount_364560
#print axioms Erdos634.Draft.T603750.tileCount_603750
