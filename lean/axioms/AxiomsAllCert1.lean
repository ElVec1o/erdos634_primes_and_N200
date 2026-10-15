/-
Axioms of the declarations of the Lean map table of the paper (and of the tilings with 330, 897 and 990
tiles) whose module lies in the import closure of `Erdos634.AllCert1`. After building `Erdos634.AllCert1`, run
from the directory `lean/`:
  lake env lean axioms/AxiomsAllCert1.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.Draft.BaseBetaScale2
import Erdos634.Draft.Spectrum200Cond4
import Erdos634.Draft.UniformThresholdCert

#print axioms Erdos634.Draft.Spectrum200Cond4.decided_154_156
#print axioms Erdos634.Draft.BaseBetaScale2.basebeta_scale_two
#print axioms Erdos634.Draft.BaseBetaScale2.scale_two_1_2_exists
#print axioms Erdos634.Draft.UniformThreshold.threshold_1_3
#print axioms Erdos634.Draft.UniformThreshold.threshold_2_3
#print axioms Erdos634.Draft.UniformThreshold.threshold_1_4_of_ne_three
#print axioms Erdos634.Draft.UniformThreshold.threshold_3_4_of_ne_three
