/-
Axioms of the headline theorems of the aggregate `Erdos634.AllV6b` (release 6.0). After building `Erdos634.AllV6b`, run from the directory `lean/`:
  lake env lean axioms/AxiomsAllV6b.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.AllV6b
#print axioms Erdos634.Draft.ThetaNotch.thetaTiled_all
#print axioms Erdos634.Draft.ThetaNotch.thetaTiled_band
#print axioms Erdos634.Draft.ThetaOddE.thetaTiled_oddE
