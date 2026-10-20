/-
Axioms of the results added after `AllV3b` in release v3.1: the 67 windowed exclusions (`no_dissection_win`, and the single-value
theorems for 750 and 963), their negative/positive controls, 465 g^2 and 7672 g^2 for every g >= 2.  After building `Erdos634.AllV3c`:
  lake env lean axioms/AxiomsAllV3c.lean
Every line should read: depends on axioms: [propext, Classical.choice, Quot.sound]; no native_decide is used.
The 15 lines were produced in the author's working repository (all modules already built there), not by a rebuild here.
-/
import Erdos634.AllV3c

#print axioms Erdos634.Draft.NSQM.no_dissection_win
#print axioms Erdos634.Draft.NSQM.no_dissection_y750
#print axioms Erdos634.Draft.NSQM.no_dissection_y963
#print axioms Erdos634.Draft.CollarFam465.tileCount_465_sq_ge2
#print axioms Erdos634.Draft.CollarFam59.tileCount_7672_sq_ge2
#print axioms Erdos634.Draft.NSQM.ctl6_72
#print axioms Erdos634.Draft.NSQM.ctl6_143
#print axioms Erdos634.Draft.NSQM.ctl6_320
#print axioms Erdos634.Draft.NSQM.ctl6_375
#print axioms Erdos634.Draft.NSQM.ctl6_540
#print axioms Erdos634.Draft.NSQM.ctl6_1860
#print axioms Erdos634.Draft.NSQM.ctl6_4185
#print axioms Erdos634.Draft.NSQM.ctl6_7440
#print axioms Erdos634.Draft.NSQM.ctl6_63
#print axioms Erdos634.Draft.NSQM.ctl6_1029
