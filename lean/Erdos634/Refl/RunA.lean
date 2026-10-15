import Erdos634.Refl.DataA
set_option maxRecDepth 100000 in
theorem okA : inst.checkAll 100 tree = true := by decide +kernel
#print axioms okA
