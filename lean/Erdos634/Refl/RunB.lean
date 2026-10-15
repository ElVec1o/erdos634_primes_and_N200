import Erdos634.Refl.DataB
set_option profiler true
set_option profiler.threshold 500
set_option maxRecDepth 100000 in
theorem okB : instB.checkAll 200 treeB = true := by decide +kernel
#print axioms okB
