import Erdos634.PrimeBranchRepair

namespace Erdos634.Draft.PrimeBranchRepairWrap
open Erdos634.PrimeBranchRepair

theorem wrap_excluded_witnesses :
    (5:ℤ) % 8 = 5 ∧ (11:ℤ) % 8 = 3 ∧ (13:ℤ) % 8 = 5 ∧ (19:ℤ) % 8 = 3 ∧
    (29:ℤ) % 8 = 5 ∧ (37:ℤ) % 8 = 5 ∧ (43:ℤ) % 8 = 3 ∧ (53:ℤ) % 8 = 5 :=
  excluded_witnesses

example : True := trivial
#print axioms wrap_excluded_witnesses

end Erdos634.Draft.PrimeBranchRepairWrap
