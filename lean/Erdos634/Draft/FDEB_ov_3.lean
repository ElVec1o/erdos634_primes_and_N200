import Erdos634.Draft.FDEDefs
/-! FDE: block 3 of the `ov` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_ov_3 : ∀ N ∈ List.range' 101 50,
    (FamB N && (decide (N ∈ exclList) || decide (N ∈ primeExcl))) = false := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
