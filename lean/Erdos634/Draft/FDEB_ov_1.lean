import Erdos634.Draft.FDEDefs
/-! FDE: block 1 of the `ov` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_ov_1 : ∀ N ∈ List.range' 0 51,
    (FamB N && (decide (N ∈ exclList) || decide (N ∈ primeExcl))) = false := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
