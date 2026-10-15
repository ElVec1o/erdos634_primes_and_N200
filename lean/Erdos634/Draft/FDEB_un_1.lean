import Erdos634.Draft.FDEDefs
/-! FDE: block 1 of the `un` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_un_1 : (List.range' 0 51).filter (fun N => 0 < N && !FamB N && !exclB N) = [] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
