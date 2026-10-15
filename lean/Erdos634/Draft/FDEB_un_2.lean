import Erdos634.Draft.FDEDefs
/-! FDE: block 2 of the `un` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_un_2 : (List.range' 51 50).filter (fun N => 0 < N && !FamB N && !exclB N) = [56, 60, 70, 76, 92] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
