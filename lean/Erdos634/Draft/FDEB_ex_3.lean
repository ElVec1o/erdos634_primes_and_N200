import Erdos634.Draft.FDEDefs
/-! FDE: block 3 of the `ex` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_ex_3 : (List.range' 101 50).filter (fun N => 0 < N && !FamB N && exclB N) = [103, 107, 110, 111, 123, 127, 129, 131, 133, 139, 141] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
