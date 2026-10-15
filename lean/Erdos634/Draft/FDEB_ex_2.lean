import Erdos634.Draft.FDEDefs
/-! FDE: block 2 of the `ex` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_ex_2 : (List.range' 51 50).filter (fun N => 0 < N && !FamB N && exclB N) = [51, 55, 57, 59, 62, 66, 67, 69, 71, 78, 79, 83, 86, 87, 91, 93, 94, 95] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
