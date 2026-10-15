import Erdos634.Draft.FDEDefs
/-! FDE: block 1 of the `ex` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_ex_1 : (List.range' 0 51).filter (fun N => 0 < N && !FamB N && exclB N) = [7, 11, 14, 15, 19, 21, 22, 23, 30, 31, 33, 35, 38, 39, 42, 43, 46, 47] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
