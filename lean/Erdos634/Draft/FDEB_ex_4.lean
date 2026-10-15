import Erdos634.Draft.FDEDefs
/-! FDE: block 4 of the `ex` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_ex_4 : (List.range' 151 50).filter (fun N => 0 < N && !FamB N && exclB N) = [151, 152, 159, 163, 165, 167, 177, 179, 183, 191, 195, 199] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
