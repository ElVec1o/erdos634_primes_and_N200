import Erdos634.Draft.FDEDefs
/-! FDE: block 3 of the `un` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_un_3 : (List.range' 101 50).filter (fun N => 0 < N && !FamB N && !exclB N) = [102, 105, 114, 115, 118, 119, 120, 124, 132, 134, 135, 138, 140, 142, 143] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
