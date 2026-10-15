import Erdos634.Draft.FDEDefs
/-! FDE: block 4 of the `un` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_un_4 : (List.range' 151 50).filter (fun N => 0 < N && !FamB N && !exclB N) = [154, 155, 156, 158, 161, 166, 168, 171, 172, 174, 182, 184, 186, 187, 188, 189, 190, 198] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
