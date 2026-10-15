import Erdos634.Draft.FDEDefs
/-! FDE: block 4 of the `re` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_re_4 : (List.range' 151 50).filter (fun N => 0 < N && FamB N) = [153, 157, 160, 162, 164, 169, 170, 173, 175, 176, 178, 180, 181, 185, 192, 193, 194, 196, 197, 200] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
