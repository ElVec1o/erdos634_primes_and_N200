import Erdos634.Draft.FDEDefs
/-! FDE: block 2 of the `re` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_re_2 : (List.range' 51 50).filter (fun N => 0 < N && FamB N) = [52, 53, 54, 58, 61, 63, 64, 65, 68, 72, 73, 74, 75, 77, 80, 81, 82, 84, 85, 88, 89, 90, 96, 97, 98, 99, 100] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
