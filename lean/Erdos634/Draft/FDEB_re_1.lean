import Erdos634.Draft.FDEDefs
/-! FDE: block 1 of the `re` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_re_1 : (List.range' 0 51).filter (fun N => 0 < N && FamB N) = [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 32, 34, 36, 37, 40, 41, 44, 45, 48, 49, 50] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
