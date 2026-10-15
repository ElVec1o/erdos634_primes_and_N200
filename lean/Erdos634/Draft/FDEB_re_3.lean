import Erdos634.Draft.FDEDefs
/-! FDE: block 3 of the `re` check of the spectrum table (imports only the definitions). -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem blk_re_3 : (List.range' 101 50).filter (fun N => 0 < N && FamB N) = [101, 104, 106, 108, 109, 112, 113, 116, 117, 121, 122, 125, 126, 128, 130, 136, 137, 144, 145, 146, 147, 148, 149, 150] := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
