/- AllN2Check242: N = 4443, 4445, 4447, 4449, 4451
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4443_sqf   : LeafSqf 4443   := by decide +kernel
private theorem c4443_range : LeafRange 4443  := by decide +kernel
private theorem c4443_ell   : LeafEll 4443    := by decide +kernel
private theorem c4443_nsq   : NSqChkSq 4443   := by decide +kernel
private theorem c4443_har   : HArithChkSq 4443 := by decide +kernel
private theorem c4443_r     : LeafR 4443      := by decide +kernel
private theorem c4443_e'    : LeafE' 4443     := by decide +kernel
private theorem c4443_f1    : LeafF1 4443     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4443_s2    : S2ChkSq 4443    := by decide +kernel
private theorem c4443_s3    : S3ChkSq 4443    := by decide +kernel
private theorem c4443_iso   : LeafIso 4443    := by decide +kernel
private theorem c4443_nof2  : NoF2ChkSq 4443  := by decide +kernel
private theorem c4443_nof3  : NoF3ChkSq 4443  := by decide +kernel
private theorem c4443_nof4z : NoF4zChkSq 4443 := by decide +kernel
theorem C'_4443 : C' 4443 :=
  ⟨c4443_sqf, c4443_range, c4443_ell, leafNSq_of_sq c4443_nsq, leafHAr_of_sq c4443_har,
   c4443_r, c4443_e', c4443_f1, leafS2_of_sq c4443_s2, leafS3_of_sq c4443_s3,
   c4443_iso, leafR8_of_sq c4443_nof2 c4443_nof3 c4443_nof4z⟩
theorem not_tile'_4443 (D : CongruentDissection 4443) : False :=
  not_tile_of_conditions' 4443 C'_4443 D

private theorem c4445_sqf   : LeafSqf 4445   := by decide +kernel
private theorem c4445_range : LeafRange 4445  := by decide +kernel
private theorem c4445_ell   : LeafEll 4445    := by decide +kernel
private theorem c4445_nsq   : NSqChkSq 4445   := by decide +kernel
private theorem c4445_har   : HArithChkSq 4445 := by decide +kernel
private theorem c4445_r     : LeafR 4445      := by decide +kernel
private theorem c4445_e'    : LeafE' 4445     := by decide +kernel
private theorem c4445_f1    : LeafF1 4445     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4445_s2    : S2ChkSq 4445    := by decide +kernel
private theorem c4445_s3    : S3ChkSq 4445    := by decide +kernel
private theorem c4445_iso   : LeafIso 4445    := by decide +kernel
private theorem c4445_nof2  : NoF2ChkSq 4445  := by decide +kernel
private theorem c4445_nof3  : NoF3ChkSq 4445  := by decide +kernel
private theorem c4445_nof4z : NoF4zChkSq 4445 := by decide +kernel
theorem C'_4445 : C' 4445 :=
  ⟨c4445_sqf, c4445_range, c4445_ell, leafNSq_of_sq c4445_nsq, leafHAr_of_sq c4445_har,
   c4445_r, c4445_e', c4445_f1, leafS2_of_sq c4445_s2, leafS3_of_sq c4445_s3,
   c4445_iso, leafR8_of_sq c4445_nof2 c4445_nof3 c4445_nof4z⟩
theorem not_tile'_4445 (D : CongruentDissection 4445) : False :=
  not_tile_of_conditions' 4445 C'_4445 D

private theorem c4447_sqf   : LeafSqf 4447   := by decide +kernel
private theorem c4447_range : LeafRange 4447  := by decide +kernel
private theorem c4447_ell   : LeafEll 4447    := by decide +kernel
private theorem c4447_nsq   : NSqChkSq 4447   := by decide +kernel
private theorem c4447_har   : HArithChkSq 4447 := by decide +kernel
private theorem c4447_r     : LeafR 4447      := by decide +kernel
private theorem c4447_e'    : LeafE' 4447     := by decide +kernel
private theorem c4447_f1    : LeafF1 4447     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4447_s2    : S2ChkSq 4447    := by decide +kernel
private theorem c4447_s3    : S3ChkSq 4447    := by decide +kernel
private theorem c4447_iso   : LeafIso 4447    := by decide +kernel
private theorem c4447_nof2  : NoF2ChkSq 4447  := by decide +kernel
private theorem c4447_nof3  : NoF3ChkSq 4447  := by decide +kernel
private theorem c4447_nof4z : NoF4zChkSq 4447 := by decide +kernel
theorem C'_4447 : C' 4447 :=
  ⟨c4447_sqf, c4447_range, c4447_ell, leafNSq_of_sq c4447_nsq, leafHAr_of_sq c4447_har,
   c4447_r, c4447_e', c4447_f1, leafS2_of_sq c4447_s2, leafS3_of_sq c4447_s3,
   c4447_iso, leafR8_of_sq c4447_nof2 c4447_nof3 c4447_nof4z⟩
theorem not_tile'_4447 (D : CongruentDissection 4447) : False :=
  not_tile_of_conditions' 4447 C'_4447 D

private theorem c4449_sqf   : LeafSqf 4449   := by decide +kernel
private theorem c4449_range : LeafRange 4449  := by decide +kernel
private theorem c4449_ell   : LeafEll 4449    := by decide +kernel
private theorem c4449_nsq   : NSqChkSq 4449   := by decide +kernel
private theorem c4449_har   : HArithChkSq 4449 := by decide +kernel
private theorem c4449_r     : LeafR 4449      := by decide +kernel
private theorem c4449_e'    : LeafE' 4449     := by decide +kernel
private theorem c4449_f1    : LeafF1 4449     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4449_s2    : S2ChkSq 4449    := by decide +kernel
private theorem c4449_s3    : S3ChkSq 4449    := by decide +kernel
private theorem c4449_iso   : LeafIso 4449    := by decide +kernel
private theorem c4449_nof2  : NoF2ChkSq 4449  := by decide +kernel
private theorem c4449_nof3  : NoF3ChkSq 4449  := by decide +kernel
private theorem c4449_nof4z : NoF4zChkSq 4449 := by decide +kernel
theorem C'_4449 : C' 4449 :=
  ⟨c4449_sqf, c4449_range, c4449_ell, leafNSq_of_sq c4449_nsq, leafHAr_of_sq c4449_har,
   c4449_r, c4449_e', c4449_f1, leafS2_of_sq c4449_s2, leafS3_of_sq c4449_s3,
   c4449_iso, leafR8_of_sq c4449_nof2 c4449_nof3 c4449_nof4z⟩
theorem not_tile'_4449 (D : CongruentDissection 4449) : False :=
  not_tile_of_conditions' 4449 C'_4449 D

private theorem c4451_sqf   : LeafSqf 4451   := by decide +kernel
private theorem c4451_range : LeafRange 4451  := by decide +kernel
private theorem c4451_ell   : LeafEll 4451    := by decide +kernel
private theorem c4451_nsq   : NSqChkSq 4451   := by decide +kernel
private theorem c4451_har   : HArithChkSq 4451 := by decide +kernel
private theorem c4451_r     : LeafR 4451      := by decide +kernel
private theorem c4451_e'    : LeafE' 4451     := by decide +kernel
private theorem c4451_f1    : LeafF1 4451     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4451_s2    : S2ChkSq 4451    := by decide +kernel
private theorem c4451_s3    : S3ChkSq 4451    := by decide +kernel
private theorem c4451_iso   : LeafIso 4451    := by decide +kernel
private theorem c4451_nof2  : NoF2ChkSq 4451  := by decide +kernel
private theorem c4451_nof3  : NoF3ChkSq 4451  := by decide +kernel
private theorem c4451_nof4z : NoF4zChkSq 4451 := by decide +kernel
theorem C'_4451 : C' 4451 :=
  ⟨c4451_sqf, c4451_range, c4451_ell, leafNSq_of_sq c4451_nsq, leafHAr_of_sq c4451_har,
   c4451_r, c4451_e', c4451_f1, leafS2_of_sq c4451_s2, leafS3_of_sq c4451_s3,
   c4451_iso, leafR8_of_sq c4451_nof2 c4451_nof3 c4451_nof4z⟩
theorem not_tile'_4451 (D : CongruentDissection 4451) : False :=
  not_tile_of_conditions' 4451 C'_4451 D

end Erdos634.Draft.AllN2
