/- AllN2Check18b: N = 681, 687, 695, 699, 707
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c681_sqf   : LeafSqf 681   := by decide +kernel
private theorem c681_range : LeafRange 681  := by decide +kernel
private theorem c681_ell   : LeafEll 681    := by decide +kernel
private theorem c681_nsq   : NSqChkSq 681   := by decide +kernel
private theorem c681_har   : HArithChkSq 681 := by decide +kernel
private theorem c681_r     : LeafR 681      := by decide +kernel
private theorem c681_e'    : LeafE' 681     := by decide +kernel
private theorem c681_f1    : LeafF1 681     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c681_s2    : S2ChkSq 681    := by decide +kernel
private theorem c681_s3    : S3ChkSq 681    := by decide +kernel
private theorem c681_iso   : LeafIso 681    := by decide +kernel
private theorem c681_nof2  : NoF2ChkSq 681  := by decide +kernel
private theorem c681_nof3  : NoF3ChkSq 681  := by decide +kernel
private theorem c681_nof4z : NoF4zChkSq 681 := by decide +kernel
theorem C'_681 : C' 681 :=
  ⟨c681_sqf, c681_range, c681_ell, leafNSq_of_sq c681_nsq, leafHAr_of_sq c681_har,
   c681_r, c681_e', c681_f1, leafS2_of_sq c681_s2, leafS3_of_sq c681_s3,
   c681_iso, leafR8_of_sq c681_nof2 c681_nof3 c681_nof4z⟩
theorem not_tile'_681 (D : CongruentDissection 681) : False :=
  not_tile_of_conditions' 681 C'_681 D

private theorem c687_sqf   : LeafSqf 687   := by decide +kernel
private theorem c687_range : LeafRange 687  := by decide +kernel
private theorem c687_ell   : LeafEll 687    := by decide +kernel
private theorem c687_nsq   : NSqChkSq 687   := by decide +kernel
private theorem c687_har   : HArithChkSq 687 := by decide +kernel
private theorem c687_r     : LeafR 687      := by decide +kernel
private theorem c687_e'    : LeafE' 687     := by decide +kernel
private theorem c687_f1    : LeafF1 687     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c687_s2    : S2ChkSq 687    := by decide +kernel
private theorem c687_s3    : S3ChkSq 687    := by decide +kernel
private theorem c687_iso   : LeafIso 687    := by decide +kernel
private theorem c687_nof2  : NoF2ChkSq 687  := by decide +kernel
private theorem c687_nof3  : NoF3ChkSq 687  := by decide +kernel
private theorem c687_nof4z : NoF4zChkSq 687 := by decide +kernel
theorem C'_687 : C' 687 :=
  ⟨c687_sqf, c687_range, c687_ell, leafNSq_of_sq c687_nsq, leafHAr_of_sq c687_har,
   c687_r, c687_e', c687_f1, leafS2_of_sq c687_s2, leafS3_of_sq c687_s3,
   c687_iso, leafR8_of_sq c687_nof2 c687_nof3 c687_nof4z⟩
theorem not_tile'_687 (D : CongruentDissection 687) : False :=
  not_tile_of_conditions' 687 C'_687 D

private theorem c695_sqf   : LeafSqf 695   := by decide +kernel
private theorem c695_range : LeafRange 695  := by decide +kernel
private theorem c695_ell   : LeafEll 695    := by decide +kernel
private theorem c695_nsq   : NSqChkSq 695   := by decide +kernel
private theorem c695_har   : HArithChkSq 695 := by decide +kernel
private theorem c695_r     : LeafR 695      := by decide +kernel
private theorem c695_e'    : LeafE' 695     := by decide +kernel
private theorem c695_f1    : LeafF1 695     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c695_s2    : S2ChkSq 695    := by decide +kernel
private theorem c695_s3    : S3ChkSq 695    := by decide +kernel
private theorem c695_iso   : LeafIso 695    := by decide +kernel
private theorem c695_nof2  : NoF2ChkSq 695  := by decide +kernel
private theorem c695_nof3  : NoF3ChkSq 695  := by decide +kernel
private theorem c695_nof4z : NoF4zChkSq 695 := by decide +kernel
theorem C'_695 : C' 695 :=
  ⟨c695_sqf, c695_range, c695_ell, leafNSq_of_sq c695_nsq, leafHAr_of_sq c695_har,
   c695_r, c695_e', c695_f1, leafS2_of_sq c695_s2, leafS3_of_sq c695_s3,
   c695_iso, leafR8_of_sq c695_nof2 c695_nof3 c695_nof4z⟩
theorem not_tile'_695 (D : CongruentDissection 695) : False :=
  not_tile_of_conditions' 695 C'_695 D

private theorem c699_sqf   : LeafSqf 699   := by decide +kernel
private theorem c699_range : LeafRange 699  := by decide +kernel
private theorem c699_ell   : LeafEll 699    := by decide +kernel
private theorem c699_nsq   : NSqChkSq 699   := by decide +kernel
private theorem c699_har   : HArithChkSq 699 := by decide +kernel
private theorem c699_r     : LeafR 699      := by decide +kernel
private theorem c699_e'    : LeafE' 699     := by decide +kernel
private theorem c699_f1    : LeafF1 699     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c699_s2    : S2ChkSq 699    := by decide +kernel
private theorem c699_s3    : S3ChkSq 699    := by decide +kernel
private theorem c699_iso   : LeafIso 699    := by decide +kernel
private theorem c699_nof2  : NoF2ChkSq 699  := by decide +kernel
private theorem c699_nof3  : NoF3ChkSq 699  := by decide +kernel
private theorem c699_nof4z : NoF4zChkSq 699 := by decide +kernel
theorem C'_699 : C' 699 :=
  ⟨c699_sqf, c699_range, c699_ell, leafNSq_of_sq c699_nsq, leafHAr_of_sq c699_har,
   c699_r, c699_e', c699_f1, leafS2_of_sq c699_s2, leafS3_of_sq c699_s3,
   c699_iso, leafR8_of_sq c699_nof2 c699_nof3 c699_nof4z⟩
theorem not_tile'_699 (D : CongruentDissection 699) : False :=
  not_tile_of_conditions' 699 C'_699 D

private theorem c707_sqf   : LeafSqf 707   := by decide +kernel
private theorem c707_range : LeafRange 707  := by decide +kernel
private theorem c707_ell   : LeafEll 707    := by decide +kernel
private theorem c707_nsq   : NSqChkSq 707   := by decide +kernel
private theorem c707_har   : HArithChkSq 707 := by decide +kernel
private theorem c707_r     : LeafR 707      := by decide +kernel
private theorem c707_e'    : LeafE' 707     := by decide +kernel
private theorem c707_f1    : LeafF1 707     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c707_s2    : S2ChkSq 707    := by decide +kernel
private theorem c707_s3    : S3ChkSq 707    := by decide +kernel
private theorem c707_iso   : LeafIso 707    := by decide +kernel
private theorem c707_nof2  : NoF2ChkSq 707  := by decide +kernel
private theorem c707_nof3  : NoF3ChkSq 707  := by decide +kernel
private theorem c707_nof4z : NoF4zChkSq 707 := by decide +kernel
theorem C'_707 : C' 707 :=
  ⟨c707_sqf, c707_range, c707_ell, leafNSq_of_sq c707_nsq, leafHAr_of_sq c707_har,
   c707_r, c707_e', c707_f1, leafS2_of_sq c707_s2, leafS3_of_sq c707_s3,
   c707_iso, leafR8_of_sq c707_nof2 c707_nof3 c707_nof4z⟩
theorem not_tile'_707 (D : CongruentDissection 707) : False :=
  not_tile_of_conditions' 707 C'_707 D

end Erdos634.Draft.AllN2
