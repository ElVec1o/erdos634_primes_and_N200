/- AllN2Check187: N = 3727, 3731, 3734, 3738, 3739
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3727_sqf   : LeafSqf 3727   := by decide +kernel
private theorem c3727_range : LeafRange 3727  := by decide +kernel
private theorem c3727_ell   : LeafEll 3727    := by decide +kernel
private theorem c3727_nsq   : NSqChkSq 3727   := by decide +kernel
private theorem c3727_har   : HArithChkSq 3727 := by decide +kernel
private theorem c3727_r     : LeafR 3727      := by decide +kernel
private theorem c3727_e'    : LeafE' 3727     := by decide +kernel
private theorem c3727_f1    : LeafF1 3727     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3727_s2    : S2ChkSq 3727    := by decide +kernel
private theorem c3727_s3    : S3ChkSq 3727    := by decide +kernel
private theorem c3727_iso   : LeafIso 3727    := by decide +kernel
private theorem c3727_nof2  : NoF2ChkSq 3727  := by decide +kernel
private theorem c3727_nof3  : NoF3ChkSq 3727  := by decide +kernel
private theorem c3727_nof4z : NoF4zChkSq 3727 := by decide +kernel
theorem C'_3727 : C' 3727 :=
  ⟨c3727_sqf, c3727_range, c3727_ell, leafNSq_of_sq c3727_nsq, leafHAr_of_sq c3727_har,
   c3727_r, c3727_e', c3727_f1, leafS2_of_sq c3727_s2, leafS3_of_sq c3727_s3,
   c3727_iso, leafR8_of_sq c3727_nof2 c3727_nof3 c3727_nof4z⟩
theorem not_tile'_3727 (D : CongruentDissection 3727) : False :=
  not_tile_of_conditions' 3727 C'_3727 D

private theorem c3731_sqf   : LeafSqf 3731   := by decide +kernel
private theorem c3731_range : LeafRange 3731  := by decide +kernel
private theorem c3731_ell   : LeafEll 3731    := by decide +kernel
private theorem c3731_nsq   : NSqChkSq 3731   := by decide +kernel
private theorem c3731_har   : HArithChkSq 3731 := by decide +kernel
private theorem c3731_r     : LeafR 3731      := by decide +kernel
private theorem c3731_e'    : LeafE' 3731     := by decide +kernel
private theorem c3731_f1    : LeafF1 3731     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3731_s2    : S2ChkSq 3731    := by decide +kernel
private theorem c3731_s3    : S3ChkSq 3731    := by decide +kernel
private theorem c3731_iso   : LeafIso 3731    := by decide +kernel
private theorem c3731_nof2  : NoF2ChkSq 3731  := by decide +kernel
private theorem c3731_nof3  : NoF3ChkSq 3731  := by decide +kernel
private theorem c3731_nof4z : NoF4zChkSq 3731 := by decide +kernel
theorem C'_3731 : C' 3731 :=
  ⟨c3731_sqf, c3731_range, c3731_ell, leafNSq_of_sq c3731_nsq, leafHAr_of_sq c3731_har,
   c3731_r, c3731_e', c3731_f1, leafS2_of_sq c3731_s2, leafS3_of_sq c3731_s3,
   c3731_iso, leafR8_of_sq c3731_nof2 c3731_nof3 c3731_nof4z⟩
theorem not_tile'_3731 (D : CongruentDissection 3731) : False :=
  not_tile_of_conditions' 3731 C'_3731 D

private theorem c3734_sqf   : LeafSqf 3734   := by decide +kernel
private theorem c3734_range : LeafRange 3734  := by decide +kernel
private theorem c3734_ell   : LeafEll 3734    := by decide +kernel
private theorem c3734_nsq   : NSqChkSq 3734   := by decide +kernel
private theorem c3734_har   : HArithChkSq 3734 := by decide +kernel
private theorem c3734_r     : LeafR 3734      := by decide +kernel
private theorem c3734_e'    : LeafE' 3734     := by decide +kernel
private theorem c3734_f1    : LeafF1 3734     := Or.inl (by decide)
private theorem c3734_s2    : S2ChkSq 3734    := by decide +kernel
private theorem c3734_s3    : S3ChkSq 3734    := by decide +kernel
private theorem c3734_iso   : LeafIso 3734    := by decide +kernel
private theorem c3734_nof2  : NoF2ChkSq 3734  := by decide +kernel
private theorem c3734_nof3  : NoF3ChkSq 3734  := by decide +kernel
private theorem c3734_nof4z : NoF4zChkSq 3734 := by decide +kernel
theorem C'_3734 : C' 3734 :=
  ⟨c3734_sqf, c3734_range, c3734_ell, leafNSq_of_sq c3734_nsq, leafHAr_of_sq c3734_har,
   c3734_r, c3734_e', c3734_f1, leafS2_of_sq c3734_s2, leafS3_of_sq c3734_s3,
   c3734_iso, leafR8_of_sq c3734_nof2 c3734_nof3 c3734_nof4z⟩
theorem not_tile'_3734 (D : CongruentDissection 3734) : False :=
  not_tile_of_conditions' 3734 C'_3734 D

private theorem c3738_sqf   : LeafSqf 3738   := by decide +kernel
private theorem c3738_range : LeafRange 3738  := by decide +kernel
private theorem c3738_ell   : LeafEll 3738    := by decide +kernel
private theorem c3738_nsq   : NSqChkSq 3738   := by decide +kernel
private theorem c3738_har   : HArithChkSq 3738 := by decide +kernel
private theorem c3738_r     : LeafR 3738      := by decide +kernel
private theorem c3738_e'    : LeafE' 3738     := by decide +kernel
private theorem c3738_f1    : LeafF1 3738     := Or.inl (by decide)
private theorem c3738_s2    : S2ChkSq 3738    := by decide +kernel
private theorem c3738_s3    : S3ChkSq 3738    := by decide +kernel
private theorem c3738_iso   : LeafIso 3738    := by decide +kernel
private theorem c3738_nof2  : NoF2ChkSq 3738  := by decide +kernel
private theorem c3738_nof3  : NoF3ChkSq 3738  := by decide +kernel
private theorem c3738_nof4z : NoF4zChkSq 3738 := by decide +kernel
theorem C'_3738 : C' 3738 :=
  ⟨c3738_sqf, c3738_range, c3738_ell, leafNSq_of_sq c3738_nsq, leafHAr_of_sq c3738_har,
   c3738_r, c3738_e', c3738_f1, leafS2_of_sq c3738_s2, leafS3_of_sq c3738_s3,
   c3738_iso, leafR8_of_sq c3738_nof2 c3738_nof3 c3738_nof4z⟩
theorem not_tile'_3738 (D : CongruentDissection 3738) : False :=
  not_tile_of_conditions' 3738 C'_3738 D

private theorem c3739_sqf   : LeafSqf 3739   := by decide +kernel
private theorem c3739_range : LeafRange 3739  := by decide +kernel
private theorem c3739_ell   : LeafEll 3739    := by decide +kernel
private theorem c3739_nsq   : NSqChkSq 3739   := by decide +kernel
private theorem c3739_har   : HArithChkSq 3739 := by decide +kernel
private theorem c3739_r     : LeafR 3739      := by decide +kernel
private theorem c3739_e'    : LeafE' 3739     := by decide +kernel
private theorem c3739_f1    : LeafF1 3739     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3739_s2    : S2ChkSq 3739    := by decide +kernel
private theorem c3739_s3    : S3ChkSq 3739    := by decide +kernel
private theorem c3739_iso   : LeafIso 3739    := by decide +kernel
private theorem c3739_nof2  : NoF2ChkSq 3739  := by decide +kernel
private theorem c3739_nof3  : NoF3ChkSq 3739  := by decide +kernel
private theorem c3739_nof4z : NoF4zChkSq 3739 := by decide +kernel
theorem C'_3739 : C' 3739 :=
  ⟨c3739_sqf, c3739_range, c3739_ell, leafNSq_of_sq c3739_nsq, leafHAr_of_sq c3739_har,
   c3739_r, c3739_e', c3739_f1, leafS2_of_sq c3739_s2, leafS3_of_sq c3739_s3,
   c3739_iso, leafR8_of_sq c3739_nof2 c3739_nof3 c3739_nof4z⟩
theorem not_tile'_3739 (D : CongruentDissection 3739) : False :=
  not_tile_of_conditions' 3739 C'_3739 D

end Erdos634.Draft.AllN2
