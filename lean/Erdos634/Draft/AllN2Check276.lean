/- AllN2Check276: N = 4862, 4863, 4865, 4866, 4867
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4862_sqf   : LeafSqf 4862   := by decide +kernel
private theorem c4862_range : LeafRange 4862  := by decide +kernel
private theorem c4862_ell   : LeafEll 4862    := by decide +kernel
private theorem c4862_nsq   : NSqChkSq 4862   := by decide +kernel
private theorem c4862_har   : HArithChkSq 4862 := by decide +kernel
private theorem c4862_r     : LeafR 4862      := by decide +kernel
private theorem c4862_e'    : LeafE' 4862     := by decide +kernel
private theorem c4862_f1    : LeafF1 4862     := Or.inl (by decide)
private theorem c4862_s2    : S2ChkSq 4862    := by decide +kernel
private theorem c4862_s3    : S3ChkSq 4862    := by decide +kernel
private theorem c4862_iso   : LeafIso 4862    := by decide +kernel
private theorem c4862_nof2  : NoF2ChkSq 4862  := by decide +kernel
private theorem c4862_nof3  : NoF3ChkSq 4862  := by decide +kernel
private theorem c4862_nof4z : NoF4zChkSq 4862 := by decide +kernel
theorem C'_4862 : C' 4862 :=
  ⟨c4862_sqf, c4862_range, c4862_ell, leafNSq_of_sq c4862_nsq, leafHAr_of_sq c4862_har,
   c4862_r, c4862_e', c4862_f1, leafS2_of_sq c4862_s2, leafS3_of_sq c4862_s3,
   c4862_iso, leafR8_of_sq c4862_nof2 c4862_nof3 c4862_nof4z⟩
theorem not_tile'_4862 (D : CongruentDissection 4862) : False :=
  not_tile_of_conditions' 4862 C'_4862 D

private theorem c4863_sqf   : LeafSqf 4863   := by decide +kernel
private theorem c4863_range : LeafRange 4863  := by decide +kernel
private theorem c4863_ell   : LeafEll 4863    := by decide +kernel
private theorem c4863_nsq   : NSqChkSq 4863   := by decide +kernel
private theorem c4863_har   : HArithChkSq 4863 := by decide +kernel
private theorem c4863_r     : LeafR 4863      := by decide +kernel
private theorem c4863_e'    : LeafE' 4863     := by decide +kernel
private theorem c4863_f1    : LeafF1 4863     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4863_s2    : S2ChkSq 4863    := by decide +kernel
private theorem c4863_s3    : S3ChkSq 4863    := by decide +kernel
private theorem c4863_iso   : LeafIso 4863    := by decide +kernel
private theorem c4863_nof2  : NoF2ChkSq 4863  := by decide +kernel
private theorem c4863_nof3  : NoF3ChkSq 4863  := by decide +kernel
private theorem c4863_nof4z : NoF4zChkSq 4863 := by decide +kernel
theorem C'_4863 : C' 4863 :=
  ⟨c4863_sqf, c4863_range, c4863_ell, leafNSq_of_sq c4863_nsq, leafHAr_of_sq c4863_har,
   c4863_r, c4863_e', c4863_f1, leafS2_of_sq c4863_s2, leafS3_of_sq c4863_s3,
   c4863_iso, leafR8_of_sq c4863_nof2 c4863_nof3 c4863_nof4z⟩
theorem not_tile'_4863 (D : CongruentDissection 4863) : False :=
  not_tile_of_conditions' 4863 C'_4863 D

private theorem c4865_sqf   : LeafSqf 4865   := by decide +kernel
private theorem c4865_range : LeafRange 4865  := by decide +kernel
private theorem c4865_ell   : LeafEll 4865    := by decide +kernel
private theorem c4865_nsq   : NSqChkSq 4865   := by decide +kernel
private theorem c4865_har   : HArithChkSq 4865 := by decide +kernel
private theorem c4865_r     : LeafR 4865      := by decide +kernel
private theorem c4865_e'    : LeafE' 4865     := by decide +kernel
private theorem c4865_f1    : LeafF1 4865     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4865_s2    : S2ChkSq 4865    := by decide +kernel
private theorem c4865_s3    : S3ChkSq 4865    := by decide +kernel
private theorem c4865_iso   : LeafIso 4865    := by decide +kernel
private theorem c4865_nof2  : NoF2ChkSq 4865  := by decide +kernel
private theorem c4865_nof3  : NoF3ChkSq 4865  := by decide +kernel
private theorem c4865_nof4z : NoF4zChkSq 4865 := by decide +kernel
theorem C'_4865 : C' 4865 :=
  ⟨c4865_sqf, c4865_range, c4865_ell, leafNSq_of_sq c4865_nsq, leafHAr_of_sq c4865_har,
   c4865_r, c4865_e', c4865_f1, leafS2_of_sq c4865_s2, leafS3_of_sq c4865_s3,
   c4865_iso, leafR8_of_sq c4865_nof2 c4865_nof3 c4865_nof4z⟩
theorem not_tile'_4865 (D : CongruentDissection 4865) : False :=
  not_tile_of_conditions' 4865 C'_4865 D

private theorem c4866_sqf   : LeafSqf 4866   := by decide +kernel
private theorem c4866_range : LeafRange 4866  := by decide +kernel
private theorem c4866_ell   : LeafEll 4866    := by decide +kernel
private theorem c4866_nsq   : NSqChkSq 4866   := by decide +kernel
private theorem c4866_har   : HArithChkSq 4866 := by decide +kernel
private theorem c4866_r     : LeafR 4866      := by decide +kernel
private theorem c4866_e'    : LeafE' 4866     := by decide +kernel
private theorem c4866_f1    : LeafF1 4866     := Or.inl (by decide)
private theorem c4866_s2    : S2ChkSq 4866    := by decide +kernel
private theorem c4866_s3    : S3ChkSq 4866    := by decide +kernel
private theorem c4866_iso   : LeafIso 4866    := by decide +kernel
private theorem c4866_nof2  : NoF2ChkSq 4866  := by decide +kernel
private theorem c4866_nof3  : NoF3ChkSq 4866  := by decide +kernel
private theorem c4866_nof4z : NoF4zChkSq 4866 := by decide +kernel
theorem C'_4866 : C' 4866 :=
  ⟨c4866_sqf, c4866_range, c4866_ell, leafNSq_of_sq c4866_nsq, leafHAr_of_sq c4866_har,
   c4866_r, c4866_e', c4866_f1, leafS2_of_sq c4866_s2, leafS3_of_sq c4866_s3,
   c4866_iso, leafR8_of_sq c4866_nof2 c4866_nof3 c4866_nof4z⟩
theorem not_tile'_4866 (D : CongruentDissection 4866) : False :=
  not_tile_of_conditions' 4866 C'_4866 D

private theorem c4867_sqf   : LeafSqf 4867   := by decide +kernel
private theorem c4867_range : LeafRange 4867  := by decide +kernel
private theorem c4867_ell   : LeafEll 4867    := by decide +kernel
private theorem c4867_nsq   : NSqChkSq 4867   := by decide +kernel
private theorem c4867_har   : HArithChkSq 4867 := by decide +kernel
private theorem c4867_r     : LeafR 4867      := by decide +kernel
private theorem c4867_e'    : LeafE' 4867     := by decide +kernel
private theorem c4867_f1    : LeafF1 4867     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4867_s2    : S2ChkSq 4867    := by decide +kernel
private theorem c4867_s3    : S3ChkSq 4867    := by decide +kernel
private theorem c4867_iso   : LeafIso 4867    := by decide +kernel
private theorem c4867_nof2  : NoF2ChkSq 4867  := by decide +kernel
private theorem c4867_nof3  : NoF3ChkSq 4867  := by decide +kernel
private theorem c4867_nof4z : NoF4zChkSq 4867 := by decide +kernel
theorem C'_4867 : C' 4867 :=
  ⟨c4867_sqf, c4867_range, c4867_ell, leafNSq_of_sq c4867_nsq, leafHAr_of_sq c4867_har,
   c4867_r, c4867_e', c4867_f1, leafS2_of_sq c4867_s2, leafS3_of_sq c4867_s3,
   c4867_iso, leafR8_of_sq c4867_nof2 c4867_nof3 c4867_nof4z⟩
theorem not_tile'_4867 (D : CongruentDissection 4867) : False :=
  not_tile_of_conditions' 4867 C'_4867 D

end Erdos634.Draft.AllN2
