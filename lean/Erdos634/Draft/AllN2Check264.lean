/- AllN2Check264: N = 4718, 4722, 4723, 4726, 4727
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4718_sqf   : LeafSqf 4718   := by decide +kernel
private theorem c4718_range : LeafRange 4718  := by decide +kernel
private theorem c4718_ell   : LeafEll 4718    := by decide +kernel
private theorem c4718_nsq   : NSqChkSq 4718   := by decide +kernel
private theorem c4718_har   : HArithChkSq 4718 := by decide +kernel
private theorem c4718_r     : LeafR 4718      := by decide +kernel
private theorem c4718_e'    : LeafE' 4718     := by decide +kernel
private theorem c4718_f1    : LeafF1 4718     := Or.inl (by decide)
private theorem c4718_s2    : S2ChkSq 4718    := by decide +kernel
private theorem c4718_s3    : S3ChkSq 4718    := by decide +kernel
private theorem c4718_iso   : LeafIso 4718    := by decide +kernel
private theorem c4718_nof2  : NoF2ChkSq 4718  := by decide +kernel
private theorem c4718_nof3  : NoF3ChkSq 4718  := by decide +kernel
private theorem c4718_nof4z : NoF4zChkSq 4718 := by decide +kernel
theorem C'_4718 : C' 4718 :=
  ⟨c4718_sqf, c4718_range, c4718_ell, leafNSq_of_sq c4718_nsq, leafHAr_of_sq c4718_har,
   c4718_r, c4718_e', c4718_f1, leafS2_of_sq c4718_s2, leafS3_of_sq c4718_s3,
   c4718_iso, leafR8_of_sq c4718_nof2 c4718_nof3 c4718_nof4z⟩
theorem not_tile'_4718 (D : CongruentDissection 4718) : False :=
  not_tile_of_conditions' 4718 C'_4718 D

private theorem c4722_sqf   : LeafSqf 4722   := by decide +kernel
private theorem c4722_range : LeafRange 4722  := by decide +kernel
private theorem c4722_ell   : LeafEll 4722    := by decide +kernel
private theorem c4722_nsq   : NSqChkSq 4722   := by decide +kernel
private theorem c4722_har   : HArithChkSq 4722 := by decide +kernel
private theorem c4722_r     : LeafR 4722      := by decide +kernel
private theorem c4722_e'    : LeafE' 4722     := by decide +kernel
private theorem c4722_f1    : LeafF1 4722     := Or.inl (by decide)
private theorem c4722_s2    : S2ChkSq 4722    := by decide +kernel
private theorem c4722_s3    : S3ChkSq 4722    := by decide +kernel
private theorem c4722_iso   : LeafIso 4722    := by decide +kernel
private theorem c4722_nof2  : NoF2ChkSq 4722  := by decide +kernel
private theorem c4722_nof3  : NoF3ChkSq 4722  := by decide +kernel
private theorem c4722_nof4z : NoF4zChkSq 4722 := by decide +kernel
theorem C'_4722 : C' 4722 :=
  ⟨c4722_sqf, c4722_range, c4722_ell, leafNSq_of_sq c4722_nsq, leafHAr_of_sq c4722_har,
   c4722_r, c4722_e', c4722_f1, leafS2_of_sq c4722_s2, leafS3_of_sq c4722_s3,
   c4722_iso, leafR8_of_sq c4722_nof2 c4722_nof3 c4722_nof4z⟩
theorem not_tile'_4722 (D : CongruentDissection 4722) : False :=
  not_tile_of_conditions' 4722 C'_4722 D

private theorem c4723_sqf   : LeafSqf 4723   := by decide +kernel
private theorem c4723_range : LeafRange 4723  := by decide +kernel
private theorem c4723_ell   : LeafEll 4723    := by decide +kernel
private theorem c4723_nsq   : NSqChkSq 4723   := by decide +kernel
private theorem c4723_har   : HArithChkSq 4723 := by decide +kernel
private theorem c4723_r     : LeafR 4723      := by decide +kernel
private theorem c4723_e'    : LeafE' 4723     := by decide +kernel
private theorem c4723_f1    : LeafF1 4723     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4723_s2    : S2ChkSq 4723    := by decide +kernel
private theorem c4723_s3    : S3ChkSq 4723    := by decide +kernel
private theorem c4723_iso   : LeafIso 4723    := by decide +kernel
private theorem c4723_nof2  : NoF2ChkSq 4723  := by decide +kernel
private theorem c4723_nof3  : NoF3ChkSq 4723  := by decide +kernel
private theorem c4723_nof4z : NoF4zChkSq 4723 := by decide +kernel
theorem C'_4723 : C' 4723 :=
  ⟨c4723_sqf, c4723_range, c4723_ell, leafNSq_of_sq c4723_nsq, leafHAr_of_sq c4723_har,
   c4723_r, c4723_e', c4723_f1, leafS2_of_sq c4723_s2, leafS3_of_sq c4723_s3,
   c4723_iso, leafR8_of_sq c4723_nof2 c4723_nof3 c4723_nof4z⟩
theorem not_tile'_4723 (D : CongruentDissection 4723) : False :=
  not_tile_of_conditions' 4723 C'_4723 D

private theorem c4726_sqf   : LeafSqf 4726   := by decide +kernel
private theorem c4726_range : LeafRange 4726  := by decide +kernel
private theorem c4726_ell   : LeafEll 4726    := by decide +kernel
private theorem c4726_nsq   : NSqChkSq 4726   := by decide +kernel
private theorem c4726_har   : HArithChkSq 4726 := by decide +kernel
private theorem c4726_r     : LeafR 4726      := by decide +kernel
private theorem c4726_e'    : LeafE' 4726     := by decide +kernel
private theorem c4726_f1    : LeafF1 4726     := Or.inl (by decide)
private theorem c4726_s2    : S2ChkSq 4726    := by decide +kernel
private theorem c4726_s3    : S3ChkSq 4726    := by decide +kernel
private theorem c4726_iso   : LeafIso 4726    := by decide +kernel
private theorem c4726_nof2  : NoF2ChkSq 4726  := by decide +kernel
private theorem c4726_nof3  : NoF3ChkSq 4726  := by decide +kernel
private theorem c4726_nof4z : NoF4zChkSq 4726 := by decide +kernel
theorem C'_4726 : C' 4726 :=
  ⟨c4726_sqf, c4726_range, c4726_ell, leafNSq_of_sq c4726_nsq, leafHAr_of_sq c4726_har,
   c4726_r, c4726_e', c4726_f1, leafS2_of_sq c4726_s2, leafS3_of_sq c4726_s3,
   c4726_iso, leafR8_of_sq c4726_nof2 c4726_nof3 c4726_nof4z⟩
theorem not_tile'_4726 (D : CongruentDissection 4726) : False :=
  not_tile_of_conditions' 4726 C'_4726 D

private theorem c4727_sqf   : LeafSqf 4727   := by decide +kernel
private theorem c4727_range : LeafRange 4727  := by decide +kernel
private theorem c4727_ell   : LeafEll 4727    := by decide +kernel
private theorem c4727_nsq   : NSqChkSq 4727   := by decide +kernel
private theorem c4727_har   : HArithChkSq 4727 := by decide +kernel
private theorem c4727_r     : LeafR 4727      := by decide +kernel
private theorem c4727_e'    : LeafE' 4727     := by decide +kernel
private theorem c4727_f1    : LeafF1 4727     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4727_s2    : S2ChkSq 4727    := by decide +kernel
private theorem c4727_s3    : S3ChkSq 4727    := by decide +kernel
private theorem c4727_iso   : LeafIso 4727    := by decide +kernel
private theorem c4727_nof2  : NoF2ChkSq 4727  := by decide +kernel
private theorem c4727_nof3  : NoF3ChkSq 4727  := by decide +kernel
private theorem c4727_nof4z : NoF4zChkSq 4727 := by decide +kernel
theorem C'_4727 : C' 4727 :=
  ⟨c4727_sqf, c4727_range, c4727_ell, leafNSq_of_sq c4727_nsq, leafHAr_of_sq c4727_har,
   c4727_r, c4727_e', c4727_f1, leafS2_of_sq c4727_s2, leafS3_of_sq c4727_s3,
   c4727_iso, leafR8_of_sq c4727_nof2 c4727_nof3 c4727_nof4z⟩
theorem not_tile'_4727 (D : CongruentDissection 4727) : False :=
  not_tile_of_conditions' 4727 C'_4727 D

end Erdos634.Draft.AllN2
