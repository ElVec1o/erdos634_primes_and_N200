/- AllN2Check20b: N = 831, 835, 843, 849, 879.
   C' N = true for each. Not in any realizable family. No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c831_sqf   : LeafSqf 831   := by decide +kernel
private theorem c831_range : LeafRange 831  := by decide +kernel
private theorem c831_ell   : LeafEll 831    := by decide +kernel
private theorem c831_nsq   : NSqChkSq 831   := by decide +kernel
private theorem c831_har   : HArithChkSq 831 := by decide +kernel
private theorem c831_r     : LeafR 831      := by decide +kernel
private theorem c831_e'    : LeafE' 831     := by decide +kernel
private theorem c831_f1    : LeafF1 831     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c831_s2    : S2ChkSq 831    := by decide +kernel
private theorem c831_s3    : S3ChkSq 831    := by decide +kernel
private theorem c831_iso   : LeafIso 831    := by decide +kernel
private theorem c831_nof2  : NoF2ChkSq 831  := by decide +kernel
private theorem c831_nof3  : NoF3ChkSq 831  := by decide +kernel
private theorem c831_nof4z : NoF4zChkSq 831 := by decide +kernel
theorem C'_831 : C' 831 :=
  ⟨c831_sqf, c831_range, c831_ell, leafNSq_of_sq c831_nsq, leafHAr_of_sq c831_har,
   c831_r, c831_e', c831_f1, leafS2_of_sq c831_s2, leafS3_of_sq c831_s3,
   c831_iso, leafR8_of_sq c831_nof2 c831_nof3 c831_nof4z⟩
theorem not_tile'_831 (D : CongruentDissection 831) : False :=
  not_tile_of_conditions' 831 C'_831 D

private theorem c835_sqf   : LeafSqf 835   := by decide +kernel
private theorem c835_range : LeafRange 835  := by decide +kernel
private theorem c835_ell   : LeafEll 835    := by decide +kernel
private theorem c835_nsq   : NSqChkSq 835   := by decide +kernel
private theorem c835_har   : HArithChkSq 835 := by decide +kernel
private theorem c835_r     : LeafR 835      := by decide +kernel
private theorem c835_e'    : LeafE' 835     := by decide +kernel
private theorem c835_f1    : LeafF1 835     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c835_s2    : S2ChkSq 835    := by decide +kernel
private theorem c835_s3    : S3ChkSq 835    := by decide +kernel
private theorem c835_iso   : LeafIso 835    := by decide +kernel
private theorem c835_nof2  : NoF2ChkSq 835  := by decide +kernel
private theorem c835_nof3  : NoF3ChkSq 835  := by decide +kernel
private theorem c835_nof4z : NoF4zChkSq 835 := by decide +kernel
theorem C'_835 : C' 835 :=
  ⟨c835_sqf, c835_range, c835_ell, leafNSq_of_sq c835_nsq, leafHAr_of_sq c835_har,
   c835_r, c835_e', c835_f1, leafS2_of_sq c835_s2, leafS3_of_sq c835_s3,
   c835_iso, leafR8_of_sq c835_nof2 c835_nof3 c835_nof4z⟩
theorem not_tile'_835 (D : CongruentDissection 835) : False :=
  not_tile_of_conditions' 835 C'_835 D

private theorem c843_sqf   : LeafSqf 843   := by decide +kernel
private theorem c843_range : LeafRange 843  := by decide +kernel
private theorem c843_ell   : LeafEll 843    := by decide +kernel
private theorem c843_nsq   : NSqChkSq 843   := by decide +kernel
private theorem c843_har   : HArithChkSq 843 := by decide +kernel
private theorem c843_r     : LeafR 843      := by decide +kernel
private theorem c843_e'    : LeafE' 843     := by decide +kernel
private theorem c843_f1    : LeafF1 843     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c843_s2    : S2ChkSq 843    := by decide +kernel
private theorem c843_s3    : S3ChkSq 843    := by decide +kernel
private theorem c843_iso   : LeafIso 843    := by decide +kernel
private theorem c843_nof2  : NoF2ChkSq 843  := by decide +kernel
private theorem c843_nof3  : NoF3ChkSq 843  := by decide +kernel
private theorem c843_nof4z : NoF4zChkSq 843 := by decide +kernel
theorem C'_843 : C' 843 :=
  ⟨c843_sqf, c843_range, c843_ell, leafNSq_of_sq c843_nsq, leafHAr_of_sq c843_har,
   c843_r, c843_e', c843_f1, leafS2_of_sq c843_s2, leafS3_of_sq c843_s3,
   c843_iso, leafR8_of_sq c843_nof2 c843_nof3 c843_nof4z⟩
theorem not_tile'_843 (D : CongruentDissection 843) : False :=
  not_tile_of_conditions' 843 C'_843 D

private theorem c849_sqf   : LeafSqf 849   := by decide +kernel
private theorem c849_range : LeafRange 849  := by decide +kernel
private theorem c849_ell   : LeafEll 849    := by decide +kernel
private theorem c849_nsq   : NSqChkSq 849   := by decide +kernel
private theorem c849_har   : HArithChkSq 849 := by decide +kernel
private theorem c849_r     : LeafR 849      := by decide +kernel
private theorem c849_e'    : LeafE' 849     := by decide +kernel
private theorem c849_f1    : LeafF1 849     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c849_s2    : S2ChkSq 849    := by decide +kernel
private theorem c849_s3    : S3ChkSq 849    := by decide +kernel
private theorem c849_iso   : LeafIso 849    := by decide +kernel
private theorem c849_nof2  : NoF2ChkSq 849  := by decide +kernel
private theorem c849_nof3  : NoF3ChkSq 849  := by decide +kernel
private theorem c849_nof4z : NoF4zChkSq 849 := by decide +kernel
theorem C'_849 : C' 849 :=
  ⟨c849_sqf, c849_range, c849_ell, leafNSq_of_sq c849_nsq, leafHAr_of_sq c849_har,
   c849_r, c849_e', c849_f1, leafS2_of_sq c849_s2, leafS3_of_sq c849_s3,
   c849_iso, leafR8_of_sq c849_nof2 c849_nof3 c849_nof4z⟩
theorem not_tile'_849 (D : CongruentDissection 849) : False :=
  not_tile_of_conditions' 849 C'_849 D

private theorem c879_sqf   : LeafSqf 879   := by decide +kernel
private theorem c879_range : LeafRange 879  := by decide +kernel
private theorem c879_ell   : LeafEll 879    := by decide +kernel
private theorem c879_nsq   : NSqChkSq 879   := by decide +kernel
private theorem c879_har   : HArithChkSq 879 := by decide +kernel
private theorem c879_r     : LeafR 879      := by decide +kernel
private theorem c879_e'    : LeafE' 879     := by decide +kernel
private theorem c879_f1    : LeafF1 879     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c879_s2    : S2ChkSq 879    := by decide +kernel
private theorem c879_s3    : S3ChkSq 879    := by decide +kernel
private theorem c879_iso   : LeafIso 879    := by decide +kernel
private theorem c879_nof2  : NoF2ChkSq 879  := by decide +kernel
private theorem c879_nof3  : NoF3ChkSq 879  := by decide +kernel
private theorem c879_nof4z : NoF4zChkSq 879 := by decide +kernel
theorem C'_879 : C' 879 :=
  ⟨c879_sqf, c879_range, c879_ell, leafNSq_of_sq c879_nsq, leafHAr_of_sq c879_har,
   c879_r, c879_e', c879_f1, leafS2_of_sq c879_s2, leafS3_of_sq c879_s3,
   c879_iso, leafR8_of_sq c879_nof2 c879_nof3 c879_nof4z⟩
theorem not_tile'_879 (D : CongruentDissection 879) : False :=
  not_tile_of_conditions' 879 C'_879 D

end Erdos634.Draft.AllN2
