/- AllN2Check268: N = 4766, 4769, 4771, 4774, 4781
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4766_sqf   : LeafSqf 4766   := by decide +kernel
private theorem c4766_range : LeafRange 4766  := by decide +kernel
private theorem c4766_ell   : LeafEll 4766    := by decide +kernel
private theorem c4766_nsq   : NSqChkSq 4766   := by decide +kernel
private theorem c4766_har   : HArithChkSq 4766 := by decide +kernel
private theorem c4766_r     : LeafR 4766      := by decide +kernel
private theorem c4766_e'    : LeafE' 4766     := by decide +kernel
private theorem c4766_f1    : LeafF1 4766     := Or.inl (by decide)
private theorem c4766_s2    : S2ChkSq 4766    := by decide +kernel
private theorem c4766_s3    : S3ChkSq 4766    := by decide +kernel
private theorem c4766_iso   : LeafIso 4766    := by decide +kernel
private theorem c4766_nof2  : NoF2ChkSq 4766  := by decide +kernel
private theorem c4766_nof3  : NoF3ChkSq 4766  := by decide +kernel
private theorem c4766_nof4z : NoF4zChkSq 4766 := by decide +kernel
theorem C'_4766 : C' 4766 :=
  ⟨c4766_sqf, c4766_range, c4766_ell, leafNSq_of_sq c4766_nsq, leafHAr_of_sq c4766_har,
   c4766_r, c4766_e', c4766_f1, leafS2_of_sq c4766_s2, leafS3_of_sq c4766_s3,
   c4766_iso, leafR8_of_sq c4766_nof2 c4766_nof3 c4766_nof4z⟩
theorem not_tile'_4766 (D : CongruentDissection 4766) : False :=
  not_tile_of_conditions' 4766 C'_4766 D

private theorem c4769_sqf   : LeafSqf 4769   := by decide +kernel
private theorem c4769_range : LeafRange 4769  := by decide +kernel
private theorem c4769_ell   : LeafEll 4769    := by decide +kernel
private theorem c4769_nsq   : NSqChkSq 4769   := by decide +kernel
private theorem c4769_har   : HArithChkSq 4769 := by decide +kernel
private theorem c4769_r     : LeafR 4769      := by decide +kernel
private theorem c4769_e'    : LeafE' 4769     := by decide +kernel
private theorem c4769_f1    : LeafF1 4769     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4769_s2    : S2ChkSq 4769    := by decide +kernel
private theorem c4769_s3    : S3ChkSq 4769    := by decide +kernel
private theorem c4769_iso   : LeafIso 4769    := by decide +kernel
private theorem c4769_nof2  : NoF2ChkSq 4769  := by decide +kernel
private theorem c4769_nof3  : NoF3ChkSq 4769  := by decide +kernel
private theorem c4769_nof4z : NoF4zChkSq 4769 := by decide +kernel
theorem C'_4769 : C' 4769 :=
  ⟨c4769_sqf, c4769_range, c4769_ell, leafNSq_of_sq c4769_nsq, leafHAr_of_sq c4769_har,
   c4769_r, c4769_e', c4769_f1, leafS2_of_sq c4769_s2, leafS3_of_sq c4769_s3,
   c4769_iso, leafR8_of_sq c4769_nof2 c4769_nof3 c4769_nof4z⟩
theorem not_tile'_4769 (D : CongruentDissection 4769) : False :=
  not_tile_of_conditions' 4769 C'_4769 D

private theorem c4771_sqf   : LeafSqf 4771   := by decide +kernel
private theorem c4771_range : LeafRange 4771  := by decide +kernel
private theorem c4771_ell   : LeafEll 4771    := by decide +kernel
private theorem c4771_nsq   : NSqChkSq 4771   := by decide +kernel
private theorem c4771_har   : HArithChkSq 4771 := by decide +kernel
private theorem c4771_r     : LeafR 4771      := by decide +kernel
private theorem c4771_e'    : LeafE' 4771     := by decide +kernel
private theorem c4771_f1    : LeafF1 4771     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4771_s2    : S2ChkSq 4771    := by decide +kernel
private theorem c4771_s3    : S3ChkSq 4771    := by decide +kernel
private theorem c4771_iso   : LeafIso 4771    := by decide +kernel
private theorem c4771_nof2  : NoF2ChkSq 4771  := by decide +kernel
private theorem c4771_nof3  : NoF3ChkSq 4771  := by decide +kernel
private theorem c4771_nof4z : NoF4zChkSq 4771 := by decide +kernel
theorem C'_4771 : C' 4771 :=
  ⟨c4771_sqf, c4771_range, c4771_ell, leafNSq_of_sq c4771_nsq, leafHAr_of_sq c4771_har,
   c4771_r, c4771_e', c4771_f1, leafS2_of_sq c4771_s2, leafS3_of_sq c4771_s3,
   c4771_iso, leafR8_of_sq c4771_nof2 c4771_nof3 c4771_nof4z⟩
theorem not_tile'_4771 (D : CongruentDissection 4771) : False :=
  not_tile_of_conditions' 4771 C'_4771 D

private theorem c4774_sqf   : LeafSqf 4774   := by decide +kernel
private theorem c4774_range : LeafRange 4774  := by decide +kernel
private theorem c4774_ell   : LeafEll 4774    := by decide +kernel
private theorem c4774_nsq   : NSqChkSq 4774   := by decide +kernel
private theorem c4774_har   : HArithChkSq 4774 := by decide +kernel
private theorem c4774_r     : LeafR 4774      := by decide +kernel
private theorem c4774_e'    : LeafE' 4774     := by decide +kernel
private theorem c4774_f1    : LeafF1 4774     := Or.inl (by decide)
private theorem c4774_s2    : S2ChkSq 4774    := by decide +kernel
private theorem c4774_s3    : S3ChkSq 4774    := by decide +kernel
private theorem c4774_iso   : LeafIso 4774    := by decide +kernel
private theorem c4774_nof2  : NoF2ChkSq 4774  := by decide +kernel
private theorem c4774_nof3  : NoF3ChkSq 4774  := by decide +kernel
private theorem c4774_nof4z : NoF4zChkSq 4774 := by decide +kernel
theorem C'_4774 : C' 4774 :=
  ⟨c4774_sqf, c4774_range, c4774_ell, leafNSq_of_sq c4774_nsq, leafHAr_of_sq c4774_har,
   c4774_r, c4774_e', c4774_f1, leafS2_of_sq c4774_s2, leafS3_of_sq c4774_s3,
   c4774_iso, leafR8_of_sq c4774_nof2 c4774_nof3 c4774_nof4z⟩
theorem not_tile'_4774 (D : CongruentDissection 4774) : False :=
  not_tile_of_conditions' 4774 C'_4774 D

private theorem c4781_sqf   : LeafSqf 4781   := by decide +kernel
private theorem c4781_range : LeafRange 4781  := by decide +kernel
private theorem c4781_ell   : LeafEll 4781    := by decide +kernel
private theorem c4781_nsq   : NSqChkSq 4781   := by decide +kernel
private theorem c4781_har   : HArithChkSq 4781 := by decide +kernel
private theorem c4781_r     : LeafR 4781      := by decide +kernel
private theorem c4781_e'    : LeafE' 4781     := by decide +kernel
private theorem c4781_f1    : LeafF1 4781     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4781_s2    : S2ChkSq 4781    := by decide +kernel
private theorem c4781_s3    : S3ChkSq 4781    := by decide +kernel
private theorem c4781_iso   : LeafIso 4781    := by decide +kernel
private theorem c4781_nof2  : NoF2ChkSq 4781  := by decide +kernel
private theorem c4781_nof3  : NoF3ChkSq 4781  := by decide +kernel
private theorem c4781_nof4z : NoF4zChkSq 4781 := by decide +kernel
theorem C'_4781 : C' 4781 :=
  ⟨c4781_sqf, c4781_range, c4781_ell, leafNSq_of_sq c4781_nsq, leafHAr_of_sq c4781_har,
   c4781_r, c4781_e', c4781_f1, leafS2_of_sq c4781_s2, leafS3_of_sq c4781_s3,
   c4781_iso, leafR8_of_sq c4781_nof2 c4781_nof3 c4781_nof4z⟩
theorem not_tile'_4781 (D : CongruentDissection 4781) : False :=
  not_tile_of_conditions' 4781 C'_4781 D

end Erdos634.Draft.AllN2
