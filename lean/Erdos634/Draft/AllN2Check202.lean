/- AllN2Check202: N = 3931, 3935, 3937, 3938, 3941
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3931_sqf   : LeafSqf 3931   := by decide +kernel
private theorem c3931_range : LeafRange 3931  := by decide +kernel
private theorem c3931_ell   : LeafEll 3931    := by decide +kernel
private theorem c3931_nsq   : NSqChkSq 3931   := by decide +kernel
private theorem c3931_har   : HArithChkSq 3931 := by decide +kernel
private theorem c3931_r     : LeafR 3931      := by decide +kernel
private theorem c3931_e'    : LeafE' 3931     := by decide +kernel
private theorem c3931_f1    : LeafF1 3931     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3931_s2    : S2ChkSq 3931    := by decide +kernel
private theorem c3931_s3    : S3ChkSq 3931    := by decide +kernel
private theorem c3931_iso   : LeafIso 3931    := by decide +kernel
private theorem c3931_nof2  : NoF2ChkSq 3931  := by decide +kernel
private theorem c3931_nof3  : NoF3ChkSq 3931  := by decide +kernel
private theorem c3931_nof4z : NoF4zChkSq 3931 := by decide +kernel
theorem C'_3931 : C' 3931 :=
  ⟨c3931_sqf, c3931_range, c3931_ell, leafNSq_of_sq c3931_nsq, leafHAr_of_sq c3931_har,
   c3931_r, c3931_e', c3931_f1, leafS2_of_sq c3931_s2, leafS3_of_sq c3931_s3,
   c3931_iso, leafR8_of_sq c3931_nof2 c3931_nof3 c3931_nof4z⟩
theorem not_tile'_3931 (D : CongruentDissection 3931) : False :=
  not_tile_of_conditions' 3931 C'_3931 D

private theorem c3935_sqf   : LeafSqf 3935   := by decide +kernel
private theorem c3935_range : LeafRange 3935  := by decide +kernel
private theorem c3935_ell   : LeafEll 3935    := by decide +kernel
private theorem c3935_nsq   : NSqChkSq 3935   := by decide +kernel
private theorem c3935_har   : HArithChkSq 3935 := by decide +kernel
private theorem c3935_r     : LeafR 3935      := by decide +kernel
private theorem c3935_e'    : LeafE' 3935     := by decide +kernel
private theorem c3935_f1    : LeafF1 3935     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3935_s2    : S2ChkSq 3935    := by decide +kernel
private theorem c3935_s3    : S3ChkSq 3935    := by decide +kernel
private theorem c3935_iso   : LeafIso 3935    := by decide +kernel
private theorem c3935_nof2  : NoF2ChkSq 3935  := by decide +kernel
private theorem c3935_nof3  : NoF3ChkSq 3935  := by decide +kernel
private theorem c3935_nof4z : NoF4zChkSq 3935 := by decide +kernel
theorem C'_3935 : C' 3935 :=
  ⟨c3935_sqf, c3935_range, c3935_ell, leafNSq_of_sq c3935_nsq, leafHAr_of_sq c3935_har,
   c3935_r, c3935_e', c3935_f1, leafS2_of_sq c3935_s2, leafS3_of_sq c3935_s3,
   c3935_iso, leafR8_of_sq c3935_nof2 c3935_nof3 c3935_nof4z⟩
theorem not_tile'_3935 (D : CongruentDissection 3935) : False :=
  not_tile_of_conditions' 3935 C'_3935 D

private theorem c3937_sqf   : LeafSqf 3937   := by decide +kernel
private theorem c3937_range : LeafRange 3937  := by decide +kernel
private theorem c3937_ell   : LeafEll 3937    := by decide +kernel
private theorem c3937_nsq   : NSqChkSq 3937   := by decide +kernel
private theorem c3937_har   : HArithChkSq 3937 := by decide +kernel
private theorem c3937_r     : LeafR 3937      := by decide +kernel
private theorem c3937_e'    : LeafE' 3937     := by decide +kernel
private theorem c3937_f1    : LeafF1 3937     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3937_s2    : S2ChkSq 3937    := by decide +kernel
private theorem c3937_s3    : S3ChkSq 3937    := by decide +kernel
private theorem c3937_iso   : LeafIso 3937    := by decide +kernel
private theorem c3937_nof2  : NoF2ChkSq 3937  := by decide +kernel
private theorem c3937_nof3  : NoF3ChkSq 3937  := by decide +kernel
private theorem c3937_nof4z : NoF4zChkSq 3937 := by decide +kernel
theorem C'_3937 : C' 3937 :=
  ⟨c3937_sqf, c3937_range, c3937_ell, leafNSq_of_sq c3937_nsq, leafHAr_of_sq c3937_har,
   c3937_r, c3937_e', c3937_f1, leafS2_of_sq c3937_s2, leafS3_of_sq c3937_s3,
   c3937_iso, leafR8_of_sq c3937_nof2 c3937_nof3 c3937_nof4z⟩
theorem not_tile'_3937 (D : CongruentDissection 3937) : False :=
  not_tile_of_conditions' 3937 C'_3937 D

private theorem c3938_sqf   : LeafSqf 3938   := by decide +kernel
private theorem c3938_range : LeafRange 3938  := by decide +kernel
private theorem c3938_ell   : LeafEll 3938    := by decide +kernel
private theorem c3938_nsq   : NSqChkSq 3938   := by decide +kernel
private theorem c3938_har   : HArithChkSq 3938 := by decide +kernel
private theorem c3938_r     : LeafR 3938      := by decide +kernel
private theorem c3938_e'    : LeafE' 3938     := by decide +kernel
private theorem c3938_f1    : LeafF1 3938     := Or.inl (by decide)
private theorem c3938_s2    : S2ChkSq 3938    := by decide +kernel
private theorem c3938_s3    : S3ChkSq 3938    := by decide +kernel
private theorem c3938_iso   : LeafIso 3938    := by decide +kernel
private theorem c3938_nof2  : NoF2ChkSq 3938  := by decide +kernel
private theorem c3938_nof3  : NoF3ChkSq 3938  := by decide +kernel
private theorem c3938_nof4z : NoF4zChkSq 3938 := by decide +kernel
theorem C'_3938 : C' 3938 :=
  ⟨c3938_sqf, c3938_range, c3938_ell, leafNSq_of_sq c3938_nsq, leafHAr_of_sq c3938_har,
   c3938_r, c3938_e', c3938_f1, leafS2_of_sq c3938_s2, leafS3_of_sq c3938_s3,
   c3938_iso, leafR8_of_sq c3938_nof2 c3938_nof3 c3938_nof4z⟩
theorem not_tile'_3938 (D : CongruentDissection 3938) : False :=
  not_tile_of_conditions' 3938 C'_3938 D

private theorem c3941_sqf   : LeafSqf 3941   := by decide +kernel
private theorem c3941_range : LeafRange 3941  := by decide +kernel
private theorem c3941_ell   : LeafEll 3941    := by decide +kernel
private theorem c3941_nsq   : NSqChkSq 3941   := by decide +kernel
private theorem c3941_har   : HArithChkSq 3941 := by decide +kernel
private theorem c3941_r     : LeafR 3941      := by decide +kernel
private theorem c3941_e'    : LeafE' 3941     := by decide +kernel
private theorem c3941_f1    : LeafF1 3941     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3941_s2    : S2ChkSq 3941    := by decide +kernel
private theorem c3941_s3    : S3ChkSq 3941    := by decide +kernel
private theorem c3941_iso   : LeafIso 3941    := by decide +kernel
private theorem c3941_nof2  : NoF2ChkSq 3941  := by decide +kernel
private theorem c3941_nof3  : NoF3ChkSq 3941  := by decide +kernel
private theorem c3941_nof4z : NoF4zChkSq 3941 := by decide +kernel
theorem C'_3941 : C' 3941 :=
  ⟨c3941_sqf, c3941_range, c3941_ell, leafNSq_of_sq c3941_nsq, leafHAr_of_sq c3941_har,
   c3941_r, c3941_e', c3941_f1, leafS2_of_sq c3941_s2, leafS3_of_sq c3941_s3,
   c3941_iso, leafR8_of_sq c3941_nof2 c3941_nof3 c3941_nof4z⟩
theorem not_tile'_3941 (D : CongruentDissection 3941) : False :=
  not_tile_of_conditions' 3941 C'_3941 D

end Erdos634.Draft.AllN2
