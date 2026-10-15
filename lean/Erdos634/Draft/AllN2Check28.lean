/- AllN2Check28: N = 1169, 1191, 1195, 1199, 1203
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1169_sqf   : LeafSqf 1169   := by decide +kernel
private theorem c1169_range : LeafRange 1169  := by decide +kernel
private theorem c1169_ell   : LeafEll 1169    := by decide +kernel
private theorem c1169_nsq   : NSqChkSq 1169   := by decide +kernel
private theorem c1169_har   : HArithChkSq 1169 := by decide +kernel
private theorem c1169_r     : LeafR 1169      := by decide +kernel
private theorem c1169_e'    : LeafE' 1169     := by decide +kernel
private theorem c1169_f1    : LeafF1 1169     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1169_s2    : S2ChkSq 1169    := by decide +kernel
private theorem c1169_s3    : S3ChkSq 1169    := by decide +kernel
private theorem c1169_iso   : LeafIso 1169    := by decide +kernel
private theorem c1169_nof2  : NoF2ChkSq 1169  := by decide +kernel
private theorem c1169_nof3  : NoF3ChkSq 1169  := by decide +kernel
private theorem c1169_nof4z : NoF4zChkSq 1169 := by decide +kernel
theorem C'_1169 : C' 1169 :=
  ⟨c1169_sqf, c1169_range, c1169_ell, leafNSq_of_sq c1169_nsq, leafHAr_of_sq c1169_har,
   c1169_r, c1169_e', c1169_f1, leafS2_of_sq c1169_s2, leafS3_of_sq c1169_s3,
   c1169_iso, leafR8_of_sq c1169_nof2 c1169_nof3 c1169_nof4z⟩
theorem not_tile'_1169 (D : CongruentDissection 1169) : False :=
  not_tile_of_conditions' 1169 C'_1169 D

private theorem c1191_sqf   : LeafSqf 1191   := by decide +kernel
private theorem c1191_range : LeafRange 1191  := by decide +kernel
private theorem c1191_ell   : LeafEll 1191    := by decide +kernel
private theorem c1191_nsq   : NSqChkSq 1191   := by decide +kernel
private theorem c1191_har   : HArithChkSq 1191 := by decide +kernel
private theorem c1191_r     : LeafR 1191      := by decide +kernel
private theorem c1191_e'    : LeafE' 1191     := by decide +kernel
private theorem c1191_f1    : LeafF1 1191     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1191_s2    : S2ChkSq 1191    := by decide +kernel
private theorem c1191_s3    : S3ChkSq 1191    := by decide +kernel
private theorem c1191_iso   : LeafIso 1191    := by decide +kernel
private theorem c1191_nof2  : NoF2ChkSq 1191  := by decide +kernel
private theorem c1191_nof3  : NoF3ChkSq 1191  := by decide +kernel
private theorem c1191_nof4z : NoF4zChkSq 1191 := by decide +kernel
theorem C'_1191 : C' 1191 :=
  ⟨c1191_sqf, c1191_range, c1191_ell, leafNSq_of_sq c1191_nsq, leafHAr_of_sq c1191_har,
   c1191_r, c1191_e', c1191_f1, leafS2_of_sq c1191_s2, leafS3_of_sq c1191_s3,
   c1191_iso, leafR8_of_sq c1191_nof2 c1191_nof3 c1191_nof4z⟩
theorem not_tile'_1191 (D : CongruentDissection 1191) : False :=
  not_tile_of_conditions' 1191 C'_1191 D

private theorem c1195_sqf   : LeafSqf 1195   := by decide +kernel
private theorem c1195_range : LeafRange 1195  := by decide +kernel
private theorem c1195_ell   : LeafEll 1195    := by decide +kernel
private theorem c1195_nsq   : NSqChkSq 1195   := by decide +kernel
private theorem c1195_har   : HArithChkSq 1195 := by decide +kernel
private theorem c1195_r     : LeafR 1195      := by decide +kernel
private theorem c1195_e'    : LeafE' 1195     := by decide +kernel
private theorem c1195_f1    : LeafF1 1195     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1195_s2    : S2ChkSq 1195    := by decide +kernel
private theorem c1195_s3    : S3ChkSq 1195    := by decide +kernel
private theorem c1195_iso   : LeafIso 1195    := by decide +kernel
private theorem c1195_nof2  : NoF2ChkSq 1195  := by decide +kernel
private theorem c1195_nof3  : NoF3ChkSq 1195  := by decide +kernel
private theorem c1195_nof4z : NoF4zChkSq 1195 := by decide +kernel
theorem C'_1195 : C' 1195 :=
  ⟨c1195_sqf, c1195_range, c1195_ell, leafNSq_of_sq c1195_nsq, leafHAr_of_sq c1195_har,
   c1195_r, c1195_e', c1195_f1, leafS2_of_sq c1195_s2, leafS3_of_sq c1195_s3,
   c1195_iso, leafR8_of_sq c1195_nof2 c1195_nof3 c1195_nof4z⟩
theorem not_tile'_1195 (D : CongruentDissection 1195) : False :=
  not_tile_of_conditions' 1195 C'_1195 D

private theorem c1199_sqf   : LeafSqf 1199   := by decide +kernel
private theorem c1199_range : LeafRange 1199  := by decide +kernel
private theorem c1199_ell   : LeafEll 1199    := by decide +kernel
private theorem c1199_nsq   : NSqChkSq 1199   := by decide +kernel
private theorem c1199_har   : HArithChkSq 1199 := by decide +kernel
private theorem c1199_r     : LeafR 1199      := by decide +kernel
private theorem c1199_e'    : LeafE' 1199     := by decide +kernel
private theorem c1199_f1    : LeafF1 1199     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1199_s2    : S2ChkSq 1199    := by decide +kernel
private theorem c1199_s3    : S3ChkSq 1199    := by decide +kernel
private theorem c1199_iso   : LeafIso 1199    := by decide +kernel
private theorem c1199_nof2  : NoF2ChkSq 1199  := by decide +kernel
private theorem c1199_nof3  : NoF3ChkSq 1199  := by decide +kernel
private theorem c1199_nof4z : NoF4zChkSq 1199 := by decide +kernel
theorem C'_1199 : C' 1199 :=
  ⟨c1199_sqf, c1199_range, c1199_ell, leafNSq_of_sq c1199_nsq, leafHAr_of_sq c1199_har,
   c1199_r, c1199_e', c1199_f1, leafS2_of_sq c1199_s2, leafS3_of_sq c1199_s3,
   c1199_iso, leafR8_of_sq c1199_nof2 c1199_nof3 c1199_nof4z⟩
theorem not_tile'_1199 (D : CongruentDissection 1199) : False :=
  not_tile_of_conditions' 1199 C'_1199 D

private theorem c1203_sqf   : LeafSqf 1203   := by decide +kernel
private theorem c1203_range : LeafRange 1203  := by decide +kernel
private theorem c1203_ell   : LeafEll 1203    := by decide +kernel
private theorem c1203_nsq   : NSqChkSq 1203   := by decide +kernel
private theorem c1203_har   : HArithChkSq 1203 := by decide +kernel
private theorem c1203_r     : LeafR 1203      := by decide +kernel
private theorem c1203_e'    : LeafE' 1203     := by decide +kernel
private theorem c1203_f1    : LeafF1 1203     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1203_s2    : S2ChkSq 1203    := by decide +kernel
private theorem c1203_s3    : S3ChkSq 1203    := by decide +kernel
private theorem c1203_iso   : LeafIso 1203    := by decide +kernel
private theorem c1203_nof2  : NoF2ChkSq 1203  := by decide +kernel
private theorem c1203_nof3  : NoF3ChkSq 1203  := by decide +kernel
private theorem c1203_nof4z : NoF4zChkSq 1203 := by decide +kernel
theorem C'_1203 : C' 1203 :=
  ⟨c1203_sqf, c1203_range, c1203_ell, leafNSq_of_sq c1203_nsq, leafHAr_of_sq c1203_har,
   c1203_r, c1203_e', c1203_f1, leafS2_of_sq c1203_s2, leafS3_of_sq c1203_s3,
   c1203_iso, leafR8_of_sq c1203_nof2 c1203_nof3 c1203_nof4z⟩
theorem not_tile'_1203 (D : CongruentDissection 1203) : False :=
  not_tile_of_conditions' 1203 C'_1203 D

end Erdos634.Draft.AllN2
