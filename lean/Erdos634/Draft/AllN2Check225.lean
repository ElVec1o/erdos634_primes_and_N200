/- AllN2Check225: N = 4238, 4242, 4243, 4246, 4247
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4238_sqf   : LeafSqf 4238   := by decide +kernel
private theorem c4238_range : LeafRange 4238  := by decide +kernel
private theorem c4238_ell   : LeafEll 4238    := by decide +kernel
private theorem c4238_nsq   : NSqChkSq 4238   := by decide +kernel
private theorem c4238_har   : HArithChkSq 4238 := by decide +kernel
private theorem c4238_r     : LeafR 4238      := by decide +kernel
private theorem c4238_e'    : LeafE' 4238     := by decide +kernel
private theorem c4238_f1    : LeafF1 4238     := Or.inl (by decide)
private theorem c4238_s2    : S2ChkSq 4238    := by decide +kernel
private theorem c4238_s3    : S3ChkSq 4238    := by decide +kernel
private theorem c4238_iso   : LeafIso 4238    := by decide +kernel
private theorem c4238_nof2  : NoF2ChkSq 4238  := by decide +kernel
private theorem c4238_nof3  : NoF3ChkSq 4238  := by decide +kernel
private theorem c4238_nof4z : NoF4zChkSq 4238 := by decide +kernel
theorem C'_4238 : C' 4238 :=
  ⟨c4238_sqf, c4238_range, c4238_ell, leafNSq_of_sq c4238_nsq, leafHAr_of_sq c4238_har,
   c4238_r, c4238_e', c4238_f1, leafS2_of_sq c4238_s2, leafS3_of_sq c4238_s3,
   c4238_iso, leafR8_of_sq c4238_nof2 c4238_nof3 c4238_nof4z⟩
theorem not_tile'_4238 (D : CongruentDissection 4238) : False :=
  not_tile_of_conditions' 4238 C'_4238 D

private theorem c4242_sqf   : LeafSqf 4242   := by decide +kernel
private theorem c4242_range : LeafRange 4242  := by decide +kernel
private theorem c4242_ell   : LeafEll 4242    := by decide +kernel
private theorem c4242_nsq   : NSqChkSq 4242   := by decide +kernel
private theorem c4242_har   : HArithChkSq 4242 := by decide +kernel
private theorem c4242_r     : LeafR 4242      := by decide +kernel
private theorem c4242_e'    : LeafE' 4242     := by decide +kernel
private theorem c4242_f1    : LeafF1 4242     := Or.inl (by decide)
private theorem c4242_s2    : S2ChkSq 4242    := by decide +kernel
private theorem c4242_s3    : S3ChkSq 4242    := by decide +kernel
private theorem c4242_iso   : LeafIso 4242    := by decide +kernel
private theorem c4242_nof2  : NoF2ChkSq 4242  := by decide +kernel
private theorem c4242_nof3  : NoF3ChkSq 4242  := by decide +kernel
private theorem c4242_nof4z : NoF4zChkSq 4242 := by decide +kernel
theorem C'_4242 : C' 4242 :=
  ⟨c4242_sqf, c4242_range, c4242_ell, leafNSq_of_sq c4242_nsq, leafHAr_of_sq c4242_har,
   c4242_r, c4242_e', c4242_f1, leafS2_of_sq c4242_s2, leafS3_of_sq c4242_s3,
   c4242_iso, leafR8_of_sq c4242_nof2 c4242_nof3 c4242_nof4z⟩
theorem not_tile'_4242 (D : CongruentDissection 4242) : False :=
  not_tile_of_conditions' 4242 C'_4242 D

private theorem c4243_sqf   : LeafSqf 4243   := by decide +kernel
private theorem c4243_range : LeafRange 4243  := by decide +kernel
private theorem c4243_ell   : LeafEll 4243    := by decide +kernel
private theorem c4243_nsq   : NSqChkSq 4243   := by decide +kernel
private theorem c4243_har   : HArithChkSq 4243 := by decide +kernel
private theorem c4243_r     : LeafR 4243      := by decide +kernel
private theorem c4243_e'    : LeafE' 4243     := by decide +kernel
private theorem c4243_f1    : LeafF1 4243     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4243_s2    : S2ChkSq 4243    := by decide +kernel
private theorem c4243_s3    : S3ChkSq 4243    := by decide +kernel
private theorem c4243_iso   : LeafIso 4243    := by decide +kernel
private theorem c4243_nof2  : NoF2ChkSq 4243  := by decide +kernel
private theorem c4243_nof3  : NoF3ChkSq 4243  := by decide +kernel
private theorem c4243_nof4z : NoF4zChkSq 4243 := by decide +kernel
theorem C'_4243 : C' 4243 :=
  ⟨c4243_sqf, c4243_range, c4243_ell, leafNSq_of_sq c4243_nsq, leafHAr_of_sq c4243_har,
   c4243_r, c4243_e', c4243_f1, leafS2_of_sq c4243_s2, leafS3_of_sq c4243_s3,
   c4243_iso, leafR8_of_sq c4243_nof2 c4243_nof3 c4243_nof4z⟩
theorem not_tile'_4243 (D : CongruentDissection 4243) : False :=
  not_tile_of_conditions' 4243 C'_4243 D

private theorem c4246_sqf   : LeafSqf 4246   := by decide +kernel
private theorem c4246_range : LeafRange 4246  := by decide +kernel
private theorem c4246_ell   : LeafEll 4246    := by decide +kernel
private theorem c4246_nsq   : NSqChkSq 4246   := by decide +kernel
private theorem c4246_har   : HArithChkSq 4246 := by decide +kernel
private theorem c4246_r     : LeafR 4246      := by decide +kernel
private theorem c4246_e'    : LeafE' 4246     := by decide +kernel
private theorem c4246_f1    : LeafF1 4246     := Or.inl (by decide)
private theorem c4246_s2    : S2ChkSq 4246    := by decide +kernel
private theorem c4246_s3    : S3ChkSq 4246    := by decide +kernel
private theorem c4246_iso   : LeafIso 4246    := by decide +kernel
private theorem c4246_nof2  : NoF2ChkSq 4246  := by decide +kernel
private theorem c4246_nof3  : NoF3ChkSq 4246  := by decide +kernel
private theorem c4246_nof4z : NoF4zChkSq 4246 := by decide +kernel
theorem C'_4246 : C' 4246 :=
  ⟨c4246_sqf, c4246_range, c4246_ell, leafNSq_of_sq c4246_nsq, leafHAr_of_sq c4246_har,
   c4246_r, c4246_e', c4246_f1, leafS2_of_sq c4246_s2, leafS3_of_sq c4246_s3,
   c4246_iso, leafR8_of_sq c4246_nof2 c4246_nof3 c4246_nof4z⟩
theorem not_tile'_4246 (D : CongruentDissection 4246) : False :=
  not_tile_of_conditions' 4246 C'_4246 D

private theorem c4247_sqf   : LeafSqf 4247   := by decide +kernel
private theorem c4247_range : LeafRange 4247  := by decide +kernel
private theorem c4247_ell   : LeafEll 4247    := by decide +kernel
private theorem c4247_nsq   : NSqChkSq 4247   := by decide +kernel
private theorem c4247_har   : HArithChkSq 4247 := by decide +kernel
private theorem c4247_r     : LeafR 4247      := by decide +kernel
private theorem c4247_e'    : LeafE' 4247     := by decide +kernel
private theorem c4247_f1    : LeafF1 4247     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4247_s2    : S2ChkSq 4247    := by decide +kernel
private theorem c4247_s3    : S3ChkSq 4247    := by decide +kernel
private theorem c4247_iso   : LeafIso 4247    := by decide +kernel
private theorem c4247_nof2  : NoF2ChkSq 4247  := by decide +kernel
private theorem c4247_nof3  : NoF3ChkSq 4247  := by decide +kernel
private theorem c4247_nof4z : NoF4zChkSq 4247 := by decide +kernel
theorem C'_4247 : C' 4247 :=
  ⟨c4247_sqf, c4247_range, c4247_ell, leafNSq_of_sq c4247_nsq, leafHAr_of_sq c4247_har,
   c4247_r, c4247_e', c4247_f1, leafS2_of_sq c4247_s2, leafS3_of_sq c4247_s3,
   c4247_iso, leafR8_of_sq c4247_nof2 c4247_nof3 c4247_nof4z⟩
theorem not_tile'_4247 (D : CongruentDissection 4247) : False :=
  not_tile_of_conditions' 4247 C'_4247 D

end Erdos634.Draft.AllN2
