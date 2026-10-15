/- AllN2Check22: N = 973, 993, 995.
   Each value has C' N = true (checked by an exact computation).
   Not in any realizable family. No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c973_sqf   : LeafSqf 973   := by decide +kernel
private theorem c973_range : LeafRange 973  := by decide +kernel
private theorem c973_ell   : LeafEll 973    := by decide +kernel
private theorem c973_nsq   : NSqChkSq 973   := by decide +kernel
private theorem c973_har   : HArithChkSq 973 := by decide +kernel
private theorem c973_r     : LeafR 973      := by decide +kernel
private theorem c973_e'    : LeafE' 973     := by decide +kernel
private theorem c973_f1    : LeafF1 973     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c973_s2    : S2ChkSq 973    := by decide +kernel
private theorem c973_s3    : S3ChkSq 973    := by decide +kernel
private theorem c973_iso   : LeafIso 973    := by decide +kernel
private theorem c973_nof2  : NoF2ChkSq 973  := by decide +kernel
private theorem c973_nof3  : NoF3ChkSq 973  := by decide +kernel
private theorem c973_nof4z : NoF4zChkSq 973 := by decide +kernel
theorem C'_973 : C' 973 :=
  ⟨c973_sqf, c973_range, c973_ell, leafNSq_of_sq c973_nsq, leafHAr_of_sq c973_har,
   c973_r, c973_e', c973_f1, leafS2_of_sq c973_s2, leafS3_of_sq c973_s3,
   c973_iso, leafR8_of_sq c973_nof2 c973_nof3 c973_nof4z⟩
theorem not_tile'_973 (D : CongruentDissection 973) : False :=
  not_tile_of_conditions' 973 C'_973 D

private theorem c993_sqf   : LeafSqf 993   := by decide +kernel
private theorem c993_range : LeafRange 993  := by decide +kernel
private theorem c993_ell   : LeafEll 993    := by decide +kernel
private theorem c993_nsq   : NSqChkSq 993   := by decide +kernel
private theorem c993_har   : HArithChkSq 993 := by decide +kernel
private theorem c993_r     : LeafR 993      := by decide +kernel
private theorem c993_e'    : LeafE' 993     := by decide +kernel
private theorem c993_f1    : LeafF1 993     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c993_s2    : S2ChkSq 993    := by decide +kernel
private theorem c993_s3    : S3ChkSq 993    := by decide +kernel
private theorem c993_iso   : LeafIso 993    := by decide +kernel
private theorem c993_nof2  : NoF2ChkSq 993  := by decide +kernel
private theorem c993_nof3  : NoF3ChkSq 993  := by decide +kernel
private theorem c993_nof4z : NoF4zChkSq 993 := by decide +kernel
theorem C'_993 : C' 993 :=
  ⟨c993_sqf, c993_range, c993_ell, leafNSq_of_sq c993_nsq, leafHAr_of_sq c993_har,
   c993_r, c993_e', c993_f1, leafS2_of_sq c993_s2, leafS3_of_sq c993_s3,
   c993_iso, leafR8_of_sq c993_nof2 c993_nof3 c993_nof4z⟩
theorem not_tile'_993 (D : CongruentDissection 993) : False :=
  not_tile_of_conditions' 993 C'_993 D

private theorem c995_sqf   : LeafSqf 995   := by decide +kernel
private theorem c995_range : LeafRange 995  := by decide +kernel
private theorem c995_ell   : LeafEll 995    := by decide +kernel
private theorem c995_nsq   : NSqChkSq 995   := by decide +kernel
private theorem c995_har   : HArithChkSq 995 := by decide +kernel
private theorem c995_r     : LeafR 995      := by decide +kernel
private theorem c995_e'    : LeafE' 995     := by decide +kernel
private theorem c995_f1    : LeafF1 995     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c995_s2    : S2ChkSq 995    := by decide +kernel
private theorem c995_s3    : S3ChkSq 995    := by decide +kernel
private theorem c995_iso   : LeafIso 995    := by decide +kernel
private theorem c995_nof2  : NoF2ChkSq 995  := by decide +kernel
private theorem c995_nof3  : NoF3ChkSq 995  := by decide +kernel
private theorem c995_nof4z : NoF4zChkSq 995 := by decide +kernel
theorem C'_995 : C' 995 :=
  ⟨c995_sqf, c995_range, c995_ell, leafNSq_of_sq c995_nsq, leafHAr_of_sq c995_har,
   c995_r, c995_e', c995_f1, leafS2_of_sq c995_s2, leafS3_of_sq c995_s3,
   c995_iso, leafR8_of_sq c995_nof2 c995_nof3 c995_nof4z⟩
theorem not_tile'_995 (D : CongruentDissection 995) : False :=
  not_tile_of_conditions' 995 C'_995 D

end Erdos634.Draft.AllN2
