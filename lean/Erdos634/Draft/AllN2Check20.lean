/- AllN2Check20: N = 789, 791, 807, 813, 815
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c789_sqf   : LeafSqf 789   := by decide +kernel
private theorem c789_range : LeafRange 789  := by decide +kernel
private theorem c789_ell   : LeafEll 789    := by decide +kernel
private theorem c789_nsq   : NSqChkSq 789   := by decide +kernel
private theorem c789_har   : HArithChkSq 789 := by decide +kernel
private theorem c789_r     : LeafR 789      := by decide +kernel
private theorem c789_e'    : LeafE' 789     := by decide +kernel
private theorem c789_f1    : LeafF1 789     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c789_s2    : S2ChkSq 789    := by decide +kernel
private theorem c789_s3    : S3ChkSq 789    := by decide +kernel
private theorem c789_iso   : LeafIso 789    := by decide +kernel
private theorem c789_nof2  : NoF2ChkSq 789  := by decide +kernel
private theorem c789_nof3  : NoF3ChkSq 789  := by decide +kernel
private theorem c789_nof4z : NoF4zChkSq 789 := by decide +kernel
theorem C'_789 : C' 789 :=
  ⟨c789_sqf, c789_range, c789_ell, leafNSq_of_sq c789_nsq, leafHAr_of_sq c789_har,
   c789_r, c789_e', c789_f1, leafS2_of_sq c789_s2, leafS3_of_sq c789_s3,
   c789_iso, leafR8_of_sq c789_nof2 c789_nof3 c789_nof4z⟩
theorem not_tile'_789 (D : CongruentDissection 789) : False :=
  not_tile_of_conditions' 789 C'_789 D

private theorem c791_sqf   : LeafSqf 791   := by decide +kernel
private theorem c791_range : LeafRange 791  := by decide +kernel
private theorem c791_ell   : LeafEll 791    := by decide +kernel
private theorem c791_nsq   : NSqChkSq 791   := by decide +kernel
private theorem c791_har   : HArithChkSq 791 := by decide +kernel
private theorem c791_r     : LeafR 791      := by decide +kernel
private theorem c791_e'    : LeafE' 791     := by decide +kernel
private theorem c791_f1    : LeafF1 791     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c791_s2    : S2ChkSq 791    := by decide +kernel
private theorem c791_s3    : S3ChkSq 791    := by decide +kernel
private theorem c791_iso   : LeafIso 791    := by decide +kernel
private theorem c791_nof2  : NoF2ChkSq 791  := by decide +kernel
private theorem c791_nof3  : NoF3ChkSq 791  := by decide +kernel
private theorem c791_nof4z : NoF4zChkSq 791 := by decide +kernel
theorem C'_791 : C' 791 :=
  ⟨c791_sqf, c791_range, c791_ell, leafNSq_of_sq c791_nsq, leafHAr_of_sq c791_har,
   c791_r, c791_e', c791_f1, leafS2_of_sq c791_s2, leafS3_of_sq c791_s3,
   c791_iso, leafR8_of_sq c791_nof2 c791_nof3 c791_nof4z⟩
theorem not_tile'_791 (D : CongruentDissection 791) : False :=
  not_tile_of_conditions' 791 C'_791 D

private theorem c807_sqf   : LeafSqf 807   := by decide +kernel
private theorem c807_range : LeafRange 807  := by decide +kernel
private theorem c807_ell   : LeafEll 807    := by decide +kernel
private theorem c807_nsq   : NSqChkSq 807   := by decide +kernel
private theorem c807_har   : HArithChkSq 807 := by decide +kernel
private theorem c807_r     : LeafR 807      := by decide +kernel
private theorem c807_e'    : LeafE' 807     := by decide +kernel
private theorem c807_f1    : LeafF1 807     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c807_s2    : S2ChkSq 807    := by decide +kernel
private theorem c807_s3    : S3ChkSq 807    := by decide +kernel
private theorem c807_iso   : LeafIso 807    := by decide +kernel
private theorem c807_nof2  : NoF2ChkSq 807  := by decide +kernel
private theorem c807_nof3  : NoF3ChkSq 807  := by decide +kernel
private theorem c807_nof4z : NoF4zChkSq 807 := by decide +kernel
theorem C'_807 : C' 807 :=
  ⟨c807_sqf, c807_range, c807_ell, leafNSq_of_sq c807_nsq, leafHAr_of_sq c807_har,
   c807_r, c807_e', c807_f1, leafS2_of_sq c807_s2, leafS3_of_sq c807_s3,
   c807_iso, leafR8_of_sq c807_nof2 c807_nof3 c807_nof4z⟩
theorem not_tile'_807 (D : CongruentDissection 807) : False :=
  not_tile_of_conditions' 807 C'_807 D

private theorem c813_sqf   : LeafSqf 813   := by decide +kernel
private theorem c813_range : LeafRange 813  := by decide +kernel
private theorem c813_ell   : LeafEll 813    := by decide +kernel
private theorem c813_nsq   : NSqChkSq 813   := by decide +kernel
private theorem c813_har   : HArithChkSq 813 := by decide +kernel
private theorem c813_r     : LeafR 813      := by decide +kernel
private theorem c813_e'    : LeafE' 813     := by decide +kernel
private theorem c813_f1    : LeafF1 813     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c813_s2    : S2ChkSq 813    := by decide +kernel
private theorem c813_s3    : S3ChkSq 813    := by decide +kernel
private theorem c813_iso   : LeafIso 813    := by decide +kernel
private theorem c813_nof2  : NoF2ChkSq 813  := by decide +kernel
private theorem c813_nof3  : NoF3ChkSq 813  := by decide +kernel
private theorem c813_nof4z : NoF4zChkSq 813 := by decide +kernel
theorem C'_813 : C' 813 :=
  ⟨c813_sqf, c813_range, c813_ell, leafNSq_of_sq c813_nsq, leafHAr_of_sq c813_har,
   c813_r, c813_e', c813_f1, leafS2_of_sq c813_s2, leafS3_of_sq c813_s3,
   c813_iso, leafR8_of_sq c813_nof2 c813_nof3 c813_nof4z⟩
theorem not_tile'_813 (D : CongruentDissection 813) : False :=
  not_tile_of_conditions' 813 C'_813 D

private theorem c815_sqf   : LeafSqf 815   := by decide +kernel
private theorem c815_range : LeafRange 815  := by decide +kernel
private theorem c815_ell   : LeafEll 815    := by decide +kernel
private theorem c815_nsq   : NSqChkSq 815   := by decide +kernel
private theorem c815_har   : HArithChkSq 815 := by decide +kernel
private theorem c815_r     : LeafR 815      := by decide +kernel
private theorem c815_e'    : LeafE' 815     := by decide +kernel
private theorem c815_f1    : LeafF1 815     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c815_s2    : S2ChkSq 815    := by decide +kernel
private theorem c815_s3    : S3ChkSq 815    := by decide +kernel
private theorem c815_iso   : LeafIso 815    := by decide +kernel
private theorem c815_nof2  : NoF2ChkSq 815  := by decide +kernel
private theorem c815_nof3  : NoF3ChkSq 815  := by decide +kernel
private theorem c815_nof4z : NoF4zChkSq 815 := by decide +kernel
theorem C'_815 : C' 815 :=
  ⟨c815_sqf, c815_range, c815_ell, leafNSq_of_sq c815_nsq, leafHAr_of_sq c815_har,
   c815_r, c815_e', c815_f1, leafS2_of_sq c815_s2, leafS3_of_sq c815_s3,
   c815_iso, leafR8_of_sq c815_nof2 c815_nof3 c815_nof4z⟩
theorem not_tile'_815 (D : CongruentDissection 815) : False :=
  not_tile_of_conditions' 815 C'_815 D

end Erdos634.Draft.AllN2
