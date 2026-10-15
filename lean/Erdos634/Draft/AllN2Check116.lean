/- AllN2Check116: N = 2815, 2819, 2821, 2822, 2823
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2815_sqf   : LeafSqf 2815   := by decide +kernel
private theorem c2815_range : LeafRange 2815  := by decide +kernel
private theorem c2815_ell   : LeafEll 2815    := by decide +kernel
private theorem c2815_nsq   : NSqChkSq 2815   := by decide +kernel
private theorem c2815_har   : HArithChkSq 2815 := by decide +kernel
private theorem c2815_r     : LeafR 2815      := by decide +kernel
private theorem c2815_e'    : LeafE' 2815     := by decide +kernel
private theorem c2815_f1    : LeafF1 2815     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2815_s2    : S2ChkSq 2815    := by decide +kernel
private theorem c2815_s3    : S3ChkSq 2815    := by decide +kernel
private theorem c2815_iso   : LeafIso 2815    := by decide +kernel
private theorem c2815_nof2  : NoF2ChkSq 2815  := by decide +kernel
private theorem c2815_nof3  : NoF3ChkSq 2815  := by decide +kernel
private theorem c2815_nof4z : NoF4zChkSq 2815 := by decide +kernel
theorem C'_2815 : C' 2815 :=
  ⟨c2815_sqf, c2815_range, c2815_ell, leafNSq_of_sq c2815_nsq, leafHAr_of_sq c2815_har,
   c2815_r, c2815_e', c2815_f1, leafS2_of_sq c2815_s2, leafS3_of_sq c2815_s3,
   c2815_iso, leafR8_of_sq c2815_nof2 c2815_nof3 c2815_nof4z⟩
theorem not_tile'_2815 (D : CongruentDissection 2815) : False :=
  not_tile_of_conditions' 2815 C'_2815 D

private theorem c2819_sqf   : LeafSqf 2819   := by decide +kernel
private theorem c2819_range : LeafRange 2819  := by decide +kernel
private theorem c2819_ell   : LeafEll 2819    := by decide +kernel
private theorem c2819_nsq   : NSqChkSq 2819   := by decide +kernel
private theorem c2819_har   : HArithChkSq 2819 := by decide +kernel
private theorem c2819_r     : LeafR 2819      := by decide +kernel
private theorem c2819_e'    : LeafE' 2819     := by decide +kernel
private theorem c2819_f1    : LeafF1 2819     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2819_s2    : S2ChkSq 2819    := by decide +kernel
private theorem c2819_s3    : S3ChkSq 2819    := by decide +kernel
private theorem c2819_iso   : LeafIso 2819    := by decide +kernel
private theorem c2819_nof2  : NoF2ChkSq 2819  := by decide +kernel
private theorem c2819_nof3  : NoF3ChkSq 2819  := by decide +kernel
private theorem c2819_nof4z : NoF4zChkSq 2819 := by decide +kernel
theorem C'_2819 : C' 2819 :=
  ⟨c2819_sqf, c2819_range, c2819_ell, leafNSq_of_sq c2819_nsq, leafHAr_of_sq c2819_har,
   c2819_r, c2819_e', c2819_f1, leafS2_of_sq c2819_s2, leafS3_of_sq c2819_s3,
   c2819_iso, leafR8_of_sq c2819_nof2 c2819_nof3 c2819_nof4z⟩
theorem not_tile'_2819 (D : CongruentDissection 2819) : False :=
  not_tile_of_conditions' 2819 C'_2819 D

private theorem c2821_sqf   : LeafSqf 2821   := by decide +kernel
private theorem c2821_range : LeafRange 2821  := by decide +kernel
private theorem c2821_ell   : LeafEll 2821    := by decide +kernel
private theorem c2821_nsq   : NSqChkSq 2821   := by decide +kernel
private theorem c2821_har   : HArithChkSq 2821 := by decide +kernel
private theorem c2821_r     : LeafR 2821      := by decide +kernel
private theorem c2821_e'    : LeafE' 2821     := by decide +kernel
private theorem c2821_f1    : LeafF1 2821     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2821_s2    : S2ChkSq 2821    := by decide +kernel
private theorem c2821_s3    : S3ChkSq 2821    := by decide +kernel
private theorem c2821_iso   : LeafIso 2821    := by decide +kernel
private theorem c2821_nof2  : NoF2ChkSq 2821  := by decide +kernel
private theorem c2821_nof3  : NoF3ChkSq 2821  := by decide +kernel
private theorem c2821_nof4z : NoF4zChkSq 2821 := by decide +kernel
theorem C'_2821 : C' 2821 :=
  ⟨c2821_sqf, c2821_range, c2821_ell, leafNSq_of_sq c2821_nsq, leafHAr_of_sq c2821_har,
   c2821_r, c2821_e', c2821_f1, leafS2_of_sq c2821_s2, leafS3_of_sq c2821_s3,
   c2821_iso, leafR8_of_sq c2821_nof2 c2821_nof3 c2821_nof4z⟩
theorem not_tile'_2821 (D : CongruentDissection 2821) : False :=
  not_tile_of_conditions' 2821 C'_2821 D

private theorem c2822_sqf   : LeafSqf 2822   := by decide +kernel
private theorem c2822_range : LeafRange 2822  := by decide +kernel
private theorem c2822_ell   : LeafEll 2822    := by decide +kernel
private theorem c2822_nsq   : NSqChkSq 2822   := by decide +kernel
private theorem c2822_har   : HArithChkSq 2822 := by decide +kernel
private theorem c2822_r     : LeafR 2822      := by decide +kernel
private theorem c2822_e'    : LeafE' 2822     := by decide +kernel
private theorem c2822_f1    : LeafF1 2822     := Or.inl (by decide)
private theorem c2822_s2    : S2ChkSq 2822    := by decide +kernel
private theorem c2822_s3    : S3ChkSq 2822    := by decide +kernel
private theorem c2822_iso   : LeafIso 2822    := by decide +kernel
private theorem c2822_nof2  : NoF2ChkSq 2822  := by decide +kernel
private theorem c2822_nof3  : NoF3ChkSq 2822  := by decide +kernel
private theorem c2822_nof4z : NoF4zChkSq 2822 := by decide +kernel
theorem C'_2822 : C' 2822 :=
  ⟨c2822_sqf, c2822_range, c2822_ell, leafNSq_of_sq c2822_nsq, leafHAr_of_sq c2822_har,
   c2822_r, c2822_e', c2822_f1, leafS2_of_sq c2822_s2, leafS3_of_sq c2822_s3,
   c2822_iso, leafR8_of_sq c2822_nof2 c2822_nof3 c2822_nof4z⟩
theorem not_tile'_2822 (D : CongruentDissection 2822) : False :=
  not_tile_of_conditions' 2822 C'_2822 D

private theorem c2823_sqf   : LeafSqf 2823   := by decide +kernel
private theorem c2823_range : LeafRange 2823  := by decide +kernel
private theorem c2823_ell   : LeafEll 2823    := by decide +kernel
private theorem c2823_nsq   : NSqChkSq 2823   := by decide +kernel
private theorem c2823_har   : HArithChkSq 2823 := by decide +kernel
private theorem c2823_r     : LeafR 2823      := by decide +kernel
private theorem c2823_e'    : LeafE' 2823     := by decide +kernel
private theorem c2823_f1    : LeafF1 2823     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2823_s2    : S2ChkSq 2823    := by decide +kernel
private theorem c2823_s3    : S3ChkSq 2823    := by decide +kernel
private theorem c2823_iso   : LeafIso 2823    := by decide +kernel
private theorem c2823_nof2  : NoF2ChkSq 2823  := by decide +kernel
private theorem c2823_nof3  : NoF3ChkSq 2823  := by decide +kernel
private theorem c2823_nof4z : NoF4zChkSq 2823 := by decide +kernel
theorem C'_2823 : C' 2823 :=
  ⟨c2823_sqf, c2823_range, c2823_ell, leafNSq_of_sq c2823_nsq, leafHAr_of_sq c2823_har,
   c2823_r, c2823_e', c2823_f1, leafS2_of_sq c2823_s2, leafS3_of_sq c2823_s3,
   c2823_iso, leafR8_of_sq c2823_nof2 c2823_nof3 c2823_nof4z⟩
theorem not_tile'_2823 (D : CongruentDissection 2823) : False :=
  not_tile_of_conditions' 2823 C'_2823 D

end Erdos634.Draft.AllN2
