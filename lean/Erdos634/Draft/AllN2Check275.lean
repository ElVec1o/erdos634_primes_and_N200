/- AllN2Check275: N = 4854, 4855, 4857, 4858, 4859
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4854_sqf   : LeafSqf 4854   := by decide +kernel
private theorem c4854_range : LeafRange 4854  := by decide +kernel
private theorem c4854_ell   : LeafEll 4854    := by decide +kernel
private theorem c4854_nsq   : NSqChkSq 4854   := by decide +kernel
private theorem c4854_har   : HArithChkSq 4854 := by decide +kernel
private theorem c4854_r     : LeafR 4854      := by decide +kernel
private theorem c4854_e'    : LeafE' 4854     := by decide +kernel
private theorem c4854_f1    : LeafF1 4854     := Or.inl (by decide)
private theorem c4854_s2    : S2ChkSq 4854    := by decide +kernel
private theorem c4854_s3    : S3ChkSq 4854    := by decide +kernel
private theorem c4854_iso   : LeafIso 4854    := by decide +kernel
private theorem c4854_nof2  : NoF2ChkSq 4854  := by decide +kernel
private theorem c4854_nof3  : NoF3ChkSq 4854  := by decide +kernel
private theorem c4854_nof4z : NoF4zChkSq 4854 := by decide +kernel
theorem C'_4854 : C' 4854 :=
  ⟨c4854_sqf, c4854_range, c4854_ell, leafNSq_of_sq c4854_nsq, leafHAr_of_sq c4854_har,
   c4854_r, c4854_e', c4854_f1, leafS2_of_sq c4854_s2, leafS3_of_sq c4854_s3,
   c4854_iso, leafR8_of_sq c4854_nof2 c4854_nof3 c4854_nof4z⟩
theorem not_tile'_4854 (D : CongruentDissection 4854) : False :=
  not_tile_of_conditions' 4854 C'_4854 D

private theorem c4855_sqf   : LeafSqf 4855   := by decide +kernel
private theorem c4855_range : LeafRange 4855  := by decide +kernel
private theorem c4855_ell   : LeafEll 4855    := by decide +kernel
private theorem c4855_nsq   : NSqChkSq 4855   := by decide +kernel
private theorem c4855_har   : HArithChkSq 4855 := by decide +kernel
private theorem c4855_r     : LeafR 4855      := by decide +kernel
private theorem c4855_e'    : LeafE' 4855     := by decide +kernel
private theorem c4855_f1    : LeafF1 4855     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4855_s2    : S2ChkSq 4855    := by decide +kernel
private theorem c4855_s3    : S3ChkSq 4855    := by decide +kernel
private theorem c4855_iso   : LeafIso 4855    := by decide +kernel
private theorem c4855_nof2  : NoF2ChkSq 4855  := by decide +kernel
private theorem c4855_nof3  : NoF3ChkSq 4855  := by decide +kernel
private theorem c4855_nof4z : NoF4zChkSq 4855 := by decide +kernel
theorem C'_4855 : C' 4855 :=
  ⟨c4855_sqf, c4855_range, c4855_ell, leafNSq_of_sq c4855_nsq, leafHAr_of_sq c4855_har,
   c4855_r, c4855_e', c4855_f1, leafS2_of_sq c4855_s2, leafS3_of_sq c4855_s3,
   c4855_iso, leafR8_of_sq c4855_nof2 c4855_nof3 c4855_nof4z⟩
theorem not_tile'_4855 (D : CongruentDissection 4855) : False :=
  not_tile_of_conditions' 4855 C'_4855 D

private theorem c4857_sqf   : LeafSqf 4857   := by decide +kernel
private theorem c4857_range : LeafRange 4857  := by decide +kernel
private theorem c4857_ell   : LeafEll 4857    := by decide +kernel
private theorem c4857_nsq   : NSqChkSq 4857   := by decide +kernel
private theorem c4857_har   : HArithChkSq 4857 := by decide +kernel
private theorem c4857_r     : LeafR 4857      := by decide +kernel
private theorem c4857_e'    : LeafE' 4857     := by decide +kernel
private theorem c4857_f1    : LeafF1 4857     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4857_s2    : S2ChkSq 4857    := by decide +kernel
private theorem c4857_s3    : S3ChkSq 4857    := by decide +kernel
private theorem c4857_iso   : LeafIso 4857    := by decide +kernel
private theorem c4857_nof2  : NoF2ChkSq 4857  := by decide +kernel
private theorem c4857_nof3  : NoF3ChkSq 4857  := by decide +kernel
private theorem c4857_nof4z : NoF4zChkSq 4857 := by decide +kernel
theorem C'_4857 : C' 4857 :=
  ⟨c4857_sqf, c4857_range, c4857_ell, leafNSq_of_sq c4857_nsq, leafHAr_of_sq c4857_har,
   c4857_r, c4857_e', c4857_f1, leafS2_of_sq c4857_s2, leafS3_of_sq c4857_s3,
   c4857_iso, leafR8_of_sq c4857_nof2 c4857_nof3 c4857_nof4z⟩
theorem not_tile'_4857 (D : CongruentDissection 4857) : False :=
  not_tile_of_conditions' 4857 C'_4857 D

private theorem c4858_sqf   : LeafSqf 4858   := by decide +kernel
private theorem c4858_range : LeafRange 4858  := by decide +kernel
private theorem c4858_ell   : LeafEll 4858    := by decide +kernel
private theorem c4858_nsq   : NSqChkSq 4858   := by decide +kernel
private theorem c4858_har   : HArithChkSq 4858 := by decide +kernel
private theorem c4858_r     : LeafR 4858      := by decide +kernel
private theorem c4858_e'    : LeafE' 4858     := by decide +kernel
private theorem c4858_f1    : LeafF1 4858     := Or.inl (by decide)
private theorem c4858_s2    : S2ChkSq 4858    := by decide +kernel
private theorem c4858_s3    : S3ChkSq 4858    := by decide +kernel
private theorem c4858_iso   : LeafIso 4858    := by decide +kernel
private theorem c4858_nof2  : NoF2ChkSq 4858  := by decide +kernel
private theorem c4858_nof3  : NoF3ChkSq 4858  := by decide +kernel
private theorem c4858_nof4z : NoF4zChkSq 4858 := by decide +kernel
theorem C'_4858 : C' 4858 :=
  ⟨c4858_sqf, c4858_range, c4858_ell, leafNSq_of_sq c4858_nsq, leafHAr_of_sq c4858_har,
   c4858_r, c4858_e', c4858_f1, leafS2_of_sq c4858_s2, leafS3_of_sq c4858_s3,
   c4858_iso, leafR8_of_sq c4858_nof2 c4858_nof3 c4858_nof4z⟩
theorem not_tile'_4858 (D : CongruentDissection 4858) : False :=
  not_tile_of_conditions' 4858 C'_4858 D

private theorem c4859_sqf   : LeafSqf 4859   := by decide +kernel
private theorem c4859_range : LeafRange 4859  := by decide +kernel
private theorem c4859_ell   : LeafEll 4859    := by decide +kernel
private theorem c4859_nsq   : NSqChkSq 4859   := by decide +kernel
private theorem c4859_har   : HArithChkSq 4859 := by decide +kernel
private theorem c4859_r     : LeafR 4859      := by decide +kernel
private theorem c4859_e'    : LeafE' 4859     := by decide +kernel
private theorem c4859_f1    : LeafF1 4859     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4859_s2    : S2ChkSq 4859    := by decide +kernel
private theorem c4859_s3    : S3ChkSq 4859    := by decide +kernel
private theorem c4859_iso   : LeafIso 4859    := by decide +kernel
private theorem c4859_nof2  : NoF2ChkSq 4859  := by decide +kernel
private theorem c4859_nof3  : NoF3ChkSq 4859  := by decide +kernel
private theorem c4859_nof4z : NoF4zChkSq 4859 := by decide +kernel
theorem C'_4859 : C' 4859 :=
  ⟨c4859_sqf, c4859_range, c4859_ell, leafNSq_of_sq c4859_nsq, leafHAr_of_sq c4859_har,
   c4859_r, c4859_e', c4859_f1, leafS2_of_sq c4859_s2, leafS3_of_sq c4859_s3,
   c4859_iso, leafR8_of_sq c4859_nof2 c4859_nof3 c4859_nof4z⟩
theorem not_tile'_4859 (D : CongruentDissection 4859) : False :=
  not_tile_of_conditions' 4859 C'_4859 D

end Erdos634.Draft.AllN2
