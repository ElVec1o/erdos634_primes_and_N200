/- AllN2Check52: N = 1999, 2002, 2003, 2010, 2011
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c1999_sqf   : LeafSqf 1999   := by decide +kernel
private theorem c1999_range : LeafRange 1999  := by decide +kernel
private theorem c1999_ell   : LeafEll 1999    := by decide +kernel
private theorem c1999_nsq   : NSqChkSq 1999   := by decide +kernel
private theorem c1999_har   : HArithChkSq 1999 := by decide +kernel
private theorem c1999_r     : LeafR 1999      := by decide +kernel
private theorem c1999_e'    : LeafE' 1999     := by decide +kernel
private theorem c1999_f1    : LeafF1 1999     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1999_s2    : S2ChkSq 1999    := by decide +kernel
private theorem c1999_s3    : S3ChkSq 1999    := by decide +kernel
private theorem c1999_iso   : LeafIso 1999    := by decide +kernel
private theorem c1999_nof2  : NoF2ChkSq 1999  := by decide +kernel
private theorem c1999_nof3  : NoF3ChkSq 1999  := by decide +kernel
private theorem c1999_nof4z : NoF4zChkSq 1999 := by decide +kernel
theorem C'_1999 : C' 1999 :=
  ⟨c1999_sqf, c1999_range, c1999_ell, leafNSq_of_sq c1999_nsq, leafHAr_of_sq c1999_har,
   c1999_r, c1999_e', c1999_f1, leafS2_of_sq c1999_s2, leafS3_of_sq c1999_s3,
   c1999_iso, leafR8_of_sq c1999_nof2 c1999_nof3 c1999_nof4z⟩
theorem not_tile'_1999 (D : CongruentDissection 1999) : False :=
  not_tile_of_conditions' 1999 C'_1999 D

private theorem c2002_sqf   : LeafSqf 2002   := by decide +kernel
private theorem c2002_range : LeafRange 2002  := by decide +kernel
private theorem c2002_ell   : LeafEll 2002    := by decide +kernel
private theorem c2002_nsq   : NSqChkSq 2002   := by decide +kernel
private theorem c2002_har   : HArithChkSq 2002 := by decide +kernel
private theorem c2002_r     : LeafR 2002      := by decide +kernel
private theorem c2002_e'    : LeafE' 2002     := by decide +kernel
private theorem c2002_f1    : LeafF1 2002     := Or.inl (by decide)
private theorem c2002_s2    : S2ChkSq 2002    := by decide +kernel
private theorem c2002_s3    : S3ChkSq 2002    := by decide +kernel
private theorem c2002_iso   : LeafIso 2002    := by decide +kernel
private theorem c2002_nof2  : NoF2ChkSq 2002  := by decide +kernel
private theorem c2002_nof3  : NoF3ChkSq 2002  := by decide +kernel
private theorem c2002_nof4z : NoF4zChkSq 2002 := by decide +kernel
theorem C'_2002 : C' 2002 :=
  ⟨c2002_sqf, c2002_range, c2002_ell, leafNSq_of_sq c2002_nsq, leafHAr_of_sq c2002_har,
   c2002_r, c2002_e', c2002_f1, leafS2_of_sq c2002_s2, leafS3_of_sq c2002_s3,
   c2002_iso, leafR8_of_sq c2002_nof2 c2002_nof3 c2002_nof4z⟩
theorem not_tile'_2002 (D : CongruentDissection 2002) : False :=
  not_tile_of_conditions' 2002 C'_2002 D

private theorem c2003_sqf   : LeafSqf 2003   := by decide +kernel
private theorem c2003_range : LeafRange 2003  := by decide +kernel
private theorem c2003_ell   : LeafEll 2003    := by decide +kernel
private theorem c2003_nsq   : NSqChkSq 2003   := by decide +kernel
private theorem c2003_har   : HArithChkSq 2003 := by decide +kernel
private theorem c2003_r     : LeafR 2003      := by decide +kernel
private theorem c2003_e'    : LeafE' 2003     := by decide +kernel
private theorem c2003_f1    : LeafF1 2003     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2003_s2    : S2ChkSq 2003    := by decide +kernel
private theorem c2003_s3    : S3ChkSq 2003    := by decide +kernel
private theorem c2003_iso   : LeafIso 2003    := by decide +kernel
private theorem c2003_nof2  : NoF2ChkSq 2003  := by decide +kernel
private theorem c2003_nof3  : NoF3ChkSq 2003  := by decide +kernel
private theorem c2003_nof4z : NoF4zChkSq 2003 := by decide +kernel
theorem C'_2003 : C' 2003 :=
  ⟨c2003_sqf, c2003_range, c2003_ell, leafNSq_of_sq c2003_nsq, leafHAr_of_sq c2003_har,
   c2003_r, c2003_e', c2003_f1, leafS2_of_sq c2003_s2, leafS3_of_sq c2003_s3,
   c2003_iso, leafR8_of_sq c2003_nof2 c2003_nof3 c2003_nof4z⟩
theorem not_tile'_2003 (D : CongruentDissection 2003) : False :=
  not_tile_of_conditions' 2003 C'_2003 D

private theorem c2010_sqf   : LeafSqf 2010   := by decide +kernel
private theorem c2010_range : LeafRange 2010  := by decide +kernel
private theorem c2010_ell   : LeafEll 2010    := by decide +kernel
private theorem c2010_nsq   : NSqChkSq 2010   := by decide +kernel
private theorem c2010_har   : HArithChkSq 2010 := by decide +kernel
private theorem c2010_r     : LeafR 2010      := by decide +kernel
private theorem c2010_e'    : LeafE' 2010     := by decide +kernel
private theorem c2010_f1    : LeafF1 2010     := Or.inl (by decide)
private theorem c2010_s2    : S2ChkSq 2010    := by decide +kernel
private theorem c2010_s3    : S3ChkSq 2010    := by decide +kernel
private theorem c2010_iso   : LeafIso 2010    := by decide +kernel
private theorem c2010_nof2  : NoF2ChkSq 2010  := by decide +kernel
private theorem c2010_nof3  : NoF3ChkSq 2010  := by decide +kernel
private theorem c2010_nof4z : NoF4zChkSq 2010 := by decide +kernel
theorem C'_2010 : C' 2010 :=
  ⟨c2010_sqf, c2010_range, c2010_ell, leafNSq_of_sq c2010_nsq, leafHAr_of_sq c2010_har,
   c2010_r, c2010_e', c2010_f1, leafS2_of_sq c2010_s2, leafS3_of_sq c2010_s3,
   c2010_iso, leafR8_of_sq c2010_nof2 c2010_nof3 c2010_nof4z⟩
theorem not_tile'_2010 (D : CongruentDissection 2010) : False :=
  not_tile_of_conditions' 2010 C'_2010 D

private theorem c2011_sqf   : LeafSqf 2011   := by decide +kernel
private theorem c2011_range : LeafRange 2011  := by decide +kernel
private theorem c2011_ell   : LeafEll 2011    := by decide +kernel
private theorem c2011_nsq   : NSqChkSq 2011   := by decide +kernel
private theorem c2011_har   : HArithChkSq 2011 := by decide +kernel
private theorem c2011_r     : LeafR 2011      := by decide +kernel
private theorem c2011_e'    : LeafE' 2011     := by decide +kernel
private theorem c2011_f1    : LeafF1 2011     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2011_s2    : S2ChkSq 2011    := by decide +kernel
private theorem c2011_s3    : S3ChkSq 2011    := by decide +kernel
private theorem c2011_iso   : LeafIso 2011    := by decide +kernel
private theorem c2011_nof2  : NoF2ChkSq 2011  := by decide +kernel
private theorem c2011_nof3  : NoF3ChkSq 2011  := by decide +kernel
private theorem c2011_nof4z : NoF4zChkSq 2011 := by decide +kernel
theorem C'_2011 : C' 2011 :=
  ⟨c2011_sqf, c2011_range, c2011_ell, leafNSq_of_sq c2011_nsq, leafHAr_of_sq c2011_har,
   c2011_r, c2011_e', c2011_f1, leafS2_of_sq c2011_s2, leafS3_of_sq c2011_s3,
   c2011_iso, leafR8_of_sq c2011_nof2 c2011_nof3 c2011_nof4z⟩
theorem not_tile'_2011 (D : CongruentDissection 2011) : False :=
  not_tile_of_conditions' 2011 C'_2011 D

end Erdos634.Draft.AllN2
