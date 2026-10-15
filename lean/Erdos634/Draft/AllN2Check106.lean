/- AllN2Check106: N = 2681, 2683, 2686, 2687, 2694
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2681_sqf   : LeafSqf 2681   := by decide +kernel
private theorem c2681_range : LeafRange 2681  := by decide +kernel
private theorem c2681_ell   : LeafEll 2681    := by decide +kernel
private theorem c2681_nsq   : NSqChkSq 2681   := by decide +kernel
private theorem c2681_har   : HArithChkSq 2681 := by decide +kernel
private theorem c2681_r     : LeafR 2681      := by decide +kernel
private theorem c2681_e'    : LeafE' 2681     := by decide +kernel
private theorem c2681_f1    : LeafF1 2681     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2681_s2    : S2ChkSq 2681    := by decide +kernel
private theorem c2681_s3    : S3ChkSq 2681    := by decide +kernel
private theorem c2681_iso   : LeafIso 2681    := by decide +kernel
private theorem c2681_nof2  : NoF2ChkSq 2681  := by decide +kernel
private theorem c2681_nof3  : NoF3ChkSq 2681  := by decide +kernel
private theorem c2681_nof4z : NoF4zChkSq 2681 := by decide +kernel
theorem C'_2681 : C' 2681 :=
  ⟨c2681_sqf, c2681_range, c2681_ell, leafNSq_of_sq c2681_nsq, leafHAr_of_sq c2681_har,
   c2681_r, c2681_e', c2681_f1, leafS2_of_sq c2681_s2, leafS3_of_sq c2681_s3,
   c2681_iso, leafR8_of_sq c2681_nof2 c2681_nof3 c2681_nof4z⟩
theorem not_tile'_2681 (D : CongruentDissection 2681) : False :=
  not_tile_of_conditions' 2681 C'_2681 D

private theorem c2683_sqf   : LeafSqf 2683   := by decide +kernel
private theorem c2683_range : LeafRange 2683  := by decide +kernel
private theorem c2683_ell   : LeafEll 2683    := by decide +kernel
private theorem c2683_nsq   : NSqChkSq 2683   := by decide +kernel
private theorem c2683_har   : HArithChkSq 2683 := by decide +kernel
private theorem c2683_r     : LeafR 2683      := by decide +kernel
private theorem c2683_e'    : LeafE' 2683     := by decide +kernel
private theorem c2683_f1    : LeafF1 2683     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2683_s2    : S2ChkSq 2683    := by decide +kernel
private theorem c2683_s3    : S3ChkSq 2683    := by decide +kernel
private theorem c2683_iso   : LeafIso 2683    := by decide +kernel
private theorem c2683_nof2  : NoF2ChkSq 2683  := by decide +kernel
private theorem c2683_nof3  : NoF3ChkSq 2683  := by decide +kernel
private theorem c2683_nof4z : NoF4zChkSq 2683 := by decide +kernel
theorem C'_2683 : C' 2683 :=
  ⟨c2683_sqf, c2683_range, c2683_ell, leafNSq_of_sq c2683_nsq, leafHAr_of_sq c2683_har,
   c2683_r, c2683_e', c2683_f1, leafS2_of_sq c2683_s2, leafS3_of_sq c2683_s3,
   c2683_iso, leafR8_of_sq c2683_nof2 c2683_nof3 c2683_nof4z⟩
theorem not_tile'_2683 (D : CongruentDissection 2683) : False :=
  not_tile_of_conditions' 2683 C'_2683 D

private theorem c2686_sqf   : LeafSqf 2686   := by decide +kernel
private theorem c2686_range : LeafRange 2686  := by decide +kernel
private theorem c2686_ell   : LeafEll 2686    := by decide +kernel
private theorem c2686_nsq   : NSqChkSq 2686   := by decide +kernel
private theorem c2686_har   : HArithChkSq 2686 := by decide +kernel
private theorem c2686_r     : LeafR 2686      := by decide +kernel
private theorem c2686_e'    : LeafE' 2686     := by decide +kernel
private theorem c2686_f1    : LeafF1 2686     := Or.inl (by decide)
private theorem c2686_s2    : S2ChkSq 2686    := by decide +kernel
private theorem c2686_s3    : S3ChkSq 2686    := by decide +kernel
private theorem c2686_iso   : LeafIso 2686    := by decide +kernel
private theorem c2686_nof2  : NoF2ChkSq 2686  := by decide +kernel
private theorem c2686_nof3  : NoF3ChkSq 2686  := by decide +kernel
private theorem c2686_nof4z : NoF4zChkSq 2686 := by decide +kernel
theorem C'_2686 : C' 2686 :=
  ⟨c2686_sqf, c2686_range, c2686_ell, leafNSq_of_sq c2686_nsq, leafHAr_of_sq c2686_har,
   c2686_r, c2686_e', c2686_f1, leafS2_of_sq c2686_s2, leafS3_of_sq c2686_s3,
   c2686_iso, leafR8_of_sq c2686_nof2 c2686_nof3 c2686_nof4z⟩
theorem not_tile'_2686 (D : CongruentDissection 2686) : False :=
  not_tile_of_conditions' 2686 C'_2686 D

private theorem c2687_sqf   : LeafSqf 2687   := by decide +kernel
private theorem c2687_range : LeafRange 2687  := by decide +kernel
private theorem c2687_ell   : LeafEll 2687    := by decide +kernel
private theorem c2687_nsq   : NSqChkSq 2687   := by decide +kernel
private theorem c2687_har   : HArithChkSq 2687 := by decide +kernel
private theorem c2687_r     : LeafR 2687      := by decide +kernel
private theorem c2687_e'    : LeafE' 2687     := by decide +kernel
private theorem c2687_f1    : LeafF1 2687     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2687_s2    : S2ChkSq 2687    := by decide +kernel
private theorem c2687_s3    : S3ChkSq 2687    := by decide +kernel
private theorem c2687_iso   : LeafIso 2687    := by decide +kernel
private theorem c2687_nof2  : NoF2ChkSq 2687  := by decide +kernel
private theorem c2687_nof3  : NoF3ChkSq 2687  := by decide +kernel
private theorem c2687_nof4z : NoF4zChkSq 2687 := by decide +kernel
theorem C'_2687 : C' 2687 :=
  ⟨c2687_sqf, c2687_range, c2687_ell, leafNSq_of_sq c2687_nsq, leafHAr_of_sq c2687_har,
   c2687_r, c2687_e', c2687_f1, leafS2_of_sq c2687_s2, leafS3_of_sq c2687_s3,
   c2687_iso, leafR8_of_sq c2687_nof2 c2687_nof3 c2687_nof4z⟩
theorem not_tile'_2687 (D : CongruentDissection 2687) : False :=
  not_tile_of_conditions' 2687 C'_2687 D

private theorem c2694_sqf   : LeafSqf 2694   := by decide +kernel
private theorem c2694_range : LeafRange 2694  := by decide +kernel
private theorem c2694_ell   : LeafEll 2694    := by decide +kernel
private theorem c2694_nsq   : NSqChkSq 2694   := by decide +kernel
private theorem c2694_har   : HArithChkSq 2694 := by decide +kernel
private theorem c2694_r     : LeafR 2694      := by decide +kernel
private theorem c2694_e'    : LeafE' 2694     := by decide +kernel
private theorem c2694_f1    : LeafF1 2694     := Or.inl (by decide)
private theorem c2694_s2    : S2ChkSq 2694    := by decide +kernel
private theorem c2694_s3    : S3ChkSq 2694    := by decide +kernel
private theorem c2694_iso   : LeafIso 2694    := by decide +kernel
private theorem c2694_nof2  : NoF2ChkSq 2694  := by decide +kernel
private theorem c2694_nof3  : NoF3ChkSq 2694  := by decide +kernel
private theorem c2694_nof4z : NoF4zChkSq 2694 := by decide +kernel
theorem C'_2694 : C' 2694 :=
  ⟨c2694_sqf, c2694_range, c2694_ell, leafNSq_of_sq c2694_nsq, leafHAr_of_sq c2694_har,
   c2694_r, c2694_e', c2694_f1, leafS2_of_sq c2694_s2, leafS3_of_sq c2694_s3,
   c2694_iso, leafR8_of_sq c2694_nof2 c2694_nof3 c2694_nof4z⟩
theorem not_tile'_2694 (D : CongruentDissection 2694) : False :=
  not_tile_of_conditions' 2694 C'_2694 D

end Erdos634.Draft.AllN2
