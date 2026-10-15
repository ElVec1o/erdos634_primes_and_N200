/- AllN2Check19: N = 715, 717, 721, 723, 749
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c715_sqf   : LeafSqf 715   := by decide +kernel
private theorem c715_range : LeafRange 715  := by decide +kernel
private theorem c715_ell   : LeafEll 715    := by decide +kernel
private theorem c715_nsq   : NSqChkSq 715   := by decide +kernel
private theorem c715_har   : HArithChkSq 715 := by decide +kernel
private theorem c715_r     : LeafR 715      := by decide +kernel
private theorem c715_e'    : LeafE' 715     := by decide +kernel
private theorem c715_f1    : LeafF1 715     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c715_s2    : S2ChkSq 715    := by decide +kernel
private theorem c715_s3    : S3ChkSq 715    := by decide +kernel
private theorem c715_iso   : LeafIso 715    := by decide +kernel
private theorem c715_nof2  : NoF2ChkSq 715  := by decide +kernel
private theorem c715_nof3  : NoF3ChkSq 715  := by decide +kernel
private theorem c715_nof4z : NoF4zChkSq 715 := by decide +kernel
theorem C'_715 : C' 715 :=
  ⟨c715_sqf, c715_range, c715_ell, leafNSq_of_sq c715_nsq, leafHAr_of_sq c715_har,
   c715_r, c715_e', c715_f1, leafS2_of_sq c715_s2, leafS3_of_sq c715_s3,
   c715_iso, leafR8_of_sq c715_nof2 c715_nof3 c715_nof4z⟩
theorem not_tile'_715 (D : CongruentDissection 715) : False :=
  not_tile_of_conditions' 715 C'_715 D

private theorem c717_sqf   : LeafSqf 717   := by decide +kernel
private theorem c717_range : LeafRange 717  := by decide +kernel
private theorem c717_ell   : LeafEll 717    := by decide +kernel
private theorem c717_nsq   : NSqChkSq 717   := by decide +kernel
private theorem c717_har   : HArithChkSq 717 := by decide +kernel
private theorem c717_r     : LeafR 717      := by decide +kernel
private theorem c717_e'    : LeafE' 717     := by decide +kernel
private theorem c717_f1    : LeafF1 717     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c717_s2    : S2ChkSq 717    := by decide +kernel
private theorem c717_s3    : S3ChkSq 717    := by decide +kernel
private theorem c717_iso   : LeafIso 717    := by decide +kernel
private theorem c717_nof2  : NoF2ChkSq 717  := by decide +kernel
private theorem c717_nof3  : NoF3ChkSq 717  := by decide +kernel
private theorem c717_nof4z : NoF4zChkSq 717 := by decide +kernel
theorem C'_717 : C' 717 :=
  ⟨c717_sqf, c717_range, c717_ell, leafNSq_of_sq c717_nsq, leafHAr_of_sq c717_har,
   c717_r, c717_e', c717_f1, leafS2_of_sq c717_s2, leafS3_of_sq c717_s3,
   c717_iso, leafR8_of_sq c717_nof2 c717_nof3 c717_nof4z⟩
theorem not_tile'_717 (D : CongruentDissection 717) : False :=
  not_tile_of_conditions' 717 C'_717 D

private theorem c721_sqf   : LeafSqf 721   := by decide +kernel
private theorem c721_range : LeafRange 721  := by decide +kernel
private theorem c721_ell   : LeafEll 721    := by decide +kernel
private theorem c721_nsq   : NSqChkSq 721   := by decide +kernel
private theorem c721_har   : HArithChkSq 721 := by decide +kernel
private theorem c721_r     : LeafR 721      := by decide +kernel
private theorem c721_e'    : LeafE' 721     := by decide +kernel
private theorem c721_f1    : LeafF1 721     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c721_s2    : S2ChkSq 721    := by decide +kernel
private theorem c721_s3    : S3ChkSq 721    := by decide +kernel
private theorem c721_iso   : LeafIso 721    := by decide +kernel
private theorem c721_nof2  : NoF2ChkSq 721  := by decide +kernel
private theorem c721_nof3  : NoF3ChkSq 721  := by decide +kernel
private theorem c721_nof4z : NoF4zChkSq 721 := by decide +kernel
theorem C'_721 : C' 721 :=
  ⟨c721_sqf, c721_range, c721_ell, leafNSq_of_sq c721_nsq, leafHAr_of_sq c721_har,
   c721_r, c721_e', c721_f1, leafS2_of_sq c721_s2, leafS3_of_sq c721_s3,
   c721_iso, leafR8_of_sq c721_nof2 c721_nof3 c721_nof4z⟩
theorem not_tile'_721 (D : CongruentDissection 721) : False :=
  not_tile_of_conditions' 721 C'_721 D

private theorem c723_sqf   : LeafSqf 723   := by decide +kernel
private theorem c723_range : LeafRange 723  := by decide +kernel
private theorem c723_ell   : LeafEll 723    := by decide +kernel
private theorem c723_nsq   : NSqChkSq 723   := by decide +kernel
private theorem c723_har   : HArithChkSq 723 := by decide +kernel
private theorem c723_r     : LeafR 723      := by decide +kernel
private theorem c723_e'    : LeafE' 723     := by decide +kernel
private theorem c723_f1    : LeafF1 723     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c723_s2    : S2ChkSq 723    := by decide +kernel
private theorem c723_s3    : S3ChkSq 723    := by decide +kernel
private theorem c723_iso   : LeafIso 723    := by decide +kernel
private theorem c723_nof2  : NoF2ChkSq 723  := by decide +kernel
private theorem c723_nof3  : NoF3ChkSq 723  := by decide +kernel
private theorem c723_nof4z : NoF4zChkSq 723 := by decide +kernel
theorem C'_723 : C' 723 :=
  ⟨c723_sqf, c723_range, c723_ell, leafNSq_of_sq c723_nsq, leafHAr_of_sq c723_har,
   c723_r, c723_e', c723_f1, leafS2_of_sq c723_s2, leafS3_of_sq c723_s3,
   c723_iso, leafR8_of_sq c723_nof2 c723_nof3 c723_nof4z⟩
theorem not_tile'_723 (D : CongruentDissection 723) : False :=
  not_tile_of_conditions' 723 C'_723 D

private theorem c749_sqf   : LeafSqf 749   := by decide +kernel
private theorem c749_range : LeafRange 749  := by decide +kernel
private theorem c749_ell   : LeafEll 749    := by decide +kernel
private theorem c749_nsq   : NSqChkSq 749   := by decide +kernel
private theorem c749_har   : HArithChkSq 749 := by decide +kernel
private theorem c749_r     : LeafR 749      := by decide +kernel
private theorem c749_e'    : LeafE' 749     := by decide +kernel
private theorem c749_f1    : LeafF1 749     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c749_s2    : S2ChkSq 749    := by decide +kernel
private theorem c749_s3    : S3ChkSq 749    := by decide +kernel
private theorem c749_iso   : LeafIso 749    := by decide +kernel
private theorem c749_nof2  : NoF2ChkSq 749  := by decide +kernel
private theorem c749_nof3  : NoF3ChkSq 749  := by decide +kernel
private theorem c749_nof4z : NoF4zChkSq 749 := by decide +kernel
theorem C'_749 : C' 749 :=
  ⟨c749_sqf, c749_range, c749_ell, leafNSq_of_sq c749_nsq, leafHAr_of_sq c749_har,
   c749_r, c749_e', c749_f1, leafS2_of_sq c749_s2, leafS3_of_sq c749_s3,
   c749_iso, leafR8_of_sq c749_nof2 c749_nof3 c749_nof4z⟩
theorem not_tile'_749 (D : CongruentDissection 749) : False :=
  not_tile_of_conditions' 749 C'_749 D

end Erdos634.Draft.AllN2
