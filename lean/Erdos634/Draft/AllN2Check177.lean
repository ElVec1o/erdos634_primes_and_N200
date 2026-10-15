/- AllN2Check177: N = 3606, 3607, 3611, 3614, 3619
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3606_sqf   : LeafSqf 3606   := by decide +kernel
private theorem c3606_range : LeafRange 3606  := by decide +kernel
private theorem c3606_ell   : LeafEll 3606    := by decide +kernel
private theorem c3606_nsq   : NSqChkSq 3606   := by decide +kernel
private theorem c3606_har   : HArithChkSq 3606 := by decide +kernel
private theorem c3606_r     : LeafR 3606      := by decide +kernel
private theorem c3606_e'    : LeafE' 3606     := by decide +kernel
private theorem c3606_f1    : LeafF1 3606     := Or.inl (by decide)
private theorem c3606_s2    : S2ChkSq 3606    := by decide +kernel
private theorem c3606_s3    : S3ChkSq 3606    := by decide +kernel
private theorem c3606_iso   : LeafIso 3606    := by decide +kernel
private theorem c3606_nof2  : NoF2ChkSq 3606  := by decide +kernel
private theorem c3606_nof3  : NoF3ChkSq 3606  := by decide +kernel
private theorem c3606_nof4z : NoF4zChkSq 3606 := by decide +kernel
theorem C'_3606 : C' 3606 :=
  ⟨c3606_sqf, c3606_range, c3606_ell, leafNSq_of_sq c3606_nsq, leafHAr_of_sq c3606_har,
   c3606_r, c3606_e', c3606_f1, leafS2_of_sq c3606_s2, leafS3_of_sq c3606_s3,
   c3606_iso, leafR8_of_sq c3606_nof2 c3606_nof3 c3606_nof4z⟩
theorem not_tile'_3606 (D : CongruentDissection 3606) : False :=
  not_tile_of_conditions' 3606 C'_3606 D

private theorem c3607_sqf   : LeafSqf 3607   := by decide +kernel
private theorem c3607_range : LeafRange 3607  := by decide +kernel
private theorem c3607_ell   : LeafEll 3607    := by decide +kernel
private theorem c3607_nsq   : NSqChkSq 3607   := by decide +kernel
private theorem c3607_har   : HArithChkSq 3607 := by decide +kernel
private theorem c3607_r     : LeafR 3607      := by decide +kernel
private theorem c3607_e'    : LeafE' 3607     := by decide +kernel
private theorem c3607_f1    : LeafF1 3607     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3607_s2    : S2ChkSq 3607    := by decide +kernel
private theorem c3607_s3    : S3ChkSq 3607    := by decide +kernel
private theorem c3607_iso   : LeafIso 3607    := by decide +kernel
private theorem c3607_nof2  : NoF2ChkSq 3607  := by decide +kernel
private theorem c3607_nof3  : NoF3ChkSq 3607  := by decide +kernel
private theorem c3607_nof4z : NoF4zChkSq 3607 := by decide +kernel
theorem C'_3607 : C' 3607 :=
  ⟨c3607_sqf, c3607_range, c3607_ell, leafNSq_of_sq c3607_nsq, leafHAr_of_sq c3607_har,
   c3607_r, c3607_e', c3607_f1, leafS2_of_sq c3607_s2, leafS3_of_sq c3607_s3,
   c3607_iso, leafR8_of_sq c3607_nof2 c3607_nof3 c3607_nof4z⟩
theorem not_tile'_3607 (D : CongruentDissection 3607) : False :=
  not_tile_of_conditions' 3607 C'_3607 D

private theorem c3611_sqf   : LeafSqf 3611   := by decide +kernel
private theorem c3611_range : LeafRange 3611  := by decide +kernel
private theorem c3611_ell   : LeafEll 3611    := by decide +kernel
private theorem c3611_nsq   : NSqChkSq 3611   := by decide +kernel
private theorem c3611_har   : HArithChkSq 3611 := by decide +kernel
private theorem c3611_r     : LeafR 3611      := by decide +kernel
private theorem c3611_e'    : LeafE' 3611     := by decide +kernel
private theorem c3611_f1    : LeafF1 3611     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3611_s2    : S2ChkSq 3611    := by decide +kernel
private theorem c3611_s3    : S3ChkSq 3611    := by decide +kernel
private theorem c3611_iso   : LeafIso 3611    := by decide +kernel
private theorem c3611_nof2  : NoF2ChkSq 3611  := by decide +kernel
private theorem c3611_nof3  : NoF3ChkSq 3611  := by decide +kernel
private theorem c3611_nof4z : NoF4zChkSq 3611 := by decide +kernel
theorem C'_3611 : C' 3611 :=
  ⟨c3611_sqf, c3611_range, c3611_ell, leafNSq_of_sq c3611_nsq, leafHAr_of_sq c3611_har,
   c3611_r, c3611_e', c3611_f1, leafS2_of_sq c3611_s2, leafS3_of_sq c3611_s3,
   c3611_iso, leafR8_of_sq c3611_nof2 c3611_nof3 c3611_nof4z⟩
theorem not_tile'_3611 (D : CongruentDissection 3611) : False :=
  not_tile_of_conditions' 3611 C'_3611 D

private theorem c3614_sqf   : LeafSqf 3614   := by decide +kernel
private theorem c3614_range : LeafRange 3614  := by decide +kernel
private theorem c3614_ell   : LeafEll 3614    := by decide +kernel
private theorem c3614_nsq   : NSqChkSq 3614   := by decide +kernel
private theorem c3614_har   : HArithChkSq 3614 := by decide +kernel
private theorem c3614_r     : LeafR 3614      := by decide +kernel
private theorem c3614_e'    : LeafE' 3614     := by decide +kernel
private theorem c3614_f1    : LeafF1 3614     := Or.inl (by decide)
private theorem c3614_s2    : S2ChkSq 3614    := by decide +kernel
private theorem c3614_s3    : S3ChkSq 3614    := by decide +kernel
private theorem c3614_iso   : LeafIso 3614    := by decide +kernel
private theorem c3614_nof2  : NoF2ChkSq 3614  := by decide +kernel
private theorem c3614_nof3  : NoF3ChkSq 3614  := by decide +kernel
private theorem c3614_nof4z : NoF4zChkSq 3614 := by decide +kernel
theorem C'_3614 : C' 3614 :=
  ⟨c3614_sqf, c3614_range, c3614_ell, leafNSq_of_sq c3614_nsq, leafHAr_of_sq c3614_har,
   c3614_r, c3614_e', c3614_f1, leafS2_of_sq c3614_s2, leafS3_of_sq c3614_s3,
   c3614_iso, leafR8_of_sq c3614_nof2 c3614_nof3 c3614_nof4z⟩
theorem not_tile'_3614 (D : CongruentDissection 3614) : False :=
  not_tile_of_conditions' 3614 C'_3614 D

private theorem c3619_sqf   : LeafSqf 3619   := by decide +kernel
private theorem c3619_range : LeafRange 3619  := by decide +kernel
private theorem c3619_ell   : LeafEll 3619    := by decide +kernel
private theorem c3619_nsq   : NSqChkSq 3619   := by decide +kernel
private theorem c3619_har   : HArithChkSq 3619 := by decide +kernel
private theorem c3619_r     : LeafR 3619      := by decide +kernel
private theorem c3619_e'    : LeafE' 3619     := by decide +kernel
private theorem c3619_f1    : LeafF1 3619     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3619_s2    : S2ChkSq 3619    := by decide +kernel
private theorem c3619_s3    : S3ChkSq 3619    := by decide +kernel
private theorem c3619_iso   : LeafIso 3619    := by decide +kernel
private theorem c3619_nof2  : NoF2ChkSq 3619  := by decide +kernel
private theorem c3619_nof3  : NoF3ChkSq 3619  := by decide +kernel
private theorem c3619_nof4z : NoF4zChkSq 3619 := by decide +kernel
theorem C'_3619 : C' 3619 :=
  ⟨c3619_sqf, c3619_range, c3619_ell, leafNSq_of_sq c3619_nsq, leafHAr_of_sq c3619_har,
   c3619_r, c3619_e', c3619_f1, leafS2_of_sq c3619_s2, leafS3_of_sq c3619_s3,
   c3619_iso, leafR8_of_sq c3619_nof2 c3619_nof3 c3619_nof4z⟩
theorem not_tile'_3619 (D : CongruentDissection 3619) : False :=
  not_tile_of_conditions' 3619 C'_3619 D

end Erdos634.Draft.AllN2
