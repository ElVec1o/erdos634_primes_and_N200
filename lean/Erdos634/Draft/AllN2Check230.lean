/- AllN2Check230: N = 4299, 4301, 4303, 4307, 4309
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4299_sqf   : LeafSqf 4299   := by decide +kernel
private theorem c4299_range : LeafRange 4299  := by decide +kernel
private theorem c4299_ell   : LeafEll 4299    := by decide +kernel
private theorem c4299_nsq   : NSqChkSq 4299   := by decide +kernel
private theorem c4299_har   : HArithChkSq 4299 := by decide +kernel
private theorem c4299_r     : LeafR 4299      := by decide +kernel
private theorem c4299_e'    : LeafE' 4299     := by decide +kernel
private theorem c4299_f1    : LeafF1 4299     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4299_s2    : S2ChkSq 4299    := by decide +kernel
private theorem c4299_s3    : S3ChkSq 4299    := by decide +kernel
private theorem c4299_iso   : LeafIso 4299    := by decide +kernel
private theorem c4299_nof2  : NoF2ChkSq 4299  := by decide +kernel
private theorem c4299_nof3  : NoF3ChkSq 4299  := by decide +kernel
private theorem c4299_nof4z : NoF4zChkSq 4299 := by decide +kernel
theorem C'_4299 : C' 4299 :=
  ⟨c4299_sqf, c4299_range, c4299_ell, leafNSq_of_sq c4299_nsq, leafHAr_of_sq c4299_har,
   c4299_r, c4299_e', c4299_f1, leafS2_of_sq c4299_s2, leafS3_of_sq c4299_s3,
   c4299_iso, leafR8_of_sq c4299_nof2 c4299_nof3 c4299_nof4z⟩
theorem not_tile'_4299 (D : CongruentDissection 4299) : False :=
  not_tile_of_conditions' 4299 C'_4299 D

private theorem c4301_sqf   : LeafSqf 4301   := by decide +kernel
private theorem c4301_range : LeafRange 4301  := by decide +kernel
private theorem c4301_ell   : LeafEll 4301    := by decide +kernel
private theorem c4301_nsq   : NSqChkSq 4301   := by decide +kernel
private theorem c4301_har   : HArithChkSq 4301 := by decide +kernel
private theorem c4301_r     : LeafR 4301      := by decide +kernel
private theorem c4301_e'    : LeafE' 4301     := by decide +kernel
private theorem c4301_f1    : LeafF1 4301     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4301_s2    : S2ChkSq 4301    := by decide +kernel
private theorem c4301_s3    : S3ChkSq 4301    := by decide +kernel
private theorem c4301_iso   : LeafIso 4301    := by decide +kernel
private theorem c4301_nof2  : NoF2ChkSq 4301  := by decide +kernel
private theorem c4301_nof3  : NoF3ChkSq 4301  := by decide +kernel
private theorem c4301_nof4z : NoF4zChkSq 4301 := by decide +kernel
theorem C'_4301 : C' 4301 :=
  ⟨c4301_sqf, c4301_range, c4301_ell, leafNSq_of_sq c4301_nsq, leafHAr_of_sq c4301_har,
   c4301_r, c4301_e', c4301_f1, leafS2_of_sq c4301_s2, leafS3_of_sq c4301_s3,
   c4301_iso, leafR8_of_sq c4301_nof2 c4301_nof3 c4301_nof4z⟩
theorem not_tile'_4301 (D : CongruentDissection 4301) : False :=
  not_tile_of_conditions' 4301 C'_4301 D

private theorem c4303_sqf   : LeafSqf 4303   := by decide +kernel
private theorem c4303_range : LeafRange 4303  := by decide +kernel
private theorem c4303_ell   : LeafEll 4303    := by decide +kernel
private theorem c4303_nsq   : NSqChkSq 4303   := by decide +kernel
private theorem c4303_har   : HArithChkSq 4303 := by decide +kernel
private theorem c4303_r     : LeafR 4303      := by decide +kernel
private theorem c4303_e'    : LeafE' 4303     := by decide +kernel
private theorem c4303_f1    : LeafF1 4303     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4303_s2    : S2ChkSq 4303    := by decide +kernel
private theorem c4303_s3    : S3ChkSq 4303    := by decide +kernel
private theorem c4303_iso   : LeafIso 4303    := by decide +kernel
private theorem c4303_nof2  : NoF2ChkSq 4303  := by decide +kernel
private theorem c4303_nof3  : NoF3ChkSq 4303  := by decide +kernel
private theorem c4303_nof4z : NoF4zChkSq 4303 := by decide +kernel
theorem C'_4303 : C' 4303 :=
  ⟨c4303_sqf, c4303_range, c4303_ell, leafNSq_of_sq c4303_nsq, leafHAr_of_sq c4303_har,
   c4303_r, c4303_e', c4303_f1, leafS2_of_sq c4303_s2, leafS3_of_sq c4303_s3,
   c4303_iso, leafR8_of_sq c4303_nof2 c4303_nof3 c4303_nof4z⟩
theorem not_tile'_4303 (D : CongruentDissection 4303) : False :=
  not_tile_of_conditions' 4303 C'_4303 D

private theorem c4307_sqf   : LeafSqf 4307   := by decide +kernel
private theorem c4307_range : LeafRange 4307  := by decide +kernel
private theorem c4307_ell   : LeafEll 4307    := by decide +kernel
private theorem c4307_nsq   : NSqChkSq 4307   := by decide +kernel
private theorem c4307_har   : HArithChkSq 4307 := by decide +kernel
private theorem c4307_r     : LeafR 4307      := by decide +kernel
private theorem c4307_e'    : LeafE' 4307     := by decide +kernel
private theorem c4307_f1    : LeafF1 4307     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4307_s2    : S2ChkSq 4307    := by decide +kernel
private theorem c4307_s3    : S3ChkSq 4307    := by decide +kernel
private theorem c4307_iso   : LeafIso 4307    := by decide +kernel
private theorem c4307_nof2  : NoF2ChkSq 4307  := by decide +kernel
private theorem c4307_nof3  : NoF3ChkSq 4307  := by decide +kernel
private theorem c4307_nof4z : NoF4zChkSq 4307 := by decide +kernel
theorem C'_4307 : C' 4307 :=
  ⟨c4307_sqf, c4307_range, c4307_ell, leafNSq_of_sq c4307_nsq, leafHAr_of_sq c4307_har,
   c4307_r, c4307_e', c4307_f1, leafS2_of_sq c4307_s2, leafS3_of_sq c4307_s3,
   c4307_iso, leafR8_of_sq c4307_nof2 c4307_nof3 c4307_nof4z⟩
theorem not_tile'_4307 (D : CongruentDissection 4307) : False :=
  not_tile_of_conditions' 4307 C'_4307 D

private theorem c4309_sqf   : LeafSqf 4309   := by decide +kernel
private theorem c4309_range : LeafRange 4309  := by decide +kernel
private theorem c4309_ell   : LeafEll 4309    := by decide +kernel
private theorem c4309_nsq   : NSqChkSq 4309   := by decide +kernel
private theorem c4309_har   : HArithChkSq 4309 := by decide +kernel
private theorem c4309_r     : LeafR 4309      := by decide +kernel
private theorem c4309_e'    : LeafE' 4309     := by decide +kernel
private theorem c4309_f1    : LeafF1 4309     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4309_s2    : S2ChkSq 4309    := by decide +kernel
private theorem c4309_s3    : S3ChkSq 4309    := by decide +kernel
private theorem c4309_iso   : LeafIso 4309    := by decide +kernel
private theorem c4309_nof2  : NoF2ChkSq 4309  := by decide +kernel
private theorem c4309_nof3  : NoF3ChkSq 4309  := by decide +kernel
private theorem c4309_nof4z : NoF4zChkSq 4309 := by decide +kernel
theorem C'_4309 : C' 4309 :=
  ⟨c4309_sqf, c4309_range, c4309_ell, leafNSq_of_sq c4309_nsq, leafHAr_of_sq c4309_har,
   c4309_r, c4309_e', c4309_f1, leafS2_of_sq c4309_s2, leafS3_of_sq c4309_s3,
   c4309_iso, leafR8_of_sq c4309_nof2 c4309_nof3 c4309_nof4z⟩
theorem not_tile'_4309 (D : CongruentDissection 4309) : False :=
  not_tile_of_conditions' 4309 C'_4309 D

end Erdos634.Draft.AllN2
