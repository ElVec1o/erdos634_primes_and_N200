/- AllN2Check206: N = 3981, 3982, 3983, 3991, 3995
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3981_sqf   : LeafSqf 3981   := by decide +kernel
private theorem c3981_range : LeafRange 3981  := by decide +kernel
private theorem c3981_ell   : LeafEll 3981    := by decide +kernel
private theorem c3981_nsq   : NSqChkSq 3981   := by decide +kernel
private theorem c3981_har   : HArithChkSq 3981 := by decide +kernel
private theorem c3981_r     : LeafR 3981      := by decide +kernel
private theorem c3981_e'    : LeafE' 3981     := by decide +kernel
private theorem c3981_f1    : LeafF1 3981     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3981_s2    : S2ChkSq 3981    := by decide +kernel
private theorem c3981_s3    : S3ChkSq 3981    := by decide +kernel
private theorem c3981_iso   : LeafIso 3981    := by decide +kernel
private theorem c3981_nof2  : NoF2ChkSq 3981  := by decide +kernel
private theorem c3981_nof3  : NoF3ChkSq 3981  := by decide +kernel
private theorem c3981_nof4z : NoF4zChkSq 3981 := by decide +kernel
theorem C'_3981 : C' 3981 :=
  ⟨c3981_sqf, c3981_range, c3981_ell, leafNSq_of_sq c3981_nsq, leafHAr_of_sq c3981_har,
   c3981_r, c3981_e', c3981_f1, leafS2_of_sq c3981_s2, leafS3_of_sq c3981_s3,
   c3981_iso, leafR8_of_sq c3981_nof2 c3981_nof3 c3981_nof4z⟩
theorem not_tile'_3981 (D : CongruentDissection 3981) : False :=
  not_tile_of_conditions' 3981 C'_3981 D

private theorem c3982_sqf   : LeafSqf 3982   := by decide +kernel
private theorem c3982_range : LeafRange 3982  := by decide +kernel
private theorem c3982_ell   : LeafEll 3982    := by decide +kernel
private theorem c3982_nsq   : NSqChkSq 3982   := by decide +kernel
private theorem c3982_har   : HArithChkSq 3982 := by decide +kernel
private theorem c3982_r     : LeafR 3982      := by decide +kernel
private theorem c3982_e'    : LeafE' 3982     := by decide +kernel
private theorem c3982_f1    : LeafF1 3982     := Or.inl (by decide)
private theorem c3982_s2    : S2ChkSq 3982    := by decide +kernel
private theorem c3982_s3    : S3ChkSq 3982    := by decide +kernel
private theorem c3982_iso   : LeafIso 3982    := by decide +kernel
private theorem c3982_nof2  : NoF2ChkSq 3982  := by decide +kernel
private theorem c3982_nof3  : NoF3ChkSq 3982  := by decide +kernel
private theorem c3982_nof4z : NoF4zChkSq 3982 := by decide +kernel
theorem C'_3982 : C' 3982 :=
  ⟨c3982_sqf, c3982_range, c3982_ell, leafNSq_of_sq c3982_nsq, leafHAr_of_sq c3982_har,
   c3982_r, c3982_e', c3982_f1, leafS2_of_sq c3982_s2, leafS3_of_sq c3982_s3,
   c3982_iso, leafR8_of_sq c3982_nof2 c3982_nof3 c3982_nof4z⟩
theorem not_tile'_3982 (D : CongruentDissection 3982) : False :=
  not_tile_of_conditions' 3982 C'_3982 D

private theorem c3983_sqf   : LeafSqf 3983   := by decide +kernel
private theorem c3983_range : LeafRange 3983  := by decide +kernel
private theorem c3983_ell   : LeafEll 3983    := by decide +kernel
private theorem c3983_nsq   : NSqChkSq 3983   := by decide +kernel
private theorem c3983_har   : HArithChkSq 3983 := by decide +kernel
private theorem c3983_r     : LeafR 3983      := by decide +kernel
private theorem c3983_e'    : LeafE' 3983     := by decide +kernel
private theorem c3983_f1    : LeafF1 3983     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3983_s2    : S2ChkSq 3983    := by decide +kernel
private theorem c3983_s3    : S3ChkSq 3983    := by decide +kernel
private theorem c3983_iso   : LeafIso 3983    := by decide +kernel
private theorem c3983_nof2  : NoF2ChkSq 3983  := by decide +kernel
private theorem c3983_nof3  : NoF3ChkSq 3983  := by decide +kernel
private theorem c3983_nof4z : NoF4zChkSq 3983 := by decide +kernel
theorem C'_3983 : C' 3983 :=
  ⟨c3983_sqf, c3983_range, c3983_ell, leafNSq_of_sq c3983_nsq, leafHAr_of_sq c3983_har,
   c3983_r, c3983_e', c3983_f1, leafS2_of_sq c3983_s2, leafS3_of_sq c3983_s3,
   c3983_iso, leafR8_of_sq c3983_nof2 c3983_nof3 c3983_nof4z⟩
theorem not_tile'_3983 (D : CongruentDissection 3983) : False :=
  not_tile_of_conditions' 3983 C'_3983 D

private theorem c3991_sqf   : LeafSqf 3991   := by decide +kernel
private theorem c3991_range : LeafRange 3991  := by decide +kernel
private theorem c3991_ell   : LeafEll 3991    := by decide +kernel
private theorem c3991_nsq   : NSqChkSq 3991   := by decide +kernel
private theorem c3991_har   : HArithChkSq 3991 := by decide +kernel
private theorem c3991_r     : LeafR 3991      := by decide +kernel
private theorem c3991_e'    : LeafE' 3991     := by decide +kernel
private theorem c3991_f1    : LeafF1 3991     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3991_s2    : S2ChkSq 3991    := by decide +kernel
private theorem c3991_s3    : S3ChkSq 3991    := by decide +kernel
private theorem c3991_iso   : LeafIso 3991    := by decide +kernel
private theorem c3991_nof2  : NoF2ChkSq 3991  := by decide +kernel
private theorem c3991_nof3  : NoF3ChkSq 3991  := by decide +kernel
private theorem c3991_nof4z : NoF4zChkSq 3991 := by decide +kernel
theorem C'_3991 : C' 3991 :=
  ⟨c3991_sqf, c3991_range, c3991_ell, leafNSq_of_sq c3991_nsq, leafHAr_of_sq c3991_har,
   c3991_r, c3991_e', c3991_f1, leafS2_of_sq c3991_s2, leafS3_of_sq c3991_s3,
   c3991_iso, leafR8_of_sq c3991_nof2 c3991_nof3 c3991_nof4z⟩
theorem not_tile'_3991 (D : CongruentDissection 3991) : False :=
  not_tile_of_conditions' 3991 C'_3991 D

private theorem c3995_sqf   : LeafSqf 3995   := by decide +kernel
private theorem c3995_range : LeafRange 3995  := by decide +kernel
private theorem c3995_ell   : LeafEll 3995    := by decide +kernel
private theorem c3995_nsq   : NSqChkSq 3995   := by decide +kernel
private theorem c3995_har   : HArithChkSq 3995 := by decide +kernel
private theorem c3995_r     : LeafR 3995      := by decide +kernel
private theorem c3995_e'    : LeafE' 3995     := by decide +kernel
private theorem c3995_f1    : LeafF1 3995     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3995_s2    : S2ChkSq 3995    := by decide +kernel
private theorem c3995_s3    : S3ChkSq 3995    := by decide +kernel
private theorem c3995_iso   : LeafIso 3995    := by decide +kernel
private theorem c3995_nof2  : NoF2ChkSq 3995  := by decide +kernel
private theorem c3995_nof3  : NoF3ChkSq 3995  := by decide +kernel
private theorem c3995_nof4z : NoF4zChkSq 3995 := by decide +kernel
theorem C'_3995 : C' 3995 :=
  ⟨c3995_sqf, c3995_range, c3995_ell, leafNSq_of_sq c3995_nsq, leafHAr_of_sq c3995_har,
   c3995_r, c3995_e', c3995_f1, leafS2_of_sq c3995_s2, leafS3_of_sq c3995_s3,
   c3995_iso, leafR8_of_sq c3995_nof2 c3995_nof3 c3995_nof4z⟩
theorem not_tile'_3995 (D : CongruentDissection 3995) : False :=
  not_tile_of_conditions' 3995 C'_3995 D

end Erdos634.Draft.AllN2
