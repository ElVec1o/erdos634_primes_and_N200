/- AllN3Check3: N = 805, 861, 885, 903, 915, 987.
   Squarefree values excluded by `AllN3.C3` and not by `R8ZF.C''` (through the discriminant table of the `π/3` pairs,
   or, for 438 and 805, the base-`α` divisibility).  Kernel checks, leaf by leaf, with square-root-bounded loops.
   Composite-N work.  No sorry, no native_decide. -/
import Erdos634.Draft.AllN3Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN3
open Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.R8ZF Erdos634.Geometry
open Erdos634.Draft.TileCountFamilies (TileCount)

private theorem c805_sqf   : LeafSqf 805   := by decide +kernel
private theorem c805_range : LeafRange 805  := by decide +kernel
private theorem c805_ell   : LeafEll 805    := by decide +kernel
private theorem c805_nsq   : NSqChkSq 805   := by decide +kernel
private theorem c805_har   : HArithChkSq 805 := by decide +kernel
private theorem c805_r     : LeafR 805      := by decide +kernel
private theorem c805_e     : LeafEsq 805    := by decide +kernel
private theorem c805_f1    : LeafF1 805     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c805_s2    : S2ChkSq 805    := by decide +kernel
private theorem c805_s3    : S3ChkDSq 805   := by decide +kernel
private theorem c805_iso   : LeafIso 805    := by decide +kernel
private theorem c805_nof2  : NoF2ChkSq 805  := by decide +kernel
private theorem c805_nof3  : NoF3zChkSq 805 := by decide +kernel
private theorem c805_nof4z : NoF4zChkSq 805 := by decide +kernel
theorem C3_805 : C3 805 :=
  ⟨c805_sqf, c805_range, c805_ell, leafNSq_of_sq c805_nsq, leafHAr_of_sq c805_har,
   c805_r, c805_e, c805_f1, leafS2_of_sq c805_s2, s3ChkD_of_sq c805_s3, c805_iso,
   leafR8z_of_sq c805_nof2 c805_nof3 c805_nof4z⟩
theorem not_tileCount_805 : ¬ TileCount 805 := not_tileCount_of_c3 C3_805

private theorem c861_sqf   : LeafSqf 861   := by decide +kernel
private theorem c861_range : LeafRange 861  := by decide +kernel
private theorem c861_ell   : LeafEll 861    := by decide +kernel
private theorem c861_nsq   : NSqChkSq 861   := by decide +kernel
private theorem c861_har   : HArithChkSq 861 := by decide +kernel
private theorem c861_r     : LeafR 861      := by decide +kernel
private theorem c861_e     : LeafEsq 861    := by decide +kernel
private theorem c861_f1    : LeafF1 861     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c861_s2    : S2ChkSq 861    := by decide +kernel
private theorem c861_s3    : S3ChkDSq 861   := by decide +kernel
private theorem c861_iso   : LeafIso 861    := by decide +kernel
private theorem c861_nof2  : NoF2ChkSq 861  := by decide +kernel
private theorem c861_nof3  : NoF3zChkSq 861 := by decide +kernel
private theorem c861_nof4z : NoF4zChkSq 861 := by decide +kernel
theorem C3_861 : C3 861 :=
  ⟨c861_sqf, c861_range, c861_ell, leafNSq_of_sq c861_nsq, leafHAr_of_sq c861_har,
   c861_r, c861_e, c861_f1, leafS2_of_sq c861_s2, s3ChkD_of_sq c861_s3, c861_iso,
   leafR8z_of_sq c861_nof2 c861_nof3 c861_nof4z⟩
theorem not_tileCount_861 : ¬ TileCount 861 := not_tileCount_of_c3 C3_861

private theorem c885_sqf   : LeafSqf 885   := by decide +kernel
private theorem c885_range : LeafRange 885  := by decide +kernel
private theorem c885_ell   : LeafEll 885    := by decide +kernel
private theorem c885_nsq   : NSqChkSq 885   := by decide +kernel
private theorem c885_har   : HArithChkSq 885 := by decide +kernel
private theorem c885_r     : LeafR 885      := by decide +kernel
private theorem c885_e     : LeafEsq 885    := by decide +kernel
private theorem c885_f1    : LeafF1 885     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c885_s2    : S2ChkSq 885    := by decide +kernel
private theorem c885_s3    : S3ChkDSq 885   := by decide +kernel
private theorem c885_iso   : LeafIso 885    := by decide +kernel
private theorem c885_nof2  : NoF2ChkSq 885  := by decide +kernel
private theorem c885_nof3  : NoF3zChkSq 885 := by decide +kernel
private theorem c885_nof4z : NoF4zChkSq 885 := by decide +kernel
theorem C3_885 : C3 885 :=
  ⟨c885_sqf, c885_range, c885_ell, leafNSq_of_sq c885_nsq, leafHAr_of_sq c885_har,
   c885_r, c885_e, c885_f1, leafS2_of_sq c885_s2, s3ChkD_of_sq c885_s3, c885_iso,
   leafR8z_of_sq c885_nof2 c885_nof3 c885_nof4z⟩
theorem not_tileCount_885 : ¬ TileCount 885 := not_tileCount_of_c3 C3_885

private theorem c903_sqf   : LeafSqf 903   := by decide +kernel
private theorem c903_range : LeafRange 903  := by decide +kernel
private theorem c903_ell   : LeafEll 903    := by decide +kernel
private theorem c903_nsq   : NSqChkSq 903   := by decide +kernel
private theorem c903_har   : HArithChkSq 903 := by decide +kernel
private theorem c903_r     : LeafR 903      := by decide +kernel
private theorem c903_e     : LeafEsq 903    := by decide +kernel
private theorem c903_f1    : LeafF1 903     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c903_s2    : S2ChkSq 903    := by decide +kernel
private theorem c903_s3    : S3ChkDSq 903   := by decide +kernel
private theorem c903_iso   : LeafIso 903    := by decide +kernel
private theorem c903_nof2  : NoF2ChkSq 903  := by decide +kernel
private theorem c903_nof3  : NoF3zChkSq 903 := by decide +kernel
private theorem c903_nof4z : NoF4zChkSq 903 := by decide +kernel
theorem C3_903 : C3 903 :=
  ⟨c903_sqf, c903_range, c903_ell, leafNSq_of_sq c903_nsq, leafHAr_of_sq c903_har,
   c903_r, c903_e, c903_f1, leafS2_of_sq c903_s2, s3ChkD_of_sq c903_s3, c903_iso,
   leafR8z_of_sq c903_nof2 c903_nof3 c903_nof4z⟩
theorem not_tileCount_903 : ¬ TileCount 903 := not_tileCount_of_c3 C3_903

private theorem c915_sqf   : LeafSqf 915   := by decide +kernel
private theorem c915_range : LeafRange 915  := by decide +kernel
private theorem c915_ell   : LeafEll 915    := by decide +kernel
private theorem c915_nsq   : NSqChkSq 915   := by decide +kernel
private theorem c915_har   : HArithChkSq 915 := by decide +kernel
private theorem c915_r     : LeafR 915      := by decide +kernel
private theorem c915_e     : LeafEsq 915    := by decide +kernel
private theorem c915_f1    : LeafF1 915     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c915_s2    : S2ChkSq 915    := by decide +kernel
private theorem c915_s3    : S3ChkDSq 915   := by decide +kernel
private theorem c915_iso   : LeafIso 915    := by decide +kernel
private theorem c915_nof2  : NoF2ChkSq 915  := by decide +kernel
private theorem c915_nof3  : NoF3zChkSq 915 := by decide +kernel
private theorem c915_nof4z : NoF4zChkSq 915 := by decide +kernel
theorem C3_915 : C3 915 :=
  ⟨c915_sqf, c915_range, c915_ell, leafNSq_of_sq c915_nsq, leafHAr_of_sq c915_har,
   c915_r, c915_e, c915_f1, leafS2_of_sq c915_s2, s3ChkD_of_sq c915_s3, c915_iso,
   leafR8z_of_sq c915_nof2 c915_nof3 c915_nof4z⟩
theorem not_tileCount_915 : ¬ TileCount 915 := not_tileCount_of_c3 C3_915

private theorem c987_sqf   : LeafSqf 987   := by decide +kernel
private theorem c987_range : LeafRange 987  := by decide +kernel
private theorem c987_ell   : LeafEll 987    := by decide +kernel
private theorem c987_nsq   : NSqChkSq 987   := by decide +kernel
private theorem c987_har   : HArithChkSq 987 := by decide +kernel
private theorem c987_r     : LeafR 987      := by decide +kernel
private theorem c987_e     : LeafEsq 987    := by decide +kernel
private theorem c987_f1    : LeafF1 987     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c987_s2    : S2ChkSq 987    := by decide +kernel
private theorem c987_s3    : S3ChkDSq 987   := by decide +kernel
private theorem c987_iso   : LeafIso 987    := by decide +kernel
private theorem c987_nof2  : NoF2ChkSq 987  := by decide +kernel
private theorem c987_nof3  : NoF3zChkSq 987 := by decide +kernel
private theorem c987_nof4z : NoF4zChkSq 987 := by decide +kernel
theorem C3_987 : C3 987 :=
  ⟨c987_sqf, c987_range, c987_ell, leafNSq_of_sq c987_nsq, leafHAr_of_sq c987_har,
   c987_r, c987_e, c987_f1, leafS2_of_sq c987_s2, s3ChkD_of_sq c987_s3, c987_iso,
   leafR8z_of_sq c987_nof2 c987_nof3 c987_nof4z⟩
theorem not_tileCount_987 : ¬ TileCount 987 := not_tileCount_of_c3 C3_987

end Erdos634.Draft.AllN3

#print axioms Erdos634.Draft.AllN3.not_tileCount_805
