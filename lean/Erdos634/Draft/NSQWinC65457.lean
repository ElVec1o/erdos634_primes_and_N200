/-
Draft/NSQWinC65457.lean -- `no_dissection_c65457` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 6 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_65457 : NQChkW 65457 := by decide +kernel
theorem cl2w_65457 : EllOrAsqW 65457 := by decide +kernel
theorem cl2_65457 : (EllChk2 65457 ∨ AsqChk 65457) := ellAsq_of_W cl2w_65457
theorem cl3_65457 : NSqChkSq 65457 := by decide +kernel
theorem cl4_65457 : HArithChkSq 65457 := by decide +kernel
theorem cl5_65457 : (65457 % 2 = 1 ∨ (65457 % 2 = 0 ∧ NHSqChkSq 65457)) := by decide +kernel
theorem cl6_65457 : LeafEsqW 65457 := by decide +kernel
theorem cl7_65457 : (65457 % 4 = 2 ∨ F1ChkParW 65457) := by decide +kernel
theorem cl10_65457 : IsoH9bChkW 65457 := by decide +kernel
theorem cl12_65457 : GammaChkDW 65457 := by decide +kernel
theorem cl13_65457 : S1t2ChkW 65457 := by decide +kernel
theorem cl14_65457 : RWChkT2W 65457 := by decide +kernel
theorem cl15_65457 : S5wChkW 65457 := by decide +kernel
theorem cf2z_65457 : F2z 65457 := by decide +kernel
theorem c_s2_65457_0 : ChunkP (S2P 65457) 0 209 := by decide +kernel
theorem c_s2_65457_1 : ChunkP (S2P 65457) 209 296 := by decide +kernel
theorem c_s2_65457_2 : ChunkP (S2P 65457) 296 362 := by decide +kernel
theorem c_s2_65457_3 : ChunkP (S2P 65457) 362 418 := by decide +kernel
theorem c_s2_65457_4 : ChunkP (S2P 65457) 418 467 := by decide +kernel
theorem c_s2_65457_5 : ChunkP (S2P 65457) 467 (Nat.sqrt (4 * 65457) + 1) := by decide +kernel
theorem c_s3_65457_0 : ChunkP (S3P 65457) 0 43 := by decide +kernel
theorem c_s3_65457_1 : ChunkP (S3P 65457) 43 85 := by decide +kernel
theorem c_s3_65457_2 : ChunkP (S3P 65457) 85 128 := by decide +kernel
theorem c_s3_65457_3 : ChunkP (S3P 65457) 128 171 := by decide +kernel
theorem c_s3_65457_4 : ChunkP (S3P 65457) 171 213 := by decide +kernel
theorem c_s3_65457_5 : ChunkP (S3P 65457) 213 (Nat.sqrt 65457 + 1) := by decide +kernel
theorem c_f4_65457_0 : ChunkP (F4zP 65457) 0 43 := by decide +kernel
theorem c_f4_65457_1 : ChunkP (F4zP 65457) 43 85 := by decide +kernel
theorem c_f4_65457_2 : ChunkP (F4zP 65457) 85 128 := by decide +kernel
theorem c_f4_65457_3 : ChunkP (F4zP 65457) 128 171 := by decide +kernel
theorem c_f4_65457_4 : ChunkP (F4zP 65457) 171 213 := by decide +kernel
theorem c_f4_65457_5 : ChunkP (F4zP 65457) 213 (Nat.sqrt 65457 + 1) := by decide +kernel
theorem c_f2_65457_0 : ChunkP (F2P 65457) 0 43 := by decide +kernel
theorem c_f2_65457_1 : ChunkP (F2P 65457) 43 85 := by decide +kernel
theorem c_f2_65457_2 : ChunkP (F2P 65457) 85 128 := by decide +kernel
theorem c_f2_65457_3 : ChunkP (F2P 65457) 128 171 := by decide +kernel
theorem c_f2_65457_4 : ChunkP (F2P 65457) 171 213 := by decide +kernel
theorem c_f2_65457_5 : ChunkP (F2P 65457) 213 (Nat.sqrt 65457 + 1) := by decide +kernel
theorem c_f3_65457_0 : ChunkP (F3zP 65457) 0 43 := by decide +kernel
theorem c_f3_65457_1 : ChunkP (F3zP 65457) 43 85 := by decide +kernel
theorem c_f3_65457_2 : ChunkP (F3zP 65457) 85 128 := by decide +kernel
theorem c_f3_65457_3 : ChunkP (F3zP 65457) 128 171 := by decide +kernel
theorem c_f3_65457_4 : ChunkP (F3zP 65457) 171 213 := by decide +kernel
theorem c_f3_65457_5 : ChunkP (F3zP 65457) 213 (Nat.sqrt 65457 + 1) := by decide +kernel

theorem cl8_65457 : S2ChkSq 65457 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_65457_0 c_s2_65457_1) c_s2_65457_2) c_s2_65457_3) c_s2_65457_4) c_s2_65457_5))
theorem cl9_65457 : S3ChkSq 65457 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_65457_0 c_s3_65457_1) c_s3_65457_2) c_s3_65457_3) c_s3_65457_4) c_s3_65457_5))
theorem cl11_65457 : (NoF2ChkSq 65457 ∧ NoF3zChkSq 65457 ∧ NoF4zChkSq 65457) :=
  ⟨f2Sq_of_P cf2z_65457 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_65457_0 c_f2_65457_1) c_f2_65457_2) c_f2_65457_3) c_f2_65457_4) c_f2_65457_5)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_65457_0 c_f3_65457_1) c_f3_65457_2) c_f3_65457_3) c_f3_65457_4) c_f3_65457_5)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_65457_0 c_f4_65457_1) c_f4_65457_2) c_f4_65457_3) c_f4_65457_4) c_f4_65457_5))⟩

theorem cnzETWD6_c65457 : CN'zETWD6 65457 :=
  ⟨cl1_65457, cl2_65457, cl3_65457, cl4_65457, cl5_65457, cl6_65457, cl7_65457, cl8_65457, cl9_65457, cl10_65457, cl11_65457, cl12_65457, cl13_65457, cl14_65457, cl15_65457⟩
theorem no_dissection_c65457 (D : CongruentDissection 65457) : False := not_tile_of_conditionsNSQzETWD6 65457 cnzETWD6_c65457 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c65457
