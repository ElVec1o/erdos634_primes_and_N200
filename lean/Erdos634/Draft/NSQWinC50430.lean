/-
Draft/NSQWinC50430.lean -- `no_dissection_c50430` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 5 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_50430 : NQChkW 50430 := by decide +kernel
theorem cl2w_50430 : EllOrAsqW 50430 := by decide +kernel
theorem cl2_50430 : (EllChk2 50430 ∨ AsqChk 50430) := ellAsq_of_W cl2w_50430
theorem cl3_50430 : NSqChkSq 50430 := by decide +kernel
theorem cl4_50430 : HArithChkSq 50430 := by decide +kernel
theorem cl5_50430 : (50430 % 2 = 1 ∨ (50430 % 2 = 0 ∧ NHSqChkSq 50430)) := by decide +kernel
theorem cl6_50430 : LeafEsqW 50430 := by decide +kernel
theorem cl7_50430 : (50430 % 4 = 2 ∨ F1ChkParW 50430) := by decide +kernel
theorem cl10_50430 : IsoH9bChkW 50430 := by decide +kernel
theorem cl12_50430 : GammaChkDW 50430 := by decide +kernel
theorem cl13_50430 : S1t2ChkW 50430 := by decide +kernel
theorem cl14_50430 : RWChkT2W 50430 := by decide +kernel
theorem cl15_50430 : S5wChkW 50430 := by decide +kernel
theorem cf2z_50430 : F2z 50430 := by decide +kernel
theorem c_s2_50430_0 : ChunkP (S2P 50430) 0 201 := by decide +kernel
theorem c_s2_50430_1 : ChunkP (S2P 50430) 201 285 := by decide +kernel
theorem c_s2_50430_2 : ChunkP (S2P 50430) 285 349 := by decide +kernel
theorem c_s2_50430_3 : ChunkP (S2P 50430) 349 402 := by decide +kernel
theorem c_s2_50430_4 : ChunkP (S2P 50430) 402 (Nat.sqrt (4 * 50430) + 1) := by decide +kernel
theorem c_s3_50430_0 : ChunkP (S3P 50430) 0 45 := by decide +kernel
theorem c_s3_50430_1 : ChunkP (S3P 50430) 45 90 := by decide +kernel
theorem c_s3_50430_2 : ChunkP (S3P 50430) 90 135 := by decide +kernel
theorem c_s3_50430_3 : ChunkP (S3P 50430) 135 180 := by decide +kernel
theorem c_s3_50430_4 : ChunkP (S3P 50430) 180 (Nat.sqrt 50430 + 1) := by decide +kernel
theorem c_f4_50430_0 : ChunkP (F4zP 50430) 0 45 := by decide +kernel
theorem c_f4_50430_1 : ChunkP (F4zP 50430) 45 90 := by decide +kernel
theorem c_f4_50430_2 : ChunkP (F4zP 50430) 90 135 := by decide +kernel
theorem c_f4_50430_3 : ChunkP (F4zP 50430) 135 180 := by decide +kernel
theorem c_f4_50430_4 : ChunkP (F4zP 50430) 180 (Nat.sqrt 50430 + 1) := by decide +kernel
theorem c_f2_50430_0 : ChunkP (F2P 50430) 0 45 := by decide +kernel
theorem c_f2_50430_1 : ChunkP (F2P 50430) 45 90 := by decide +kernel
theorem c_f2_50430_2 : ChunkP (F2P 50430) 90 135 := by decide +kernel
theorem c_f2_50430_3 : ChunkP (F2P 50430) 135 180 := by decide +kernel
theorem c_f2_50430_4 : ChunkP (F2P 50430) 180 (Nat.sqrt 50430 + 1) := by decide +kernel
theorem c_f3_50430_0 : ChunkP (F3zP 50430) 0 45 := by decide +kernel
theorem c_f3_50430_1 : ChunkP (F3zP 50430) 45 90 := by decide +kernel
theorem c_f3_50430_2 : ChunkP (F3zP 50430) 90 135 := by decide +kernel
theorem c_f3_50430_3 : ChunkP (F3zP 50430) 135 180 := by decide +kernel
theorem c_f3_50430_4 : ChunkP (F3zP 50430) 180 (Nat.sqrt 50430 + 1) := by decide +kernel

theorem cl8_50430 : S2ChkSq 50430 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s2_50430_0 c_s2_50430_1) c_s2_50430_2) c_s2_50430_3) c_s2_50430_4))
theorem cl9_50430 : S3ChkSq 50430 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s3_50430_0 c_s3_50430_1) c_s3_50430_2) c_s3_50430_3) c_s3_50430_4))
theorem cl11_50430 : (NoF2ChkSq 50430 ∧ NoF3zChkSq 50430 ∧ NoF4zChkSq 50430) :=
  ⟨f2Sq_of_P cf2z_50430 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f2_50430_0 c_f2_50430_1) c_f2_50430_2) c_f2_50430_3) c_f2_50430_4)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f3_50430_0 c_f3_50430_1) c_f3_50430_2) c_f3_50430_3) c_f3_50430_4)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f4_50430_0 c_f4_50430_1) c_f4_50430_2) c_f4_50430_3) c_f4_50430_4))⟩

theorem cnzETWD6_c50430 : CN'zETWD6 50430 :=
  ⟨cl1_50430, cl2_50430, cl3_50430, cl4_50430, cl5_50430, cl6_50430, cl7_50430, cl8_50430, cl9_50430, cl10_50430, cl11_50430, cl12_50430, cl13_50430, cl14_50430, cl15_50430⟩
theorem no_dissection_c50430 (D : CongruentDissection 50430) : False := not_tile_of_conditionsNSQzETWD6 50430 cnzETWD6_c50430 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c50430
