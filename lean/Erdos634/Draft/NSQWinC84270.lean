/-
Draft/NSQWinC84270.lean -- `no_dissection_c84270` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 8 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_84270 : NQChkW 84270 := by decide +kernel
theorem cl2w_84270 : EllOrAsqW 84270 := by decide +kernel
theorem cl2_84270 : (EllChk2 84270 ∨ AsqChk 84270) := ellAsq_of_W cl2w_84270
theorem cl3_84270 : NSqChkSq 84270 := by decide +kernel
theorem cl4_84270 : HArithChkSq 84270 := by decide +kernel
theorem cl5_84270 : (84270 % 2 = 1 ∨ (84270 % 2 = 0 ∧ NHSqChkSq 84270)) := by decide +kernel
theorem cl6_84270 : LeafEsqW 84270 := by decide +kernel
theorem cl7_84270 : (84270 % 4 = 2 ∨ F1ChkParW 84270) := by decide +kernel
theorem cl10_84270 : IsoH9bChkW 84270 := by decide +kernel
theorem cl12_84270 : GammaChkDW 84270 := by decide +kernel
theorem cl13_84270 : S1t2ChkW 84270 := by decide +kernel
theorem cl14_84270 : RWChkT2W 84270 := by decide +kernel
theorem cl15_84270 : S5wChkW 84270 := by decide +kernel
theorem cf2z_84270 : F2z 84270 := by decide +kernel
theorem c_s2_84270_0 : ChunkP (S2P 84270) 0 205 := by decide +kernel
theorem c_s2_84270_1 : ChunkP (S2P 84270) 205 290 := by decide +kernel
theorem c_s2_84270_2 : ChunkP (S2P 84270) 290 356 := by decide +kernel
theorem c_s2_84270_3 : ChunkP (S2P 84270) 356 411 := by decide +kernel
theorem c_s2_84270_4 : ChunkP (S2P 84270) 411 459 := by decide +kernel
theorem c_s2_84270_5 : ChunkP (S2P 84270) 459 503 := by decide +kernel
theorem c_s2_84270_6 : ChunkP (S2P 84270) 503 543 := by decide +kernel
theorem c_s2_84270_7 : ChunkP (S2P 84270) 543 (Nat.sqrt (4 * 84270) + 1) := by decide +kernel
theorem c_s3_84270_0 : ChunkP (S3P 84270) 0 36 := by decide +kernel
theorem c_s3_84270_1 : ChunkP (S3P 84270) 36 73 := by decide +kernel
theorem c_s3_84270_2 : ChunkP (S3P 84270) 73 109 := by decide +kernel
theorem c_s3_84270_3 : ChunkP (S3P 84270) 109 146 := by decide +kernel
theorem c_s3_84270_4 : ChunkP (S3P 84270) 146 182 := by decide +kernel
theorem c_s3_84270_5 : ChunkP (S3P 84270) 182 218 := by decide +kernel
theorem c_s3_84270_6 : ChunkP (S3P 84270) 218 255 := by decide +kernel
theorem c_s3_84270_7 : ChunkP (S3P 84270) 255 (Nat.sqrt 84270 + 1) := by decide +kernel
theorem c_f4_84270_0 : ChunkP (F4zP 84270) 0 36 := by decide +kernel
theorem c_f4_84270_1 : ChunkP (F4zP 84270) 36 73 := by decide +kernel
theorem c_f4_84270_2 : ChunkP (F4zP 84270) 73 109 := by decide +kernel
theorem c_f4_84270_3 : ChunkP (F4zP 84270) 109 146 := by decide +kernel
theorem c_f4_84270_4 : ChunkP (F4zP 84270) 146 182 := by decide +kernel
theorem c_f4_84270_5 : ChunkP (F4zP 84270) 182 218 := by decide +kernel
theorem c_f4_84270_6 : ChunkP (F4zP 84270) 218 255 := by decide +kernel
theorem c_f4_84270_7 : ChunkP (F4zP 84270) 255 (Nat.sqrt 84270 + 1) := by decide +kernel
theorem c_f2_84270_0 : ChunkP (F2P 84270) 0 36 := by decide +kernel
theorem c_f2_84270_1 : ChunkP (F2P 84270) 36 73 := by decide +kernel
theorem c_f2_84270_2 : ChunkP (F2P 84270) 73 109 := by decide +kernel
theorem c_f2_84270_3 : ChunkP (F2P 84270) 109 146 := by decide +kernel
theorem c_f2_84270_4 : ChunkP (F2P 84270) 146 182 := by decide +kernel
theorem c_f2_84270_5 : ChunkP (F2P 84270) 182 218 := by decide +kernel
theorem c_f2_84270_6 : ChunkP (F2P 84270) 218 255 := by decide +kernel
theorem c_f2_84270_7 : ChunkP (F2P 84270) 255 (Nat.sqrt 84270 + 1) := by decide +kernel
theorem c_f3_84270_0 : ChunkP (F3zP 84270) 0 36 := by decide +kernel
theorem c_f3_84270_1 : ChunkP (F3zP 84270) 36 73 := by decide +kernel
theorem c_f3_84270_2 : ChunkP (F3zP 84270) 73 109 := by decide +kernel
theorem c_f3_84270_3 : ChunkP (F3zP 84270) 109 146 := by decide +kernel
theorem c_f3_84270_4 : ChunkP (F3zP 84270) 146 182 := by decide +kernel
theorem c_f3_84270_5 : ChunkP (F3zP 84270) 182 218 := by decide +kernel
theorem c_f3_84270_6 : ChunkP (F3zP 84270) 218 255 := by decide +kernel
theorem c_f3_84270_7 : ChunkP (F3zP 84270) 255 (Nat.sqrt 84270 + 1) := by decide +kernel

theorem cl8_84270 : S2ChkSq 84270 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_84270_0 c_s2_84270_1) c_s2_84270_2) c_s2_84270_3) c_s2_84270_4) c_s2_84270_5) c_s2_84270_6) c_s2_84270_7))
theorem cl9_84270 : S3ChkSq 84270 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_84270_0 c_s3_84270_1) c_s3_84270_2) c_s3_84270_3) c_s3_84270_4) c_s3_84270_5) c_s3_84270_6) c_s3_84270_7))
theorem cl11_84270 : (NoF2ChkSq 84270 ∧ NoF3zChkSq 84270 ∧ NoF4zChkSq 84270) :=
  ⟨f2Sq_of_P cf2z_84270 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_84270_0 c_f2_84270_1) c_f2_84270_2) c_f2_84270_3) c_f2_84270_4) c_f2_84270_5) c_f2_84270_6) c_f2_84270_7)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_84270_0 c_f3_84270_1) c_f3_84270_2) c_f3_84270_3) c_f3_84270_4) c_f3_84270_5) c_f3_84270_6) c_f3_84270_7)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_84270_0 c_f4_84270_1) c_f4_84270_2) c_f4_84270_3) c_f4_84270_4) c_f4_84270_5) c_f4_84270_6) c_f4_84270_7))⟩

theorem cnzETWD6_c84270 : CN'zETWD6 84270 :=
  ⟨cl1_84270, cl2_84270, cl3_84270, cl4_84270, cl5_84270, cl6_84270, cl7_84270, cl8_84270, cl9_84270, cl10_84270, cl11_84270, cl12_84270, cl13_84270, cl14_84270, cl15_84270⟩
theorem no_dissection_c84270 (D : CongruentDissection 84270) : False := not_tile_of_conditionsNSQzETWD6 84270 cnzETWD6_c84270 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c84270
