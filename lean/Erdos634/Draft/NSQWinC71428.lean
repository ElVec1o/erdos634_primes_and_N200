/-
Draft/NSQWinC71428.lean -- `no_dissection_c71428` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 6 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_71428 : NQChkW 71428 := by decide +kernel
theorem cl2w_71428 : EllOrAsqW 71428 := by decide +kernel
theorem cl2_71428 : (EllChk2 71428 ∨ AsqChk 71428) := ellAsq_of_W cl2w_71428
theorem cl3_71428 : NSqChkSq 71428 := by decide +kernel
theorem cl4_71428 : HArithChkSq 71428 := by decide +kernel
theorem cl5_71428 : (71428 % 2 = 1 ∨ (71428 % 2 = 0 ∧ NHSqChkSq 71428)) := by decide +kernel
theorem cl6_71428 : LeafEsqW 71428 := by decide +kernel
theorem cl7_71428 : (71428 % 4 = 2 ∨ F1ChkParW 71428) := by decide +kernel
theorem cl10_71428 : IsoH9bChkW 71428 := by decide +kernel
theorem cl12_71428 : GammaChkDW 71428 := by decide +kernel
theorem cl13_71428 : S1t2ChkW 71428 := by decide +kernel
theorem cl14_71428 : RWChkT2W 71428 := by decide +kernel
theorem cl15_71428 : S5wChkW 71428 := by decide +kernel
theorem cf2z_71428 : F2z 71428 := by decide +kernel
theorem c_s2_71428_0 : ChunkP (S2P 71428) 0 218 := by decide +kernel
theorem c_s2_71428_1 : ChunkP (S2P 71428) 218 309 := by decide +kernel
theorem c_s2_71428_2 : ChunkP (S2P 71428) 309 378 := by decide +kernel
theorem c_s2_71428_3 : ChunkP (S2P 71428) 378 437 := by decide +kernel
theorem c_s2_71428_4 : ChunkP (S2P 71428) 437 488 := by decide +kernel
theorem c_s2_71428_5 : ChunkP (S2P 71428) 488 (Nat.sqrt (4 * 71428) + 1) := by decide +kernel
theorem c_s3_71428_0 : ChunkP (S3P 71428) 0 45 := by decide +kernel
theorem c_s3_71428_1 : ChunkP (S3P 71428) 45 89 := by decide +kernel
theorem c_s3_71428_2 : ChunkP (S3P 71428) 89 134 := by decide +kernel
theorem c_s3_71428_3 : ChunkP (S3P 71428) 134 179 := by decide +kernel
theorem c_s3_71428_4 : ChunkP (S3P 71428) 179 223 := by decide +kernel
theorem c_s3_71428_5 : ChunkP (S3P 71428) 223 (Nat.sqrt 71428 + 1) := by decide +kernel
theorem c_f4_71428_0 : ChunkP (F4zP 71428) 0 45 := by decide +kernel
theorem c_f4_71428_1 : ChunkP (F4zP 71428) 45 89 := by decide +kernel
theorem c_f4_71428_2 : ChunkP (F4zP 71428) 89 134 := by decide +kernel
theorem c_f4_71428_3 : ChunkP (F4zP 71428) 134 179 := by decide +kernel
theorem c_f4_71428_4 : ChunkP (F4zP 71428) 179 223 := by decide +kernel
theorem c_f4_71428_5 : ChunkP (F4zP 71428) 223 (Nat.sqrt 71428 + 1) := by decide +kernel
theorem c_f2_71428_0 : ChunkP (F2P 71428) 0 45 := by decide +kernel
theorem c_f2_71428_1 : ChunkP (F2P 71428) 45 89 := by decide +kernel
theorem c_f2_71428_2 : ChunkP (F2P 71428) 89 134 := by decide +kernel
theorem c_f2_71428_3 : ChunkP (F2P 71428) 134 179 := by decide +kernel
theorem c_f2_71428_4 : ChunkP (F2P 71428) 179 223 := by decide +kernel
theorem c_f2_71428_5 : ChunkP (F2P 71428) 223 (Nat.sqrt 71428 + 1) := by decide +kernel
theorem c_f3_71428_0 : ChunkP (F3zP 71428) 0 45 := by decide +kernel
theorem c_f3_71428_1 : ChunkP (F3zP 71428) 45 89 := by decide +kernel
theorem c_f3_71428_2 : ChunkP (F3zP 71428) 89 134 := by decide +kernel
theorem c_f3_71428_3 : ChunkP (F3zP 71428) 134 179 := by decide +kernel
theorem c_f3_71428_4 : ChunkP (F3zP 71428) 179 223 := by decide +kernel
theorem c_f3_71428_5 : ChunkP (F3zP 71428) 223 (Nat.sqrt 71428 + 1) := by decide +kernel

theorem cl8_71428 : S2ChkSq 71428 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_71428_0 c_s2_71428_1) c_s2_71428_2) c_s2_71428_3) c_s2_71428_4) c_s2_71428_5))
theorem cl9_71428 : S3ChkSq 71428 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_71428_0 c_s3_71428_1) c_s3_71428_2) c_s3_71428_3) c_s3_71428_4) c_s3_71428_5))
theorem cl11_71428 : (NoF2ChkSq 71428 ∧ NoF3zChkSq 71428 ∧ NoF4zChkSq 71428) :=
  ⟨f2Sq_of_P cf2z_71428 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_71428_0 c_f2_71428_1) c_f2_71428_2) c_f2_71428_3) c_f2_71428_4) c_f2_71428_5)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_71428_0 c_f3_71428_1) c_f3_71428_2) c_f3_71428_3) c_f3_71428_4) c_f3_71428_5)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_71428_0 c_f4_71428_1) c_f4_71428_2) c_f4_71428_3) c_f4_71428_4) c_f4_71428_5))⟩

theorem cnzETWD6_c71428 : CN'zETWD6 71428 :=
  ⟨cl1_71428, cl2_71428, cl3_71428, cl4_71428, cl5_71428, cl6_71428, cl7_71428, cl8_71428, cl9_71428, cl10_71428, cl11_71428, cl12_71428, cl13_71428, cl14_71428, cl15_71428⟩
theorem no_dissection_c71428 (D : CongruentDissection 71428) : False := not_tile_of_conditionsNSQzETWD6 71428 cnzETWD6_c71428 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c71428
