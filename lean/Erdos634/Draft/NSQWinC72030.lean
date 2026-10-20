/-
Draft/NSQWinC72030.lean -- `no_dissection_c72030` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 7 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_72030 : NQChkW 72030 := by decide +kernel
theorem cl2w_72030 : EllOrAsqW 72030 := by decide +kernel
theorem cl2_72030 : (EllChk2 72030 ∨ AsqChk 72030) := ellAsq_of_W cl2w_72030
theorem cl3_72030 : NSqChkSq 72030 := by decide +kernel
theorem cl4_72030 : HArithChkSq 72030 := by decide +kernel
theorem cl5_72030 : (72030 % 2 = 1 ∨ (72030 % 2 = 0 ∧ NHSqChkSq 72030)) := by decide +kernel
theorem cl6_72030 : LeafEsqW 72030 := by decide +kernel
theorem cl7_72030 : (72030 % 4 = 2 ∨ F1ChkParW 72030) := by decide +kernel
theorem cl10_72030 : IsoH9bChkW 72030 := by decide +kernel
theorem cl12_72030 : GammaChkDW 72030 := by decide +kernel
theorem cl13_72030 : S1t2ChkW 72030 := by decide +kernel
theorem cl14_72030 : RWChkT2W 72030 := by decide +kernel
theorem cl15_72030 : S5wChkW 72030 := by decide +kernel
theorem cf2z_72030 : F2z 72030 := by decide +kernel
theorem c_s2_72030_0 : ChunkP (S2P 72030) 0 203 := by decide +kernel
theorem c_s2_72030_1 : ChunkP (S2P 72030) 203 287 := by decide +kernel
theorem c_s2_72030_2 : ChunkP (S2P 72030) 287 352 := by decide +kernel
theorem c_s2_72030_3 : ChunkP (S2P 72030) 352 406 := by decide +kernel
theorem c_s2_72030_4 : ChunkP (S2P 72030) 406 454 := by decide +kernel
theorem c_s2_72030_5 : ChunkP (S2P 72030) 454 497 := by decide +kernel
theorem c_s2_72030_6 : ChunkP (S2P 72030) 497 (Nat.sqrt (4 * 72030) + 1) := by decide +kernel
theorem c_s3_72030_0 : ChunkP (S3P 72030) 0 38 := by decide +kernel
theorem c_s3_72030_1 : ChunkP (S3P 72030) 38 77 := by decide +kernel
theorem c_s3_72030_2 : ChunkP (S3P 72030) 77 115 := by decide +kernel
theorem c_s3_72030_3 : ChunkP (S3P 72030) 115 154 := by decide +kernel
theorem c_s3_72030_4 : ChunkP (S3P 72030) 154 192 := by decide +kernel
theorem c_s3_72030_5 : ChunkP (S3P 72030) 192 231 := by decide +kernel
theorem c_s3_72030_6 : ChunkP (S3P 72030) 231 (Nat.sqrt 72030 + 1) := by decide +kernel
theorem c_f4_72030_0 : ChunkP (F4zP 72030) 0 38 := by decide +kernel
theorem c_f4_72030_1 : ChunkP (F4zP 72030) 38 77 := by decide +kernel
theorem c_f4_72030_2 : ChunkP (F4zP 72030) 77 115 := by decide +kernel
theorem c_f4_72030_3 : ChunkP (F4zP 72030) 115 154 := by decide +kernel
theorem c_f4_72030_4 : ChunkP (F4zP 72030) 154 192 := by decide +kernel
theorem c_f4_72030_5 : ChunkP (F4zP 72030) 192 231 := by decide +kernel
theorem c_f4_72030_6 : ChunkP (F4zP 72030) 231 (Nat.sqrt 72030 + 1) := by decide +kernel
theorem c_f2_72030_0 : ChunkP (F2P 72030) 0 38 := by decide +kernel
theorem c_f2_72030_1 : ChunkP (F2P 72030) 38 77 := by decide +kernel
theorem c_f2_72030_2 : ChunkP (F2P 72030) 77 115 := by decide +kernel
theorem c_f2_72030_3 : ChunkP (F2P 72030) 115 154 := by decide +kernel
theorem c_f2_72030_4 : ChunkP (F2P 72030) 154 192 := by decide +kernel
theorem c_f2_72030_5 : ChunkP (F2P 72030) 192 231 := by decide +kernel
theorem c_f2_72030_6 : ChunkP (F2P 72030) 231 (Nat.sqrt 72030 + 1) := by decide +kernel
theorem c_f3_72030_0 : ChunkP (F3zP 72030) 0 38 := by decide +kernel
theorem c_f3_72030_1 : ChunkP (F3zP 72030) 38 77 := by decide +kernel
theorem c_f3_72030_2 : ChunkP (F3zP 72030) 77 115 := by decide +kernel
theorem c_f3_72030_3 : ChunkP (F3zP 72030) 115 154 := by decide +kernel
theorem c_f3_72030_4 : ChunkP (F3zP 72030) 154 192 := by decide +kernel
theorem c_f3_72030_5 : ChunkP (F3zP 72030) 192 231 := by decide +kernel
theorem c_f3_72030_6 : ChunkP (F3zP 72030) 231 (Nat.sqrt 72030 + 1) := by decide +kernel

theorem cl8_72030 : S2ChkSq 72030 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_72030_0 c_s2_72030_1) c_s2_72030_2) c_s2_72030_3) c_s2_72030_4) c_s2_72030_5) c_s2_72030_6))
theorem cl9_72030 : S3ChkSq 72030 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_72030_0 c_s3_72030_1) c_s3_72030_2) c_s3_72030_3) c_s3_72030_4) c_s3_72030_5) c_s3_72030_6))
theorem cl11_72030 : (NoF2ChkSq 72030 ∧ NoF3zChkSq 72030 ∧ NoF4zChkSq 72030) :=
  ⟨f2Sq_of_P cf2z_72030 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_72030_0 c_f2_72030_1) c_f2_72030_2) c_f2_72030_3) c_f2_72030_4) c_f2_72030_5) c_f2_72030_6)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_72030_0 c_f3_72030_1) c_f3_72030_2) c_f3_72030_3) c_f3_72030_4) c_f3_72030_5) c_f3_72030_6)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_72030_0 c_f4_72030_1) c_f4_72030_2) c_f4_72030_3) c_f4_72030_4) c_f4_72030_5) c_f4_72030_6))⟩

theorem cnzETWD6_c72030 : CN'zETWD6 72030 :=
  ⟨cl1_72030, cl2_72030, cl3_72030, cl4_72030, cl5_72030, cl6_72030, cl7_72030, cl8_72030, cl9_72030, cl10_72030, cl11_72030, cl12_72030, cl13_72030, cl14_72030, cl15_72030⟩
theorem no_dissection_c72030 (D : CongruentDissection 72030) : False := not_tile_of_conditionsNSQzETWD6 72030 cnzETWD6_c72030 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c72030
