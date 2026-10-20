/-
Draft/NSQWinC55470.lean -- `no_dissection_c55470` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 5 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_55470 : NQChkW 55470 := by decide +kernel
theorem cl2w_55470 : EllOrAsqW 55470 := by decide +kernel
theorem cl2_55470 : (EllChk2 55470 ∨ AsqChk 55470) := ellAsq_of_W cl2w_55470
theorem cl3_55470 : NSqChkSq 55470 := by decide +kernel
theorem cl4_55470 : HArithChkSq 55470 := by decide +kernel
theorem cl5_55470 : (55470 % 2 = 1 ∨ (55470 % 2 = 0 ∧ NHSqChkSq 55470)) := by decide +kernel
theorem cl6_55470 : LeafEsqW 55470 := by decide +kernel
theorem cl7_55470 : (55470 % 4 = 2 ∨ F1ChkParW 55470) := by decide +kernel
theorem cl10_55470 : IsoH9bChkW 55470 := by decide +kernel
theorem cl12_55470 : GammaChkDW 55470 := by decide +kernel
theorem cl13_55470 : S1t2ChkW 55470 := by decide +kernel
theorem cl14_55470 : RWChkT2W 55470 := by decide +kernel
theorem cl15_55470 : S5wChkW 55470 := by decide +kernel
theorem cf2z_55470 : F2z 55470 := by decide +kernel
theorem c_s2_55470_0 : ChunkP (S2P 55470) 0 211 := by decide +kernel
theorem c_s2_55470_1 : ChunkP (S2P 55470) 211 299 := by decide +kernel
theorem c_s2_55470_2 : ChunkP (S2P 55470) 299 366 := by decide +kernel
theorem c_s2_55470_3 : ChunkP (S2P 55470) 366 422 := by decide +kernel
theorem c_s2_55470_4 : ChunkP (S2P 55470) 422 (Nat.sqrt (4 * 55470) + 1) := by decide +kernel
theorem c_s3_55470_0 : ChunkP (S3P 55470) 0 47 := by decide +kernel
theorem c_s3_55470_1 : ChunkP (S3P 55470) 47 94 := by decide +kernel
theorem c_s3_55470_2 : ChunkP (S3P 55470) 94 142 := by decide +kernel
theorem c_s3_55470_3 : ChunkP (S3P 55470) 142 189 := by decide +kernel
theorem c_s3_55470_4 : ChunkP (S3P 55470) 189 (Nat.sqrt 55470 + 1) := by decide +kernel
theorem c_f4_55470_0 : ChunkP (F4zP 55470) 0 47 := by decide +kernel
theorem c_f4_55470_1 : ChunkP (F4zP 55470) 47 94 := by decide +kernel
theorem c_f4_55470_2 : ChunkP (F4zP 55470) 94 142 := by decide +kernel
theorem c_f4_55470_3 : ChunkP (F4zP 55470) 142 189 := by decide +kernel
theorem c_f4_55470_4 : ChunkP (F4zP 55470) 189 (Nat.sqrt 55470 + 1) := by decide +kernel
theorem c_f2_55470_0 : ChunkP (F2P 55470) 0 47 := by decide +kernel
theorem c_f2_55470_1 : ChunkP (F2P 55470) 47 94 := by decide +kernel
theorem c_f2_55470_2 : ChunkP (F2P 55470) 94 142 := by decide +kernel
theorem c_f2_55470_3 : ChunkP (F2P 55470) 142 189 := by decide +kernel
theorem c_f2_55470_4 : ChunkP (F2P 55470) 189 (Nat.sqrt 55470 + 1) := by decide +kernel
theorem c_f3_55470_0 : ChunkP (F3zP 55470) 0 47 := by decide +kernel
theorem c_f3_55470_1 : ChunkP (F3zP 55470) 47 94 := by decide +kernel
theorem c_f3_55470_2 : ChunkP (F3zP 55470) 94 142 := by decide +kernel
theorem c_f3_55470_3 : ChunkP (F3zP 55470) 142 189 := by decide +kernel
theorem c_f3_55470_4 : ChunkP (F3zP 55470) 189 (Nat.sqrt 55470 + 1) := by decide +kernel

theorem cl8_55470 : S2ChkSq 55470 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s2_55470_0 c_s2_55470_1) c_s2_55470_2) c_s2_55470_3) c_s2_55470_4))
theorem cl9_55470 : S3ChkSq 55470 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s3_55470_0 c_s3_55470_1) c_s3_55470_2) c_s3_55470_3) c_s3_55470_4))
theorem cl11_55470 : (NoF2ChkSq 55470 ∧ NoF3zChkSq 55470 ∧ NoF4zChkSq 55470) :=
  ⟨f2Sq_of_P cf2z_55470 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f2_55470_0 c_f2_55470_1) c_f2_55470_2) c_f2_55470_3) c_f2_55470_4)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f3_55470_0 c_f3_55470_1) c_f3_55470_2) c_f3_55470_3) c_f3_55470_4)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f4_55470_0 c_f4_55470_1) c_f4_55470_2) c_f4_55470_3) c_f4_55470_4))⟩

theorem cnzETWD6_c55470 : CN'zETWD6 55470 :=
  ⟨cl1_55470, cl2_55470, cl3_55470, cl4_55470, cl5_55470, cl6_55470, cl7_55470, cl8_55470, cl9_55470, cl10_55470, cl11_55470, cl12_55470, cl13_55470, cl14_55470, cl15_55470⟩
theorem no_dissection_c55470 (D : CongruentDissection 55470) : False := not_tile_of_conditionsNSQzETWD6 55470 cnzETWD6_c55470 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c55470
