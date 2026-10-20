/-
Draft/NSQWinC89406.lean -- `no_dissection_c89406` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 8 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_89406 : NQChkW 89406 := by decide +kernel
theorem cl2w_89406 : EllOrAsqW 89406 := by decide +kernel
theorem cl2_89406 : (EllChk2 89406 ∨ AsqChk 89406) := ellAsq_of_W cl2w_89406
theorem cl3_89406 : NSqChkSq 89406 := by decide +kernel
theorem cl4_89406 : HArithChkSq 89406 := by decide +kernel
theorem cl5_89406 : (89406 % 2 = 1 ∨ (89406 % 2 = 0 ∧ NHSqChkSq 89406)) := by decide +kernel
theorem cl6_89406 : LeafEsqW 89406 := by decide +kernel
theorem cl7_89406 : (89406 % 4 = 2 ∨ F1ChkParW 89406) := by decide +kernel
theorem cl10_89406 : IsoH9bChkW 89406 := by decide +kernel
theorem cl12_89406 : GammaChkDW 89406 := by decide +kernel
theorem cl13_89406 : S1t2ChkW 89406 := by decide +kernel
theorem cl14_89406 : RWChkT2W 89406 := by decide +kernel
theorem cl15_89406 : S5wChkW 89406 := by decide +kernel
theorem cf2z_89406 : F2z 89406 := by decide +kernel
theorem c_s2_89406_0 : ChunkP (S2P 89406) 0 212 := by decide +kernel
theorem c_s2_89406_1 : ChunkP (S2P 89406) 212 300 := by decide +kernel
theorem c_s2_89406_2 : ChunkP (S2P 89406) 300 367 := by decide +kernel
theorem c_s2_89406_3 : ChunkP (S2P 89406) 367 424 := by decide +kernel
theorem c_s2_89406_4 : ChunkP (S2P 89406) 424 474 := by decide +kernel
theorem c_s2_89406_5 : ChunkP (S2P 89406) 474 519 := by decide +kernel
theorem c_s2_89406_6 : ChunkP (S2P 89406) 519 560 := by decide +kernel
theorem c_s2_89406_7 : ChunkP (S2P 89406) 560 (Nat.sqrt (4 * 89406) + 1) := by decide +kernel
theorem c_s3_89406_0 : ChunkP (S3P 89406) 0 38 := by decide +kernel
theorem c_s3_89406_1 : ChunkP (S3P 89406) 38 75 := by decide +kernel
theorem c_s3_89406_2 : ChunkP (S3P 89406) 75 112 := by decide +kernel
theorem c_s3_89406_3 : ChunkP (S3P 89406) 112 150 := by decide +kernel
theorem c_s3_89406_4 : ChunkP (S3P 89406) 150 188 := by decide +kernel
theorem c_s3_89406_5 : ChunkP (S3P 89406) 188 225 := by decide +kernel
theorem c_s3_89406_6 : ChunkP (S3P 89406) 225 262 := by decide +kernel
theorem c_s3_89406_7 : ChunkP (S3P 89406) 262 (Nat.sqrt 89406 + 1) := by decide +kernel
theorem c_f4_89406_0 : ChunkP (F4zP 89406) 0 38 := by decide +kernel
theorem c_f4_89406_1 : ChunkP (F4zP 89406) 38 75 := by decide +kernel
theorem c_f4_89406_2 : ChunkP (F4zP 89406) 75 112 := by decide +kernel
theorem c_f4_89406_3 : ChunkP (F4zP 89406) 112 150 := by decide +kernel
theorem c_f4_89406_4 : ChunkP (F4zP 89406) 150 188 := by decide +kernel
theorem c_f4_89406_5 : ChunkP (F4zP 89406) 188 225 := by decide +kernel
theorem c_f4_89406_6 : ChunkP (F4zP 89406) 225 262 := by decide +kernel
theorem c_f4_89406_7 : ChunkP (F4zP 89406) 262 (Nat.sqrt 89406 + 1) := by decide +kernel
theorem c_f2_89406_0 : ChunkP (F2P 89406) 0 38 := by decide +kernel
theorem c_f2_89406_1 : ChunkP (F2P 89406) 38 75 := by decide +kernel
theorem c_f2_89406_2 : ChunkP (F2P 89406) 75 112 := by decide +kernel
theorem c_f2_89406_3 : ChunkP (F2P 89406) 112 150 := by decide +kernel
theorem c_f2_89406_4 : ChunkP (F2P 89406) 150 188 := by decide +kernel
theorem c_f2_89406_5 : ChunkP (F2P 89406) 188 225 := by decide +kernel
theorem c_f2_89406_6 : ChunkP (F2P 89406) 225 262 := by decide +kernel
theorem c_f2_89406_7 : ChunkP (F2P 89406) 262 (Nat.sqrt 89406 + 1) := by decide +kernel
theorem c_f3_89406_0 : ChunkP (F3zP 89406) 0 38 := by decide +kernel
theorem c_f3_89406_1 : ChunkP (F3zP 89406) 38 75 := by decide +kernel
theorem c_f3_89406_2 : ChunkP (F3zP 89406) 75 112 := by decide +kernel
theorem c_f3_89406_3 : ChunkP (F3zP 89406) 112 150 := by decide +kernel
theorem c_f3_89406_4 : ChunkP (F3zP 89406) 150 188 := by decide +kernel
theorem c_f3_89406_5 : ChunkP (F3zP 89406) 188 225 := by decide +kernel
theorem c_f3_89406_6 : ChunkP (F3zP 89406) 225 262 := by decide +kernel
theorem c_f3_89406_7 : ChunkP (F3zP 89406) 262 (Nat.sqrt 89406 + 1) := by decide +kernel

theorem cl8_89406 : S2ChkSq 89406 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_89406_0 c_s2_89406_1) c_s2_89406_2) c_s2_89406_3) c_s2_89406_4) c_s2_89406_5) c_s2_89406_6) c_s2_89406_7))
theorem cl9_89406 : S3ChkSq 89406 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_89406_0 c_s3_89406_1) c_s3_89406_2) c_s3_89406_3) c_s3_89406_4) c_s3_89406_5) c_s3_89406_6) c_s3_89406_7))
theorem cl11_89406 : (NoF2ChkSq 89406 ∧ NoF3zChkSq 89406 ∧ NoF4zChkSq 89406) :=
  ⟨f2Sq_of_P cf2z_89406 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_89406_0 c_f2_89406_1) c_f2_89406_2) c_f2_89406_3) c_f2_89406_4) c_f2_89406_5) c_f2_89406_6) c_f2_89406_7)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_89406_0 c_f3_89406_1) c_f3_89406_2) c_f3_89406_3) c_f3_89406_4) c_f3_89406_5) c_f3_89406_6) c_f3_89406_7)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_89406_0 c_f4_89406_1) c_f4_89406_2) c_f4_89406_3) c_f4_89406_4) c_f4_89406_5) c_f4_89406_6) c_f4_89406_7))⟩

theorem cnzETWD6_c89406 : CN'zETWD6 89406 :=
  ⟨cl1_89406, cl2_89406, cl3_89406, cl4_89406, cl5_89406, cl6_89406, cl7_89406, cl8_89406, cl9_89406, cl10_89406, cl11_89406, cl12_89406, cl13_89406, cl14_89406, cl15_89406⟩
theorem no_dissection_c89406 (D : CongruentDissection 89406) : False := not_tile_of_conditionsNSQzETWD6 89406 cnzETWD6_c89406 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c89406
