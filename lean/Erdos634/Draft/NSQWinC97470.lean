/-
Draft/NSQWinC97470.lean -- `no_dissection_c97470` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 9 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_97470 : NQChkW 97470 := by decide +kernel
theorem cl2w_97470 : EllOrAsqW 97470 := by decide +kernel
theorem cl2_97470 : (EllChk2 97470 ∨ AsqChk 97470) := ellAsq_of_W cl2w_97470
theorem cl3_97470 : NSqChkSq 97470 := by decide +kernel
theorem cl4_97470 : HArithChkSq 97470 := by decide +kernel
theorem cl5_97470 : (97470 % 2 = 1 ∨ (97470 % 2 = 0 ∧ NHSqChkSq 97470)) := by decide +kernel
theorem cl6_97470 : LeafEsqW 97470 := by decide +kernel
theorem cl7_97470 : (97470 % 4 = 2 ∨ F1ChkParW 97470) := by decide +kernel
theorem cl10_97470 : IsoH9bChkW 97470 := by decide +kernel
theorem cl12_97470 : GammaChkDW 97470 := by decide +kernel
theorem cl13_97470 : S1t2ChkW 97470 := by decide +kernel
theorem cl14_97470 : RWChkT2W 97470 := by decide +kernel
theorem cl15_97470 : S5wChkW 97470 := by decide +kernel
theorem cf2z_97470 : F2z 97470 := by decide +kernel
theorem c_s2_97470_0 : ChunkP (S2P 97470) 0 208 := by decide +kernel
theorem c_s2_97470_1 : ChunkP (S2P 97470) 208 295 := by decide +kernel
theorem c_s2_97470_2 : ChunkP (S2P 97470) 295 361 := by decide +kernel
theorem c_s2_97470_3 : ChunkP (S2P 97470) 361 417 := by decide +kernel
theorem c_s2_97470_4 : ChunkP (S2P 97470) 417 466 := by decide +kernel
theorem c_s2_97470_5 : ChunkP (S2P 97470) 466 510 := by decide +kernel
theorem c_s2_97470_6 : ChunkP (S2P 97470) 510 551 := by decide +kernel
theorem c_s2_97470_7 : ChunkP (S2P 97470) 551 589 := by decide +kernel
theorem c_s2_97470_8 : ChunkP (S2P 97470) 589 (Nat.sqrt (4 * 97470) + 1) := by decide +kernel
theorem c_s3_97470_0 : ChunkP (S3P 97470) 0 35 := by decide +kernel
theorem c_s3_97470_1 : ChunkP (S3P 97470) 35 70 := by decide +kernel
theorem c_s3_97470_2 : ChunkP (S3P 97470) 70 104 := by decide +kernel
theorem c_s3_97470_3 : ChunkP (S3P 97470) 104 139 := by decide +kernel
theorem c_s3_97470_4 : ChunkP (S3P 97470) 139 174 := by decide +kernel
theorem c_s3_97470_5 : ChunkP (S3P 97470) 174 209 := by decide +kernel
theorem c_s3_97470_6 : ChunkP (S3P 97470) 209 243 := by decide +kernel
theorem c_s3_97470_7 : ChunkP (S3P 97470) 243 278 := by decide +kernel
theorem c_s3_97470_8 : ChunkP (S3P 97470) 278 (Nat.sqrt 97470 + 1) := by decide +kernel
theorem c_f4_97470_0 : ChunkP (F4zP 97470) 0 35 := by decide +kernel
theorem c_f4_97470_1 : ChunkP (F4zP 97470) 35 70 := by decide +kernel
theorem c_f4_97470_2 : ChunkP (F4zP 97470) 70 104 := by decide +kernel
theorem c_f4_97470_3 : ChunkP (F4zP 97470) 104 139 := by decide +kernel
theorem c_f4_97470_4 : ChunkP (F4zP 97470) 139 174 := by decide +kernel
theorem c_f4_97470_5 : ChunkP (F4zP 97470) 174 209 := by decide +kernel
theorem c_f4_97470_6 : ChunkP (F4zP 97470) 209 243 := by decide +kernel
theorem c_f4_97470_7 : ChunkP (F4zP 97470) 243 278 := by decide +kernel
theorem c_f4_97470_8 : ChunkP (F4zP 97470) 278 (Nat.sqrt 97470 + 1) := by decide +kernel
theorem c_f2_97470_0 : ChunkP (F2P 97470) 0 35 := by decide +kernel
theorem c_f2_97470_1 : ChunkP (F2P 97470) 35 70 := by decide +kernel
theorem c_f2_97470_2 : ChunkP (F2P 97470) 70 104 := by decide +kernel
theorem c_f2_97470_3 : ChunkP (F2P 97470) 104 139 := by decide +kernel
theorem c_f2_97470_4 : ChunkP (F2P 97470) 139 174 := by decide +kernel
theorem c_f2_97470_5 : ChunkP (F2P 97470) 174 209 := by decide +kernel
theorem c_f2_97470_6 : ChunkP (F2P 97470) 209 243 := by decide +kernel
theorem c_f2_97470_7 : ChunkP (F2P 97470) 243 278 := by decide +kernel
theorem c_f2_97470_8 : ChunkP (F2P 97470) 278 (Nat.sqrt 97470 + 1) := by decide +kernel
theorem c_f3_97470_0 : ChunkP (F3zP 97470) 0 35 := by decide +kernel
theorem c_f3_97470_1 : ChunkP (F3zP 97470) 35 70 := by decide +kernel
theorem c_f3_97470_2 : ChunkP (F3zP 97470) 70 104 := by decide +kernel
theorem c_f3_97470_3 : ChunkP (F3zP 97470) 104 139 := by decide +kernel
theorem c_f3_97470_4 : ChunkP (F3zP 97470) 139 174 := by decide +kernel
theorem c_f3_97470_5 : ChunkP (F3zP 97470) 174 209 := by decide +kernel
theorem c_f3_97470_6 : ChunkP (F3zP 97470) 209 243 := by decide +kernel
theorem c_f3_97470_7 : ChunkP (F3zP 97470) 243 278 := by decide +kernel
theorem c_f3_97470_8 : ChunkP (F3zP 97470) 278 (Nat.sqrt 97470 + 1) := by decide +kernel

theorem cl8_97470 : S2ChkSq 97470 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_97470_0 c_s2_97470_1) c_s2_97470_2) c_s2_97470_3) c_s2_97470_4) c_s2_97470_5) c_s2_97470_6) c_s2_97470_7) c_s2_97470_8))
theorem cl9_97470 : S3ChkSq 97470 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_97470_0 c_s3_97470_1) c_s3_97470_2) c_s3_97470_3) c_s3_97470_4) c_s3_97470_5) c_s3_97470_6) c_s3_97470_7) c_s3_97470_8))
theorem cl11_97470 : (NoF2ChkSq 97470 ∧ NoF3zChkSq 97470 ∧ NoF4zChkSq 97470) :=
  ⟨f2Sq_of_P cf2z_97470 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_97470_0 c_f2_97470_1) c_f2_97470_2) c_f2_97470_3) c_f2_97470_4) c_f2_97470_5) c_f2_97470_6) c_f2_97470_7) c_f2_97470_8)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_97470_0 c_f3_97470_1) c_f3_97470_2) c_f3_97470_3) c_f3_97470_4) c_f3_97470_5) c_f3_97470_6) c_f3_97470_7) c_f3_97470_8)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_97470_0 c_f4_97470_1) c_f4_97470_2) c_f4_97470_3) c_f4_97470_4) c_f4_97470_5) c_f4_97470_6) c_f4_97470_7) c_f4_97470_8))⟩

theorem cnzETWD6_c97470 : CN'zETWD6 97470 :=
  ⟨cl1_97470, cl2_97470, cl3_97470, cl4_97470, cl5_97470, cl6_97470, cl7_97470, cl8_97470, cl9_97470, cl10_97470, cl11_97470, cl12_97470, cl13_97470, cl14_97470, cl15_97470⟩
theorem no_dissection_c97470 (D : CongruentDissection 97470) : False := not_tile_of_conditionsNSQzETWD6 97470 cnzETWD6_c97470 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c97470
