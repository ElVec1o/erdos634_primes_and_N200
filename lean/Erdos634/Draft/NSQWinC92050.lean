/-
Draft/NSQWinC92050.lean -- `no_dissection_c92050` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 8 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_92050 : NQChkW 92050 := by decide +kernel
theorem cl2w_92050 : EllOrAsqW 92050 := by decide +kernel
theorem cl2_92050 : (EllChk2 92050 ∨ AsqChk 92050) := ellAsq_of_W cl2w_92050
theorem cl3_92050 : NSqChkSq 92050 := by decide +kernel
theorem cl4_92050 : HArithChkSq 92050 := by decide +kernel
theorem cl5_92050 : (92050 % 2 = 1 ∨ (92050 % 2 = 0 ∧ NHSqChkSq 92050)) := by decide +kernel
theorem cl6_92050 : LeafEsqW 92050 := by decide +kernel
theorem cl7_92050 : (92050 % 4 = 2 ∨ F1ChkParW 92050) := by decide +kernel
theorem cl10_92050 : IsoH9bChkW 92050 := by decide +kernel
theorem cl12_92050 : GammaChkDW 92050 := by decide +kernel
theorem cl13_92050 : S1t2ChkW 92050 := by decide +kernel
theorem cl14_92050 : RWChkT2W 92050 := by decide +kernel
theorem cl15_92050 : S5wChkW 92050 := by decide +kernel
theorem cf2z_92050 : F2z 92050 := by decide +kernel
theorem c_s2_92050_0 : ChunkP (S2P 92050) 0 215 := by decide +kernel
theorem c_s2_92050_1 : ChunkP (S2P 92050) 215 304 := by decide +kernel
theorem c_s2_92050_2 : ChunkP (S2P 92050) 304 372 := by decide +kernel
theorem c_s2_92050_3 : ChunkP (S2P 92050) 372 429 := by decide +kernel
theorem c_s2_92050_4 : ChunkP (S2P 92050) 429 480 := by decide +kernel
theorem c_s2_92050_5 : ChunkP (S2P 92050) 480 526 := by decide +kernel
theorem c_s2_92050_6 : ChunkP (S2P 92050) 526 568 := by decide +kernel
theorem c_s2_92050_7 : ChunkP (S2P 92050) 568 (Nat.sqrt (4 * 92050) + 1) := by decide +kernel
theorem c_s3_92050_0 : ChunkP (S3P 92050) 0 38 := by decide +kernel
theorem c_s3_92050_1 : ChunkP (S3P 92050) 38 76 := by decide +kernel
theorem c_s3_92050_2 : ChunkP (S3P 92050) 76 114 := by decide +kernel
theorem c_s3_92050_3 : ChunkP (S3P 92050) 114 152 := by decide +kernel
theorem c_s3_92050_4 : ChunkP (S3P 92050) 152 190 := by decide +kernel
theorem c_s3_92050_5 : ChunkP (S3P 92050) 190 228 := by decide +kernel
theorem c_s3_92050_6 : ChunkP (S3P 92050) 228 266 := by decide +kernel
theorem c_s3_92050_7 : ChunkP (S3P 92050) 266 (Nat.sqrt 92050 + 1) := by decide +kernel
theorem c_f4_92050_0 : ChunkP (F4zP 92050) 0 38 := by decide +kernel
theorem c_f4_92050_1 : ChunkP (F4zP 92050) 38 76 := by decide +kernel
theorem c_f4_92050_2 : ChunkP (F4zP 92050) 76 114 := by decide +kernel
theorem c_f4_92050_3 : ChunkP (F4zP 92050) 114 152 := by decide +kernel
theorem c_f4_92050_4 : ChunkP (F4zP 92050) 152 190 := by decide +kernel
theorem c_f4_92050_5 : ChunkP (F4zP 92050) 190 228 := by decide +kernel
theorem c_f4_92050_6 : ChunkP (F4zP 92050) 228 266 := by decide +kernel
theorem c_f4_92050_7 : ChunkP (F4zP 92050) 266 (Nat.sqrt 92050 + 1) := by decide +kernel
theorem c_f2_92050_0 : ChunkP (F2P 92050) 0 38 := by decide +kernel
theorem c_f2_92050_1 : ChunkP (F2P 92050) 38 76 := by decide +kernel
theorem c_f2_92050_2 : ChunkP (F2P 92050) 76 114 := by decide +kernel
theorem c_f2_92050_3 : ChunkP (F2P 92050) 114 152 := by decide +kernel
theorem c_f2_92050_4 : ChunkP (F2P 92050) 152 190 := by decide +kernel
theorem c_f2_92050_5 : ChunkP (F2P 92050) 190 228 := by decide +kernel
theorem c_f2_92050_6 : ChunkP (F2P 92050) 228 266 := by decide +kernel
theorem c_f2_92050_7 : ChunkP (F2P 92050) 266 (Nat.sqrt 92050 + 1) := by decide +kernel
theorem c_f3_92050_0 : ChunkP (F3zP 92050) 0 38 := by decide +kernel
theorem c_f3_92050_1 : ChunkP (F3zP 92050) 38 76 := by decide +kernel
theorem c_f3_92050_2 : ChunkP (F3zP 92050) 76 114 := by decide +kernel
theorem c_f3_92050_3 : ChunkP (F3zP 92050) 114 152 := by decide +kernel
theorem c_f3_92050_4 : ChunkP (F3zP 92050) 152 190 := by decide +kernel
theorem c_f3_92050_5 : ChunkP (F3zP 92050) 190 228 := by decide +kernel
theorem c_f3_92050_6 : ChunkP (F3zP 92050) 228 266 := by decide +kernel
theorem c_f3_92050_7 : ChunkP (F3zP 92050) 266 (Nat.sqrt 92050 + 1) := by decide +kernel

theorem cl8_92050 : S2ChkSq 92050 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_92050_0 c_s2_92050_1) c_s2_92050_2) c_s2_92050_3) c_s2_92050_4) c_s2_92050_5) c_s2_92050_6) c_s2_92050_7))
theorem cl9_92050 : S3ChkSq 92050 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_92050_0 c_s3_92050_1) c_s3_92050_2) c_s3_92050_3) c_s3_92050_4) c_s3_92050_5) c_s3_92050_6) c_s3_92050_7))
theorem cl11_92050 : (NoF2ChkSq 92050 ∧ NoF3zChkSq 92050 ∧ NoF4zChkSq 92050) :=
  ⟨f2Sq_of_P cf2z_92050 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_92050_0 c_f2_92050_1) c_f2_92050_2) c_f2_92050_3) c_f2_92050_4) c_f2_92050_5) c_f2_92050_6) c_f2_92050_7)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_92050_0 c_f3_92050_1) c_f3_92050_2) c_f3_92050_3) c_f3_92050_4) c_f3_92050_5) c_f3_92050_6) c_f3_92050_7)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_92050_0 c_f4_92050_1) c_f4_92050_2) c_f4_92050_3) c_f4_92050_4) c_f4_92050_5) c_f4_92050_6) c_f4_92050_7))⟩

theorem cnzETWD6_c92050 : CN'zETWD6 92050 :=
  ⟨cl1_92050, cl2_92050, cl3_92050, cl4_92050, cl5_92050, cl6_92050, cl7_92050, cl8_92050, cl9_92050, cl10_92050, cl11_92050, cl12_92050, cl13_92050, cl14_92050, cl15_92050⟩
theorem no_dissection_c92050 (D : CongruentDissection 92050) : False := not_tile_of_conditionsNSQzETWD6 92050 cnzETWD6_c92050 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c92050
