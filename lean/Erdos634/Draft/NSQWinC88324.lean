/-
Draft/NSQWinC88324.lean -- `no_dissection_c88324` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 8 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_88324 : NQChkW 88324 := by decide +kernel
theorem cl2w_88324 : EllOrAsqW 88324 := by decide +kernel
theorem cl2_88324 : (EllChk2 88324 ∨ AsqChk 88324) := ellAsq_of_W cl2w_88324
theorem cl3_88324 : NSqChkSq 88324 := by decide +kernel
theorem cl4_88324 : HArithChkSq 88324 := by decide +kernel
theorem cl5_88324 : (88324 % 2 = 1 ∨ (88324 % 2 = 0 ∧ NHSqChkSq 88324)) := by decide +kernel
theorem cl6_88324 : LeafEsqW 88324 := by decide +kernel
theorem cl7_88324 : (88324 % 4 = 2 ∨ F1ChkParW 88324) := by decide +kernel
theorem cl10_88324 : IsoH9bChkW 88324 := by decide +kernel
theorem cl12_88324 : GammaChkDW 88324 := by decide +kernel
theorem cl13_88324 : S1t2ChkW 88324 := by decide +kernel
theorem cl14_88324 : RWChkT2W 88324 := by decide +kernel
theorem cl15_88324 : S5wChkW 88324 := by decide +kernel
theorem cf2z_88324 : F2z 88324 := by decide +kernel
theorem c_s2_88324_0 : ChunkP (S2P 88324) 0 210 := by decide +kernel
theorem c_s2_88324_1 : ChunkP (S2P 88324) 210 298 := by decide +kernel
theorem c_s2_88324_2 : ChunkP (S2P 88324) 298 364 := by decide +kernel
theorem c_s2_88324_3 : ChunkP (S2P 88324) 364 421 := by decide +kernel
theorem c_s2_88324_4 : ChunkP (S2P 88324) 421 470 := by decide +kernel
theorem c_s2_88324_5 : ChunkP (S2P 88324) 470 515 := by decide +kernel
theorem c_s2_88324_6 : ChunkP (S2P 88324) 515 557 := by decide +kernel
theorem c_s2_88324_7 : ChunkP (S2P 88324) 557 (Nat.sqrt (4 * 88324) + 1) := by decide +kernel
theorem c_s3_88324_0 : ChunkP (S3P 88324) 0 37 := by decide +kernel
theorem c_s3_88324_1 : ChunkP (S3P 88324) 37 74 := by decide +kernel
theorem c_s3_88324_2 : ChunkP (S3P 88324) 74 112 := by decide +kernel
theorem c_s3_88324_3 : ChunkP (S3P 88324) 112 149 := by decide +kernel
theorem c_s3_88324_4 : ChunkP (S3P 88324) 149 186 := by decide +kernel
theorem c_s3_88324_5 : ChunkP (S3P 88324) 186 224 := by decide +kernel
theorem c_s3_88324_6 : ChunkP (S3P 88324) 224 261 := by decide +kernel
theorem c_s3_88324_7 : ChunkP (S3P 88324) 261 (Nat.sqrt 88324 + 1) := by decide +kernel
theorem c_f4_88324_0 : ChunkP (F4zP 88324) 0 37 := by decide +kernel
theorem c_f4_88324_1 : ChunkP (F4zP 88324) 37 74 := by decide +kernel
theorem c_f4_88324_2 : ChunkP (F4zP 88324) 74 112 := by decide +kernel
theorem c_f4_88324_3 : ChunkP (F4zP 88324) 112 149 := by decide +kernel
theorem c_f4_88324_4 : ChunkP (F4zP 88324) 149 186 := by decide +kernel
theorem c_f4_88324_5 : ChunkP (F4zP 88324) 186 224 := by decide +kernel
theorem c_f4_88324_6 : ChunkP (F4zP 88324) 224 261 := by decide +kernel
theorem c_f4_88324_7 : ChunkP (F4zP 88324) 261 (Nat.sqrt 88324 + 1) := by decide +kernel
theorem c_f2_88324_0 : ChunkP (F2P 88324) 0 37 := by decide +kernel
theorem c_f2_88324_1 : ChunkP (F2P 88324) 37 74 := by decide +kernel
theorem c_f2_88324_2 : ChunkP (F2P 88324) 74 112 := by decide +kernel
theorem c_f2_88324_3 : ChunkP (F2P 88324) 112 149 := by decide +kernel
theorem c_f2_88324_4 : ChunkP (F2P 88324) 149 186 := by decide +kernel
theorem c_f2_88324_5 : ChunkP (F2P 88324) 186 224 := by decide +kernel
theorem c_f2_88324_6 : ChunkP (F2P 88324) 224 261 := by decide +kernel
theorem c_f2_88324_7 : ChunkP (F2P 88324) 261 (Nat.sqrt 88324 + 1) := by decide +kernel
theorem c_f3_88324_0 : ChunkP (F3zP 88324) 0 37 := by decide +kernel
theorem c_f3_88324_1 : ChunkP (F3zP 88324) 37 74 := by decide +kernel
theorem c_f3_88324_2 : ChunkP (F3zP 88324) 74 112 := by decide +kernel
theorem c_f3_88324_3 : ChunkP (F3zP 88324) 112 149 := by decide +kernel
theorem c_f3_88324_4 : ChunkP (F3zP 88324) 149 186 := by decide +kernel
theorem c_f3_88324_5 : ChunkP (F3zP 88324) 186 224 := by decide +kernel
theorem c_f3_88324_6 : ChunkP (F3zP 88324) 224 261 := by decide +kernel
theorem c_f3_88324_7 : ChunkP (F3zP 88324) 261 (Nat.sqrt 88324 + 1) := by decide +kernel

theorem cl8_88324 : S2ChkSq 88324 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_88324_0 c_s2_88324_1) c_s2_88324_2) c_s2_88324_3) c_s2_88324_4) c_s2_88324_5) c_s2_88324_6) c_s2_88324_7))
theorem cl9_88324 : S3ChkSq 88324 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_88324_0 c_s3_88324_1) c_s3_88324_2) c_s3_88324_3) c_s3_88324_4) c_s3_88324_5) c_s3_88324_6) c_s3_88324_7))
theorem cl11_88324 : (NoF2ChkSq 88324 ∧ NoF3zChkSq 88324 ∧ NoF4zChkSq 88324) :=
  ⟨f2Sq_of_P cf2z_88324 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_88324_0 c_f2_88324_1) c_f2_88324_2) c_f2_88324_3) c_f2_88324_4) c_f2_88324_5) c_f2_88324_6) c_f2_88324_7)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_88324_0 c_f3_88324_1) c_f3_88324_2) c_f3_88324_3) c_f3_88324_4) c_f3_88324_5) c_f3_88324_6) c_f3_88324_7)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_88324_0 c_f4_88324_1) c_f4_88324_2) c_f4_88324_3) c_f4_88324_4) c_f4_88324_5) c_f4_88324_6) c_f4_88324_7))⟩

theorem cnzETWD6_c88324 : CN'zETWD6 88324 :=
  ⟨cl1_88324, cl2_88324, cl3_88324, cl4_88324, cl5_88324, cl6_88324, cl7_88324, cl8_88324, cl9_88324, cl10_88324, cl11_88324, cl12_88324, cl13_88324, cl14_88324, cl15_88324⟩
theorem no_dissection_c88324 (D : CongruentDissection 88324) : False := not_tile_of_conditionsNSQzETWD6 88324 cnzETWD6_c88324 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c88324
