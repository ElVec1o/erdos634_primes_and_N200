/-
Draft/NSQWinC81486.lean -- `no_dissection_c81486` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 7 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_81486 : NQChkW 81486 := by decide +kernel
theorem cl2w_81486 : EllOrAsqW 81486 := by decide +kernel
theorem cl2_81486 : (EllChk2 81486 ∨ AsqChk 81486) := ellAsq_of_W cl2w_81486
theorem cl3_81486 : NSqChkSq 81486 := by decide +kernel
theorem cl4_81486 : HArithChkSq 81486 := by decide +kernel
theorem cl5_81486 : (81486 % 2 = 1 ∨ (81486 % 2 = 0 ∧ NHSqChkSq 81486)) := by decide +kernel
theorem cl6_81486 : LeafEsqW 81486 := by decide +kernel
theorem cl7_81486 : (81486 % 4 = 2 ∨ F1ChkParW 81486) := by decide +kernel
theorem cl10_81486 : IsoH9bChkW 81486 := by decide +kernel
theorem cl12_81486 : GammaChkDW 81486 := by decide +kernel
theorem cl13_81486 : S1t2ChkW 81486 := by decide +kernel
theorem cl14_81486 : RWChkT2W 81486 := by decide +kernel
theorem cl15_81486 : S5wChkW 81486 := by decide +kernel
theorem cf2z_81486 : F2z 81486 := by decide +kernel
theorem c_s2_81486_0 : ChunkP (S2P 81486) 0 216 := by decide +kernel
theorem c_s2_81486_1 : ChunkP (S2P 81486) 216 305 := by decide +kernel
theorem c_s2_81486_2 : ChunkP (S2P 81486) 305 374 := by decide +kernel
theorem c_s2_81486_3 : ChunkP (S2P 81486) 374 432 := by decide +kernel
theorem c_s2_81486_4 : ChunkP (S2P 81486) 432 483 := by decide +kernel
theorem c_s2_81486_5 : ChunkP (S2P 81486) 483 529 := by decide +kernel
theorem c_s2_81486_6 : ChunkP (S2P 81486) 529 (Nat.sqrt (4 * 81486) + 1) := by decide +kernel
theorem c_s3_81486_0 : ChunkP (S3P 81486) 0 41 := by decide +kernel
theorem c_s3_81486_1 : ChunkP (S3P 81486) 41 82 := by decide +kernel
theorem c_s3_81486_2 : ChunkP (S3P 81486) 82 123 := by decide +kernel
theorem c_s3_81486_3 : ChunkP (S3P 81486) 123 163 := by decide +kernel
theorem c_s3_81486_4 : ChunkP (S3P 81486) 163 204 := by decide +kernel
theorem c_s3_81486_5 : ChunkP (S3P 81486) 204 245 := by decide +kernel
theorem c_s3_81486_6 : ChunkP (S3P 81486) 245 (Nat.sqrt 81486 + 1) := by decide +kernel
theorem c_f4_81486_0 : ChunkP (F4zP 81486) 0 41 := by decide +kernel
theorem c_f4_81486_1 : ChunkP (F4zP 81486) 41 82 := by decide +kernel
theorem c_f4_81486_2 : ChunkP (F4zP 81486) 82 123 := by decide +kernel
theorem c_f4_81486_3 : ChunkP (F4zP 81486) 123 163 := by decide +kernel
theorem c_f4_81486_4 : ChunkP (F4zP 81486) 163 204 := by decide +kernel
theorem c_f4_81486_5 : ChunkP (F4zP 81486) 204 245 := by decide +kernel
theorem c_f4_81486_6 : ChunkP (F4zP 81486) 245 (Nat.sqrt 81486 + 1) := by decide +kernel
theorem c_f2_81486_0 : ChunkP (F2P 81486) 0 41 := by decide +kernel
theorem c_f2_81486_1 : ChunkP (F2P 81486) 41 82 := by decide +kernel
theorem c_f2_81486_2 : ChunkP (F2P 81486) 82 123 := by decide +kernel
theorem c_f2_81486_3 : ChunkP (F2P 81486) 123 163 := by decide +kernel
theorem c_f2_81486_4 : ChunkP (F2P 81486) 163 204 := by decide +kernel
theorem c_f2_81486_5 : ChunkP (F2P 81486) 204 245 := by decide +kernel
theorem c_f2_81486_6 : ChunkP (F2P 81486) 245 (Nat.sqrt 81486 + 1) := by decide +kernel
theorem c_f3_81486_0 : ChunkP (F3zP 81486) 0 41 := by decide +kernel
theorem c_f3_81486_1 : ChunkP (F3zP 81486) 41 82 := by decide +kernel
theorem c_f3_81486_2 : ChunkP (F3zP 81486) 82 123 := by decide +kernel
theorem c_f3_81486_3 : ChunkP (F3zP 81486) 123 163 := by decide +kernel
theorem c_f3_81486_4 : ChunkP (F3zP 81486) 163 204 := by decide +kernel
theorem c_f3_81486_5 : ChunkP (F3zP 81486) 204 245 := by decide +kernel
theorem c_f3_81486_6 : ChunkP (F3zP 81486) 245 (Nat.sqrt 81486 + 1) := by decide +kernel

theorem cl8_81486 : S2ChkSq 81486 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_81486_0 c_s2_81486_1) c_s2_81486_2) c_s2_81486_3) c_s2_81486_4) c_s2_81486_5) c_s2_81486_6))
theorem cl9_81486 : S3ChkSq 81486 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_81486_0 c_s3_81486_1) c_s3_81486_2) c_s3_81486_3) c_s3_81486_4) c_s3_81486_5) c_s3_81486_6))
theorem cl11_81486 : (NoF2ChkSq 81486 ∧ NoF3zChkSq 81486 ∧ NoF4zChkSq 81486) :=
  ⟨f2Sq_of_P cf2z_81486 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_81486_0 c_f2_81486_1) c_f2_81486_2) c_f2_81486_3) c_f2_81486_4) c_f2_81486_5) c_f2_81486_6)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_81486_0 c_f3_81486_1) c_f3_81486_2) c_f3_81486_3) c_f3_81486_4) c_f3_81486_5) c_f3_81486_6)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_81486_0 c_f4_81486_1) c_f4_81486_2) c_f4_81486_3) c_f4_81486_4) c_f4_81486_5) c_f4_81486_6))⟩

theorem cnzETWD6_c81486 : CN'zETWD6 81486 :=
  ⟨cl1_81486, cl2_81486, cl3_81486, cl4_81486, cl5_81486, cl6_81486, cl7_81486, cl8_81486, cl9_81486, cl10_81486, cl11_81486, cl12_81486, cl13_81486, cl14_81486, cl15_81486⟩
theorem no_dissection_c81486 (D : CongruentDissection 81486) : False := not_tile_of_conditionsNSQzETWD6 81486 cnzETWD6_c81486 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c81486
