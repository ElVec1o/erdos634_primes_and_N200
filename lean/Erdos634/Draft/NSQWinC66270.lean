/-
Draft/NSQWinC66270.lean -- `no_dissection_c66270` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 6 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_66270 : NQChkW 66270 := by decide +kernel
theorem cl2w_66270 : EllOrAsqW 66270 := by decide +kernel
theorem cl2_66270 : (EllChk2 66270 ∨ AsqChk 66270) := ellAsq_of_W cl2w_66270
theorem cl3_66270 : NSqChkSq 66270 := by decide +kernel
theorem cl4_66270 : HArithChkSq 66270 := by decide +kernel
theorem cl5_66270 : (66270 % 2 = 1 ∨ (66270 % 2 = 0 ∧ NHSqChkSq 66270)) := by decide +kernel
theorem cl6_66270 : LeafEsqW 66270 := by decide +kernel
theorem cl7_66270 : (66270 % 4 = 2 ∨ F1ChkParW 66270) := by decide +kernel
theorem cl10_66270 : IsoH9bChkW 66270 := by decide +kernel
theorem cl12_66270 : GammaChkDW 66270 := by decide +kernel
theorem cl13_66270 : S1t2ChkW 66270 := by decide +kernel
theorem cl14_66270 : RWChkT2W 66270 := by decide +kernel
theorem cl15_66270 : S5wChkW 66270 := by decide +kernel
theorem cf2z_66270 : F2z 66270 := by decide +kernel
theorem c_s2_66270_0 : ChunkP (S2P 66270) 0 210 := by decide +kernel
theorem c_s2_66270_1 : ChunkP (S2P 66270) 210 297 := by decide +kernel
theorem c_s2_66270_2 : ChunkP (S2P 66270) 297 364 := by decide +kernel
theorem c_s2_66270_3 : ChunkP (S2P 66270) 364 420 := by decide +kernel
theorem c_s2_66270_4 : ChunkP (S2P 66270) 420 470 := by decide +kernel
theorem c_s2_66270_5 : ChunkP (S2P 66270) 470 (Nat.sqrt (4 * 66270) + 1) := by decide +kernel
theorem c_s3_66270_0 : ChunkP (S3P 66270) 0 43 := by decide +kernel
theorem c_s3_66270_1 : ChunkP (S3P 66270) 43 86 := by decide +kernel
theorem c_s3_66270_2 : ChunkP (S3P 66270) 86 129 := by decide +kernel
theorem c_s3_66270_3 : ChunkP (S3P 66270) 129 172 := by decide +kernel
theorem c_s3_66270_4 : ChunkP (S3P 66270) 172 215 := by decide +kernel
theorem c_s3_66270_5 : ChunkP (S3P 66270) 215 (Nat.sqrt 66270 + 1) := by decide +kernel
theorem c_f4_66270_0 : ChunkP (F4zP 66270) 0 43 := by decide +kernel
theorem c_f4_66270_1 : ChunkP (F4zP 66270) 43 86 := by decide +kernel
theorem c_f4_66270_2 : ChunkP (F4zP 66270) 86 129 := by decide +kernel
theorem c_f4_66270_3 : ChunkP (F4zP 66270) 129 172 := by decide +kernel
theorem c_f4_66270_4 : ChunkP (F4zP 66270) 172 215 := by decide +kernel
theorem c_f4_66270_5 : ChunkP (F4zP 66270) 215 (Nat.sqrt 66270 + 1) := by decide +kernel
theorem c_f2_66270_0 : ChunkP (F2P 66270) 0 43 := by decide +kernel
theorem c_f2_66270_1 : ChunkP (F2P 66270) 43 86 := by decide +kernel
theorem c_f2_66270_2 : ChunkP (F2P 66270) 86 129 := by decide +kernel
theorem c_f2_66270_3 : ChunkP (F2P 66270) 129 172 := by decide +kernel
theorem c_f2_66270_4 : ChunkP (F2P 66270) 172 215 := by decide +kernel
theorem c_f2_66270_5 : ChunkP (F2P 66270) 215 (Nat.sqrt 66270 + 1) := by decide +kernel
theorem c_f3_66270_0 : ChunkP (F3zP 66270) 0 43 := by decide +kernel
theorem c_f3_66270_1 : ChunkP (F3zP 66270) 43 86 := by decide +kernel
theorem c_f3_66270_2 : ChunkP (F3zP 66270) 86 129 := by decide +kernel
theorem c_f3_66270_3 : ChunkP (F3zP 66270) 129 172 := by decide +kernel
theorem c_f3_66270_4 : ChunkP (F3zP 66270) 172 215 := by decide +kernel
theorem c_f3_66270_5 : ChunkP (F3zP 66270) 215 (Nat.sqrt 66270 + 1) := by decide +kernel

theorem cl8_66270 : S2ChkSq 66270 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_66270_0 c_s2_66270_1) c_s2_66270_2) c_s2_66270_3) c_s2_66270_4) c_s2_66270_5))
theorem cl9_66270 : S3ChkSq 66270 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_66270_0 c_s3_66270_1) c_s3_66270_2) c_s3_66270_3) c_s3_66270_4) c_s3_66270_5))
theorem cl11_66270 : (NoF2ChkSq 66270 ∧ NoF3zChkSq 66270 ∧ NoF4zChkSq 66270) :=
  ⟨f2Sq_of_P cf2z_66270 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_66270_0 c_f2_66270_1) c_f2_66270_2) c_f2_66270_3) c_f2_66270_4) c_f2_66270_5)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_66270_0 c_f3_66270_1) c_f3_66270_2) c_f3_66270_3) c_f3_66270_4) c_f3_66270_5)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_66270_0 c_f4_66270_1) c_f4_66270_2) c_f4_66270_3) c_f4_66270_4) c_f4_66270_5))⟩

theorem cnzETWD6_c66270 : CN'zETWD6 66270 :=
  ⟨cl1_66270, cl2_66270, cl3_66270, cl4_66270, cl5_66270, cl6_66270, cl7_66270, cl8_66270, cl9_66270, cl10_66270, cl11_66270, cl12_66270, cl13_66270, cl14_66270, cl15_66270⟩
theorem no_dissection_c66270 (D : CongruentDissection 66270) : False := not_tile_of_conditionsNSQzETWD6 66270 cnzETWD6_c66270 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c66270
