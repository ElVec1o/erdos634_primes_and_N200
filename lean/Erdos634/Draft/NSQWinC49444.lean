/-
Draft/NSQWinC49444.lean -- `no_dissection_c49444` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 5 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_49444 : NQChkW 49444 := by decide +kernel
theorem cl2w_49444 : EllOrAsqW 49444 := by decide +kernel
theorem cl2_49444 : (EllChk2 49444 ∨ AsqChk 49444) := ellAsq_of_W cl2w_49444
theorem cl3_49444 : NSqChkSq 49444 := by decide +kernel
theorem cl4_49444 : HArithChkSq 49444 := by decide +kernel
theorem cl5_49444 : (49444 % 2 = 1 ∨ (49444 % 2 = 0 ∧ NHSqChkSq 49444)) := by decide +kernel
theorem cl6_49444 : LeafEsqW 49444 := by decide +kernel
theorem cl7_49444 : (49444 % 4 = 2 ∨ F1ChkParW 49444) := by decide +kernel
theorem cl10_49444 : IsoH9bChkW 49444 := by decide +kernel
theorem cl12_49444 : GammaChkDW 49444 := by decide +kernel
theorem cl13_49444 : S1t2ChkW 49444 := by decide +kernel
theorem cl14_49444 : RWChkT2W 49444 := by decide +kernel
theorem cl15_49444 : S5wChkW 49444 := by decide +kernel
theorem cf2z_49444 : F2z 49444 := by decide +kernel
theorem c_s2_49444_0 : ChunkP (S2P 49444) 0 199 := by decide +kernel
theorem c_s2_49444_1 : ChunkP (S2P 49444) 199 281 := by decide +kernel
theorem c_s2_49444_2 : ChunkP (S2P 49444) 281 345 := by decide +kernel
theorem c_s2_49444_3 : ChunkP (S2P 49444) 345 398 := by decide +kernel
theorem c_s2_49444_4 : ChunkP (S2P 49444) 398 (Nat.sqrt (4 * 49444) + 1) := by decide +kernel
theorem c_s3_49444_0 : ChunkP (S3P 49444) 0 45 := by decide +kernel
theorem c_s3_49444_1 : ChunkP (S3P 49444) 45 89 := by decide +kernel
theorem c_s3_49444_2 : ChunkP (S3P 49444) 89 134 := by decide +kernel
theorem c_s3_49444_3 : ChunkP (S3P 49444) 134 178 := by decide +kernel
theorem c_s3_49444_4 : ChunkP (S3P 49444) 178 (Nat.sqrt 49444 + 1) := by decide +kernel
theorem c_f4_49444_0 : ChunkP (F4zP 49444) 0 45 := by decide +kernel
theorem c_f4_49444_1 : ChunkP (F4zP 49444) 45 89 := by decide +kernel
theorem c_f4_49444_2 : ChunkP (F4zP 49444) 89 134 := by decide +kernel
theorem c_f4_49444_3 : ChunkP (F4zP 49444) 134 178 := by decide +kernel
theorem c_f4_49444_4 : ChunkP (F4zP 49444) 178 (Nat.sqrt 49444 + 1) := by decide +kernel
theorem c_f2_49444_0 : ChunkP (F2P 49444) 0 45 := by decide +kernel
theorem c_f2_49444_1 : ChunkP (F2P 49444) 45 89 := by decide +kernel
theorem c_f2_49444_2 : ChunkP (F2P 49444) 89 134 := by decide +kernel
theorem c_f2_49444_3 : ChunkP (F2P 49444) 134 178 := by decide +kernel
theorem c_f2_49444_4 : ChunkP (F2P 49444) 178 (Nat.sqrt 49444 + 1) := by decide +kernel
theorem c_f3_49444_0 : ChunkP (F3zP 49444) 0 45 := by decide +kernel
theorem c_f3_49444_1 : ChunkP (F3zP 49444) 45 89 := by decide +kernel
theorem c_f3_49444_2 : ChunkP (F3zP 49444) 89 134 := by decide +kernel
theorem c_f3_49444_3 : ChunkP (F3zP 49444) 134 178 := by decide +kernel
theorem c_f3_49444_4 : ChunkP (F3zP 49444) 178 (Nat.sqrt 49444 + 1) := by decide +kernel

theorem cl8_49444 : S2ChkSq 49444 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s2_49444_0 c_s2_49444_1) c_s2_49444_2) c_s2_49444_3) c_s2_49444_4))
theorem cl9_49444 : S3ChkSq 49444 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s3_49444_0 c_s3_49444_1) c_s3_49444_2) c_s3_49444_3) c_s3_49444_4))
theorem cl11_49444 : (NoF2ChkSq 49444 ∧ NoF3zChkSq 49444 ∧ NoF4zChkSq 49444) :=
  ⟨f2Sq_of_P cf2z_49444 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f2_49444_0 c_f2_49444_1) c_f2_49444_2) c_f2_49444_3) c_f2_49444_4)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f3_49444_0 c_f3_49444_1) c_f3_49444_2) c_f3_49444_3) c_f3_49444_4)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f4_49444_0 c_f4_49444_1) c_f4_49444_2) c_f4_49444_3) c_f4_49444_4))⟩

theorem cnzETWD6_c49444 : CN'zETWD6 49444 :=
  ⟨cl1_49444, cl2_49444, cl3_49444, cl4_49444, cl5_49444, cl6_49444, cl7_49444, cl8_49444, cl9_49444, cl10_49444, cl11_49444, cl12_49444, cl13_49444, cl14_49444, cl15_49444⟩
theorem no_dissection_c49444 (D : CongruentDissection 49444) : False := not_tile_of_conditionsNSQzETWD6 49444 cnzETWD6_c49444 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c49444
