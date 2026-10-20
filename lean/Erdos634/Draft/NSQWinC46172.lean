/-
Draft/NSQWinC46172.lean -- `no_dissection_c46172` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 4 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_46172 : NQChkW 46172 := by decide +kernel
theorem cl2w_46172 : EllOrAsqW 46172 := by decide +kernel
theorem cl2_46172 : (EllChk2 46172 ∨ AsqChk 46172) := ellAsq_of_W cl2w_46172
theorem cl3_46172 : NSqChkSq 46172 := by decide +kernel
theorem cl4_46172 : HArithChkSq 46172 := by decide +kernel
theorem cl5_46172 : (46172 % 2 = 1 ∨ (46172 % 2 = 0 ∧ NHSqChkSq 46172)) := by decide +kernel
theorem cl6_46172 : LeafEsqW 46172 := by decide +kernel
theorem cl7_46172 : (46172 % 4 = 2 ∨ F1ChkParW 46172) := by decide +kernel
theorem cl10_46172 : IsoH9bChkW 46172 := by decide +kernel
theorem cl12_46172 : GammaChkDW 46172 := by decide +kernel
theorem cl13_46172 : S1t2ChkW 46172 := by decide +kernel
theorem cl14_46172 : RWChkT2W 46172 := by decide +kernel
theorem cl15_46172 : S5wChkW 46172 := by decide +kernel
theorem cf2z_46172 : F2z 46172 := by decide +kernel
theorem c_s2_46172_0 : ChunkP (S2P 46172) 0 215 := by decide +kernel
theorem c_s2_46172_1 : ChunkP (S2P 46172) 215 304 := by decide +kernel
theorem c_s2_46172_2 : ChunkP (S2P 46172) 304 372 := by decide +kernel
theorem c_s2_46172_3 : ChunkP (S2P 46172) 372 (Nat.sqrt (4 * 46172) + 1) := by decide +kernel
theorem c_s3_46172_0 : ChunkP (S3P 46172) 0 54 := by decide +kernel
theorem c_s3_46172_1 : ChunkP (S3P 46172) 54 108 := by decide +kernel
theorem c_s3_46172_2 : ChunkP (S3P 46172) 108 161 := by decide +kernel
theorem c_s3_46172_3 : ChunkP (S3P 46172) 161 (Nat.sqrt 46172 + 1) := by decide +kernel
theorem c_f4_46172_0 : ChunkP (F4zP 46172) 0 54 := by decide +kernel
theorem c_f4_46172_1 : ChunkP (F4zP 46172) 54 108 := by decide +kernel
theorem c_f4_46172_2 : ChunkP (F4zP 46172) 108 161 := by decide +kernel
theorem c_f4_46172_3 : ChunkP (F4zP 46172) 161 (Nat.sqrt 46172 + 1) := by decide +kernel
theorem c_f2_46172_0 : ChunkP (F2P 46172) 0 54 := by decide +kernel
theorem c_f2_46172_1 : ChunkP (F2P 46172) 54 108 := by decide +kernel
theorem c_f2_46172_2 : ChunkP (F2P 46172) 108 161 := by decide +kernel
theorem c_f2_46172_3 : ChunkP (F2P 46172) 161 (Nat.sqrt 46172 + 1) := by decide +kernel
theorem c_f3_46172_0 : ChunkP (F3zP 46172) 0 54 := by decide +kernel
theorem c_f3_46172_1 : ChunkP (F3zP 46172) 54 108 := by decide +kernel
theorem c_f3_46172_2 : ChunkP (F3zP 46172) 108 161 := by decide +kernel
theorem c_f3_46172_3 : ChunkP (F3zP 46172) 161 (Nat.sqrt 46172 + 1) := by decide +kernel

theorem cl8_46172 : S2ChkSq 46172 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append c_s2_46172_0 c_s2_46172_1) c_s2_46172_2) c_s2_46172_3))
theorem cl9_46172 : S3ChkSq 46172 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append c_s3_46172_0 c_s3_46172_1) c_s3_46172_2) c_s3_46172_3))
theorem cl11_46172 : (NoF2ChkSq 46172 ∧ NoF3zChkSq 46172 ∧ NoF4zChkSq 46172) :=
  ⟨f2Sq_of_P cf2z_46172 (chunk_full (chunk_append (chunk_append (chunk_append c_f2_46172_0 c_f2_46172_1) c_f2_46172_2) c_f2_46172_3)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append c_f3_46172_0 c_f3_46172_1) c_f3_46172_2) c_f3_46172_3)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append c_f4_46172_0 c_f4_46172_1) c_f4_46172_2) c_f4_46172_3))⟩

theorem cnzETWD6_c46172 : CN'zETWD6 46172 :=
  ⟨cl1_46172, cl2_46172, cl3_46172, cl4_46172, cl5_46172, cl6_46172, cl7_46172, cl8_46172, cl9_46172, cl10_46172, cl11_46172, cl12_46172, cl13_46172, cl14_46172, cl15_46172⟩
theorem no_dissection_c46172 (D : CongruentDissection 46172) : False := not_tile_of_conditionsNSQzETWD6 46172 cnzETWD6_c46172 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c46172
