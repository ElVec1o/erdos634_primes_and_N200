/-
Draft/NSQWinC52672.lean -- `no_dissection_c52672` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 5 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_52672 : NQChkW 52672 := by decide +kernel
theorem cl2w_52672 : EllOrAsqW 52672 := by decide +kernel
theorem cl2_52672 : (EllChk2 52672 ∨ AsqChk 52672) := ellAsq_of_W cl2w_52672
theorem cl3_52672 : NSqChkSq 52672 := by decide +kernel
theorem cl4_52672 : HArithChkSq 52672 := by decide +kernel
theorem cl5_52672 : (52672 % 2 = 1 ∨ (52672 % 2 = 0 ∧ NHSqChkSq 52672)) := by decide +kernel
theorem cl6_52672 : LeafEsqW 52672 := by decide +kernel
theorem cl7_52672 : (52672 % 4 = 2 ∨ F1ChkParW 52672) := by decide +kernel
theorem cl10_52672 : IsoH9bChkW 52672 := by decide +kernel
theorem cl12_52672 : GammaChkDW 52672 := by decide +kernel
theorem cl13_52672 : S1t2ChkW 52672 := by decide +kernel
theorem cl14_52672 : RWChkT2W 52672 := by decide +kernel
theorem cl15_52672 : S5wChkW 52672 := by decide +kernel
theorem cf2z_52672 : F2z 52672 := by decide +kernel
theorem c_s2_52672_0 : ChunkP (S2P 52672) 0 206 := by decide +kernel
theorem c_s2_52672_1 : ChunkP (S2P 52672) 206 291 := by decide +kernel
theorem c_s2_52672_2 : ChunkP (S2P 52672) 291 356 := by decide +kernel
theorem c_s2_52672_3 : ChunkP (S2P 52672) 356 411 := by decide +kernel
theorem c_s2_52672_4 : ChunkP (S2P 52672) 411 (Nat.sqrt (4 * 52672) + 1) := by decide +kernel
theorem c_s3_52672_0 : ChunkP (S3P 52672) 0 46 := by decide +kernel
theorem c_s3_52672_1 : ChunkP (S3P 52672) 46 92 := by decide +kernel
theorem c_s3_52672_2 : ChunkP (S3P 52672) 92 138 := by decide +kernel
theorem c_s3_52672_3 : ChunkP (S3P 52672) 138 184 := by decide +kernel
theorem c_s3_52672_4 : ChunkP (S3P 52672) 184 (Nat.sqrt 52672 + 1) := by decide +kernel
theorem c_f4_52672_0 : ChunkP (F4zP 52672) 0 46 := by decide +kernel
theorem c_f4_52672_1 : ChunkP (F4zP 52672) 46 92 := by decide +kernel
theorem c_f4_52672_2 : ChunkP (F4zP 52672) 92 138 := by decide +kernel
theorem c_f4_52672_3 : ChunkP (F4zP 52672) 138 184 := by decide +kernel
theorem c_f4_52672_4 : ChunkP (F4zP 52672) 184 (Nat.sqrt 52672 + 1) := by decide +kernel
theorem c_f2_52672_0 : ChunkP (F2P 52672) 0 46 := by decide +kernel
theorem c_f2_52672_1 : ChunkP (F2P 52672) 46 92 := by decide +kernel
theorem c_f2_52672_2 : ChunkP (F2P 52672) 92 138 := by decide +kernel
theorem c_f2_52672_3 : ChunkP (F2P 52672) 138 184 := by decide +kernel
theorem c_f2_52672_4 : ChunkP (F2P 52672) 184 (Nat.sqrt 52672 + 1) := by decide +kernel
theorem c_f3_52672_0 : ChunkP (F3zP 52672) 0 46 := by decide +kernel
theorem c_f3_52672_1 : ChunkP (F3zP 52672) 46 92 := by decide +kernel
theorem c_f3_52672_2 : ChunkP (F3zP 52672) 92 138 := by decide +kernel
theorem c_f3_52672_3 : ChunkP (F3zP 52672) 138 184 := by decide +kernel
theorem c_f3_52672_4 : ChunkP (F3zP 52672) 184 (Nat.sqrt 52672 + 1) := by decide +kernel

theorem cl8_52672 : S2ChkSq 52672 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s2_52672_0 c_s2_52672_1) c_s2_52672_2) c_s2_52672_3) c_s2_52672_4))
theorem cl9_52672 : S3ChkSq 52672 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s3_52672_0 c_s3_52672_1) c_s3_52672_2) c_s3_52672_3) c_s3_52672_4))
theorem cl11_52672 : (NoF2ChkSq 52672 ∧ NoF3zChkSq 52672 ∧ NoF4zChkSq 52672) :=
  ⟨f2Sq_of_P cf2z_52672 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f2_52672_0 c_f2_52672_1) c_f2_52672_2) c_f2_52672_3) c_f2_52672_4)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f3_52672_0 c_f3_52672_1) c_f3_52672_2) c_f3_52672_3) c_f3_52672_4)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f4_52672_0 c_f4_52672_1) c_f4_52672_2) c_f4_52672_3) c_f4_52672_4))⟩

theorem cnzETWD6_c52672 : CN'zETWD6 52672 :=
  ⟨cl1_52672, cl2_52672, cl3_52672, cl4_52672, cl5_52672, cl6_52672, cl7_52672, cl8_52672, cl9_52672, cl10_52672, cl11_52672, cl12_52672, cl13_52672, cl14_52672, cl15_52672⟩
theorem no_dissection_c52672 (D : CongruentDissection 52672) : False := not_tile_of_conditionsNSQzETWD6 52672 cnzETWD6_c52672 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c52672
