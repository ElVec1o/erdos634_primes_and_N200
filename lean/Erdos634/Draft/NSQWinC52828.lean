/-
Draft/NSQWinC52828.lean -- `no_dissection_c52828` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 5 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_52828 : NQChkW 52828 := by decide +kernel
theorem cl2w_52828 : EllOrAsqW 52828 := by decide +kernel
theorem cl2_52828 : (EllChk2 52828 ∨ AsqChk 52828) := ellAsq_of_W cl2w_52828
theorem cl3_52828 : NSqChkSq 52828 := by decide +kernel
theorem cl4_52828 : HArithChkSq 52828 := by decide +kernel
theorem cl5_52828 : (52828 % 2 = 1 ∨ (52828 % 2 = 0 ∧ NHSqChkSq 52828)) := by decide +kernel
theorem cl6_52828 : LeafEsqW 52828 := by decide +kernel
theorem cl7_52828 : (52828 % 4 = 2 ∨ F1ChkParW 52828) := by decide +kernel
theorem cl10_52828 : IsoH9bChkW 52828 := by decide +kernel
theorem cl12_52828 : GammaChkDW 52828 := by decide +kernel
theorem cl13_52828 : S1t2ChkW 52828 := by decide +kernel
theorem cl14_52828 : RWChkT2W 52828 := by decide +kernel
theorem cl15_52828 : S5wChkW 52828 := by decide +kernel
theorem cf2z_52828 : F2z 52828 := by decide +kernel
theorem c_s2_52828_0 : ChunkP (S2P 52828) 0 206 := by decide +kernel
theorem c_s2_52828_1 : ChunkP (S2P 52828) 206 291 := by decide +kernel
theorem c_s2_52828_2 : ChunkP (S2P 52828) 291 356 := by decide +kernel
theorem c_s2_52828_3 : ChunkP (S2P 52828) 356 411 := by decide +kernel
theorem c_s2_52828_4 : ChunkP (S2P 52828) 411 (Nat.sqrt (4 * 52828) + 1) := by decide +kernel
theorem c_s3_52828_0 : ChunkP (S3P 52828) 0 46 := by decide +kernel
theorem c_s3_52828_1 : ChunkP (S3P 52828) 46 92 := by decide +kernel
theorem c_s3_52828_2 : ChunkP (S3P 52828) 92 138 := by decide +kernel
theorem c_s3_52828_3 : ChunkP (S3P 52828) 138 184 := by decide +kernel
theorem c_s3_52828_4 : ChunkP (S3P 52828) 184 (Nat.sqrt 52828 + 1) := by decide +kernel
theorem c_f4_52828_0 : ChunkP (F4zP 52828) 0 46 := by decide +kernel
theorem c_f4_52828_1 : ChunkP (F4zP 52828) 46 92 := by decide +kernel
theorem c_f4_52828_2 : ChunkP (F4zP 52828) 92 138 := by decide +kernel
theorem c_f4_52828_3 : ChunkP (F4zP 52828) 138 184 := by decide +kernel
theorem c_f4_52828_4 : ChunkP (F4zP 52828) 184 (Nat.sqrt 52828 + 1) := by decide +kernel
theorem c_f2_52828_0 : ChunkP (F2P 52828) 0 46 := by decide +kernel
theorem c_f2_52828_1 : ChunkP (F2P 52828) 46 92 := by decide +kernel
theorem c_f2_52828_2 : ChunkP (F2P 52828) 92 138 := by decide +kernel
theorem c_f2_52828_3 : ChunkP (F2P 52828) 138 184 := by decide +kernel
theorem c_f2_52828_4 : ChunkP (F2P 52828) 184 (Nat.sqrt 52828 + 1) := by decide +kernel
theorem c_f3_52828_0 : ChunkP (F3zP 52828) 0 46 := by decide +kernel
theorem c_f3_52828_1 : ChunkP (F3zP 52828) 46 92 := by decide +kernel
theorem c_f3_52828_2 : ChunkP (F3zP 52828) 92 138 := by decide +kernel
theorem c_f3_52828_3 : ChunkP (F3zP 52828) 138 184 := by decide +kernel
theorem c_f3_52828_4 : ChunkP (F3zP 52828) 184 (Nat.sqrt 52828 + 1) := by decide +kernel

theorem cl8_52828 : S2ChkSq 52828 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s2_52828_0 c_s2_52828_1) c_s2_52828_2) c_s2_52828_3) c_s2_52828_4))
theorem cl9_52828 : S3ChkSq 52828 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s3_52828_0 c_s3_52828_1) c_s3_52828_2) c_s3_52828_3) c_s3_52828_4))
theorem cl11_52828 : (NoF2ChkSq 52828 ∧ NoF3zChkSq 52828 ∧ NoF4zChkSq 52828) :=
  ⟨f2Sq_of_P cf2z_52828 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f2_52828_0 c_f2_52828_1) c_f2_52828_2) c_f2_52828_3) c_f2_52828_4)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f3_52828_0 c_f3_52828_1) c_f3_52828_2) c_f3_52828_3) c_f3_52828_4)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f4_52828_0 c_f4_52828_1) c_f4_52828_2) c_f4_52828_3) c_f4_52828_4))⟩

theorem cnzETWD6_c52828 : CN'zETWD6 52828 :=
  ⟨cl1_52828, cl2_52828, cl3_52828, cl4_52828, cl5_52828, cl6_52828, cl7_52828, cl8_52828, cl9_52828, cl10_52828, cl11_52828, cl12_52828, cl13_52828, cl14_52828, cl15_52828⟩
theorem no_dissection_c52828 (D : CongruentDissection 52828) : False := not_tile_of_conditionsNSQzETWD6 52828 cnzETWD6_c52828 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c52828
