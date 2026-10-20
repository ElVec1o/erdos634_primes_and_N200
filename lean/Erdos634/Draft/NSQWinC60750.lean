/-
Draft/NSQWinC60750.lean -- `no_dissection_c60750` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 6 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_60750 : NQChkW 60750 := by decide +kernel
theorem cl2w_60750 : EllOrAsqW 60750 := by decide +kernel
theorem cl2_60750 : (EllChk2 60750 ∨ AsqChk 60750) := ellAsq_of_W cl2w_60750
theorem cl3_60750 : NSqChkSq 60750 := by decide +kernel
theorem cl4_60750 : HArithChkSq 60750 := by decide +kernel
theorem cl5_60750 : (60750 % 2 = 1 ∨ (60750 % 2 = 0 ∧ NHSqChkSq 60750)) := by decide +kernel
theorem cl6_60750 : LeafEsqW 60750 := by decide +kernel
theorem cl7_60750 : (60750 % 4 = 2 ∨ F1ChkParW 60750) := by decide +kernel
theorem cl10_60750 : IsoH9bChkW 60750 := by decide +kernel
theorem cl12_60750 : GammaChkDW 60750 := by decide +kernel
theorem cl13_60750 : S1t2ChkW 60750 := by decide +kernel
theorem cl14_60750 : RWChkT2W 60750 := by decide +kernel
theorem cl15_60750 : S5wChkW 60750 := by decide +kernel
theorem cf2z_60750 : F2z 60750 := by decide +kernel
theorem c_s2_60750_0 : ChunkP (S2P 60750) 0 201 := by decide +kernel
theorem c_s2_60750_1 : ChunkP (S2P 60750) 201 285 := by decide +kernel
theorem c_s2_60750_2 : ChunkP (S2P 60750) 285 349 := by decide +kernel
theorem c_s2_60750_3 : ChunkP (S2P 60750) 349 403 := by decide +kernel
theorem c_s2_60750_4 : ChunkP (S2P 60750) 403 450 := by decide +kernel
theorem c_s2_60750_5 : ChunkP (S2P 60750) 450 (Nat.sqrt (4 * 60750) + 1) := by decide +kernel
theorem c_s3_60750_0 : ChunkP (S3P 60750) 0 41 := by decide +kernel
theorem c_s3_60750_1 : ChunkP (S3P 60750) 41 82 := by decide +kernel
theorem c_s3_60750_2 : ChunkP (S3P 60750) 82 124 := by decide +kernel
theorem c_s3_60750_3 : ChunkP (S3P 60750) 124 165 := by decide +kernel
theorem c_s3_60750_4 : ChunkP (S3P 60750) 165 206 := by decide +kernel
theorem c_s3_60750_5 : ChunkP (S3P 60750) 206 (Nat.sqrt 60750 + 1) := by decide +kernel
theorem c_f4_60750_0 : ChunkP (F4zP 60750) 0 41 := by decide +kernel
theorem c_f4_60750_1 : ChunkP (F4zP 60750) 41 82 := by decide +kernel
theorem c_f4_60750_2 : ChunkP (F4zP 60750) 82 124 := by decide +kernel
theorem c_f4_60750_3 : ChunkP (F4zP 60750) 124 165 := by decide +kernel
theorem c_f4_60750_4 : ChunkP (F4zP 60750) 165 206 := by decide +kernel
theorem c_f4_60750_5 : ChunkP (F4zP 60750) 206 (Nat.sqrt 60750 + 1) := by decide +kernel
theorem c_f2_60750_0 : ChunkP (F2P 60750) 0 41 := by decide +kernel
theorem c_f2_60750_1 : ChunkP (F2P 60750) 41 82 := by decide +kernel
theorem c_f2_60750_2 : ChunkP (F2P 60750) 82 124 := by decide +kernel
theorem c_f2_60750_3 : ChunkP (F2P 60750) 124 165 := by decide +kernel
theorem c_f2_60750_4 : ChunkP (F2P 60750) 165 206 := by decide +kernel
theorem c_f2_60750_5 : ChunkP (F2P 60750) 206 (Nat.sqrt 60750 + 1) := by decide +kernel
theorem c_f3_60750_0 : ChunkP (F3zP 60750) 0 41 := by decide +kernel
theorem c_f3_60750_1 : ChunkP (F3zP 60750) 41 82 := by decide +kernel
theorem c_f3_60750_2 : ChunkP (F3zP 60750) 82 124 := by decide +kernel
theorem c_f3_60750_3 : ChunkP (F3zP 60750) 124 165 := by decide +kernel
theorem c_f3_60750_4 : ChunkP (F3zP 60750) 165 206 := by decide +kernel
theorem c_f3_60750_5 : ChunkP (F3zP 60750) 206 (Nat.sqrt 60750 + 1) := by decide +kernel

theorem cl8_60750 : S2ChkSq 60750 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_60750_0 c_s2_60750_1) c_s2_60750_2) c_s2_60750_3) c_s2_60750_4) c_s2_60750_5))
theorem cl9_60750 : S3ChkSq 60750 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_60750_0 c_s3_60750_1) c_s3_60750_2) c_s3_60750_3) c_s3_60750_4) c_s3_60750_5))
theorem cl11_60750 : (NoF2ChkSq 60750 ∧ NoF3zChkSq 60750 ∧ NoF4zChkSq 60750) :=
  ⟨f2Sq_of_P cf2z_60750 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_60750_0 c_f2_60750_1) c_f2_60750_2) c_f2_60750_3) c_f2_60750_4) c_f2_60750_5)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_60750_0 c_f3_60750_1) c_f3_60750_2) c_f3_60750_3) c_f3_60750_4) c_f3_60750_5)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_60750_0 c_f4_60750_1) c_f4_60750_2) c_f4_60750_3) c_f4_60750_4) c_f4_60750_5))⟩

theorem cnzETWD6_c60750 : CN'zETWD6 60750 :=
  ⟨cl1_60750, cl2_60750, cl3_60750, cl4_60750, cl5_60750, cl6_60750, cl7_60750, cl8_60750, cl9_60750, cl10_60750, cl11_60750, cl12_60750, cl13_60750, cl14_60750, cl15_60750⟩
theorem no_dissection_c60750 (D : CongruentDissection 60750) : False := not_tile_of_conditionsNSQzETWD6 60750 cnzETWD6_c60750 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c60750
