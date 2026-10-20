/-
Draft/NSQWinC90750.lean -- `no_dissection_c90750` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 8 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_90750 : NQChkW 90750 := by decide +kernel
theorem cl2w_90750 : EllOrAsqW 90750 := by decide +kernel
theorem cl2_90750 : (EllChk2 90750 ∨ AsqChk 90750) := ellAsq_of_W cl2w_90750
theorem cl3_90750 : NSqChkSq 90750 := by decide +kernel
theorem cl4_90750 : HArithChkSq 90750 := by decide +kernel
theorem cl5_90750 : (90750 % 2 = 1 ∨ (90750 % 2 = 0 ∧ NHSqChkSq 90750)) := by decide +kernel
theorem cl6_90750 : LeafEsqW 90750 := by decide +kernel
theorem cl7_90750 : (90750 % 4 = 2 ∨ F1ChkParW 90750) := by decide +kernel
theorem cl10_90750 : IsoH9bChkW 90750 := by decide +kernel
theorem cl12_90750 : GammaChkDW 90750 := by decide +kernel
theorem cl13_90750 : S1t2ChkW 90750 := by decide +kernel
theorem cl14_90750 : RWChkT2W 90750 := by decide +kernel
theorem cl15_90750 : S5wChkW 90750 := by decide +kernel
theorem cf2z_90750 : F2z 90750 := by decide +kernel
theorem c_s2_90750_0 : ChunkP (S2P 90750) 0 213 := by decide +kernel
theorem c_s2_90750_1 : ChunkP (S2P 90750) 213 302 := by decide +kernel
theorem c_s2_90750_2 : ChunkP (S2P 90750) 302 369 := by decide +kernel
theorem c_s2_90750_3 : ChunkP (S2P 90750) 369 426 := by decide +kernel
theorem c_s2_90750_4 : ChunkP (S2P 90750) 426 477 := by decide +kernel
theorem c_s2_90750_5 : ChunkP (S2P 90750) 477 522 := by decide +kernel
theorem c_s2_90750_6 : ChunkP (S2P 90750) 522 564 := by decide +kernel
theorem c_s2_90750_7 : ChunkP (S2P 90750) 564 (Nat.sqrt (4 * 90750) + 1) := by decide +kernel
theorem c_s3_90750_0 : ChunkP (S3P 90750) 0 38 := by decide +kernel
theorem c_s3_90750_1 : ChunkP (S3P 90750) 38 76 := by decide +kernel
theorem c_s3_90750_2 : ChunkP (S3P 90750) 76 113 := by decide +kernel
theorem c_s3_90750_3 : ChunkP (S3P 90750) 113 151 := by decide +kernel
theorem c_s3_90750_4 : ChunkP (S3P 90750) 151 189 := by decide +kernel
theorem c_s3_90750_5 : ChunkP (S3P 90750) 189 226 := by decide +kernel
theorem c_s3_90750_6 : ChunkP (S3P 90750) 226 264 := by decide +kernel
theorem c_s3_90750_7 : ChunkP (S3P 90750) 264 (Nat.sqrt 90750 + 1) := by decide +kernel
theorem c_f4_90750_0 : ChunkP (F4zP 90750) 0 38 := by decide +kernel
theorem c_f4_90750_1 : ChunkP (F4zP 90750) 38 76 := by decide +kernel
theorem c_f4_90750_2 : ChunkP (F4zP 90750) 76 113 := by decide +kernel
theorem c_f4_90750_3 : ChunkP (F4zP 90750) 113 151 := by decide +kernel
theorem c_f4_90750_4 : ChunkP (F4zP 90750) 151 189 := by decide +kernel
theorem c_f4_90750_5 : ChunkP (F4zP 90750) 189 226 := by decide +kernel
theorem c_f4_90750_6 : ChunkP (F4zP 90750) 226 264 := by decide +kernel
theorem c_f4_90750_7 : ChunkP (F4zP 90750) 264 (Nat.sqrt 90750 + 1) := by decide +kernel
theorem c_f2_90750_0 : ChunkP (F2P 90750) 0 38 := by decide +kernel
theorem c_f2_90750_1 : ChunkP (F2P 90750) 38 76 := by decide +kernel
theorem c_f2_90750_2 : ChunkP (F2P 90750) 76 113 := by decide +kernel
theorem c_f2_90750_3 : ChunkP (F2P 90750) 113 151 := by decide +kernel
theorem c_f2_90750_4 : ChunkP (F2P 90750) 151 189 := by decide +kernel
theorem c_f2_90750_5 : ChunkP (F2P 90750) 189 226 := by decide +kernel
theorem c_f2_90750_6 : ChunkP (F2P 90750) 226 264 := by decide +kernel
theorem c_f2_90750_7 : ChunkP (F2P 90750) 264 (Nat.sqrt 90750 + 1) := by decide +kernel
theorem c_f3_90750_0 : ChunkP (F3zP 90750) 0 38 := by decide +kernel
theorem c_f3_90750_1 : ChunkP (F3zP 90750) 38 76 := by decide +kernel
theorem c_f3_90750_2 : ChunkP (F3zP 90750) 76 113 := by decide +kernel
theorem c_f3_90750_3 : ChunkP (F3zP 90750) 113 151 := by decide +kernel
theorem c_f3_90750_4 : ChunkP (F3zP 90750) 151 189 := by decide +kernel
theorem c_f3_90750_5 : ChunkP (F3zP 90750) 189 226 := by decide +kernel
theorem c_f3_90750_6 : ChunkP (F3zP 90750) 226 264 := by decide +kernel
theorem c_f3_90750_7 : ChunkP (F3zP 90750) 264 (Nat.sqrt 90750 + 1) := by decide +kernel

theorem cl8_90750 : S2ChkSq 90750 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_90750_0 c_s2_90750_1) c_s2_90750_2) c_s2_90750_3) c_s2_90750_4) c_s2_90750_5) c_s2_90750_6) c_s2_90750_7))
theorem cl9_90750 : S3ChkSq 90750 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_90750_0 c_s3_90750_1) c_s3_90750_2) c_s3_90750_3) c_s3_90750_4) c_s3_90750_5) c_s3_90750_6) c_s3_90750_7))
theorem cl11_90750 : (NoF2ChkSq 90750 ∧ NoF3zChkSq 90750 ∧ NoF4zChkSq 90750) :=
  ⟨f2Sq_of_P cf2z_90750 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_90750_0 c_f2_90750_1) c_f2_90750_2) c_f2_90750_3) c_f2_90750_4) c_f2_90750_5) c_f2_90750_6) c_f2_90750_7)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_90750_0 c_f3_90750_1) c_f3_90750_2) c_f3_90750_3) c_f3_90750_4) c_f3_90750_5) c_f3_90750_6) c_f3_90750_7)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_90750_0 c_f4_90750_1) c_f4_90750_2) c_f4_90750_3) c_f4_90750_4) c_f4_90750_5) c_f4_90750_6) c_f4_90750_7))⟩

theorem cnzETWD6_c90750 : CN'zETWD6 90750 :=
  ⟨cl1_90750, cl2_90750, cl3_90750, cl4_90750, cl5_90750, cl6_90750, cl7_90750, cl8_90750, cl9_90750, cl10_90750, cl11_90750, cl12_90750, cl13_90750, cl14_90750, cl15_90750⟩
theorem no_dissection_c90750 (D : CongruentDissection 90750) : False := not_tile_of_conditionsNSQzETWD6 90750 cnzETWD6_c90750 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c90750
