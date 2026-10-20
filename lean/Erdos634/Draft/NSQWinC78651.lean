/-
Draft/NSQWinC78651.lean -- `no_dissection_c78651` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 7 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_78651 : NQChkW 78651 := by decide +kernel
theorem cl2w_78651 : EllOrAsqW 78651 := by decide +kernel
theorem cl2_78651 : (EllChk2 78651 ∨ AsqChk 78651) := ellAsq_of_W cl2w_78651
theorem cl3_78651 : NSqChkSq 78651 := by decide +kernel
theorem cl4_78651 : HArithChkSq 78651 := by decide +kernel
theorem cl5_78651 : (78651 % 2 = 1 ∨ (78651 % 2 = 0 ∧ NHSqChkSq 78651)) := by decide +kernel
theorem cl6_78651 : LeafEsqW 78651 := by decide +kernel
theorem cl7_78651 : (78651 % 4 = 2 ∨ F1ChkParW 78651) := by decide +kernel
theorem cl10_78651 : IsoH9bChkW 78651 := by decide +kernel
theorem cl12_78651 : GammaChkDW 78651 := by decide +kernel
theorem cl13_78651 : S1t2ChkW 78651 := by decide +kernel
theorem cl14_78651 : RWChkT2W 78651 := by decide +kernel
theorem cl15_78651 : S5wChkW 78651 := by decide +kernel
theorem cf2z_78651 : F2z 78651 := by decide +kernel
theorem c_s2_78651_0 : ChunkP (S2P 78651) 0 212 := by decide +kernel
theorem c_s2_78651_1 : ChunkP (S2P 78651) 212 300 := by decide +kernel
theorem c_s2_78651_2 : ChunkP (S2P 78651) 300 367 := by decide +kernel
theorem c_s2_78651_3 : ChunkP (S2P 78651) 367 424 := by decide +kernel
theorem c_s2_78651_4 : ChunkP (S2P 78651) 424 474 := by decide +kernel
theorem c_s2_78651_5 : ChunkP (S2P 78651) 474 519 := by decide +kernel
theorem c_s2_78651_6 : ChunkP (S2P 78651) 519 (Nat.sqrt (4 * 78651) + 1) := by decide +kernel
theorem c_s3_78651_0 : ChunkP (S3P 78651) 0 40 := by decide +kernel
theorem c_s3_78651_1 : ChunkP (S3P 78651) 40 80 := by decide +kernel
theorem c_s3_78651_2 : ChunkP (S3P 78651) 80 120 := by decide +kernel
theorem c_s3_78651_3 : ChunkP (S3P 78651) 120 161 := by decide +kernel
theorem c_s3_78651_4 : ChunkP (S3P 78651) 161 201 := by decide +kernel
theorem c_s3_78651_5 : ChunkP (S3P 78651) 201 241 := by decide +kernel
theorem c_s3_78651_6 : ChunkP (S3P 78651) 241 (Nat.sqrt 78651 + 1) := by decide +kernel
theorem c_f4_78651_0 : ChunkP (F4zP 78651) 0 40 := by decide +kernel
theorem c_f4_78651_1 : ChunkP (F4zP 78651) 40 80 := by decide +kernel
theorem c_f4_78651_2 : ChunkP (F4zP 78651) 80 120 := by decide +kernel
theorem c_f4_78651_3 : ChunkP (F4zP 78651) 120 161 := by decide +kernel
theorem c_f4_78651_4 : ChunkP (F4zP 78651) 161 201 := by decide +kernel
theorem c_f4_78651_5 : ChunkP (F4zP 78651) 201 241 := by decide +kernel
theorem c_f4_78651_6 : ChunkP (F4zP 78651) 241 (Nat.sqrt 78651 + 1) := by decide +kernel
theorem c_f2_78651_0 : ChunkP (F2P 78651) 0 40 := by decide +kernel
theorem c_f2_78651_1 : ChunkP (F2P 78651) 40 80 := by decide +kernel
theorem c_f2_78651_2 : ChunkP (F2P 78651) 80 120 := by decide +kernel
theorem c_f2_78651_3 : ChunkP (F2P 78651) 120 161 := by decide +kernel
theorem c_f2_78651_4 : ChunkP (F2P 78651) 161 201 := by decide +kernel
theorem c_f2_78651_5 : ChunkP (F2P 78651) 201 241 := by decide +kernel
theorem c_f2_78651_6 : ChunkP (F2P 78651) 241 (Nat.sqrt 78651 + 1) := by decide +kernel
theorem c_f3_78651_0 : ChunkP (F3zP 78651) 0 40 := by decide +kernel
theorem c_f3_78651_1 : ChunkP (F3zP 78651) 40 80 := by decide +kernel
theorem c_f3_78651_2 : ChunkP (F3zP 78651) 80 120 := by decide +kernel
theorem c_f3_78651_3 : ChunkP (F3zP 78651) 120 161 := by decide +kernel
theorem c_f3_78651_4 : ChunkP (F3zP 78651) 161 201 := by decide +kernel
theorem c_f3_78651_5 : ChunkP (F3zP 78651) 201 241 := by decide +kernel
theorem c_f3_78651_6 : ChunkP (F3zP 78651) 241 (Nat.sqrt 78651 + 1) := by decide +kernel

theorem cl8_78651 : S2ChkSq 78651 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_78651_0 c_s2_78651_1) c_s2_78651_2) c_s2_78651_3) c_s2_78651_4) c_s2_78651_5) c_s2_78651_6))
theorem cl9_78651 : S3ChkSq 78651 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_78651_0 c_s3_78651_1) c_s3_78651_2) c_s3_78651_3) c_s3_78651_4) c_s3_78651_5) c_s3_78651_6))
theorem cl11_78651 : (NoF2ChkSq 78651 ∧ NoF3zChkSq 78651 ∧ NoF4zChkSq 78651) :=
  ⟨f2Sq_of_P cf2z_78651 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_78651_0 c_f2_78651_1) c_f2_78651_2) c_f2_78651_3) c_f2_78651_4) c_f2_78651_5) c_f2_78651_6)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_78651_0 c_f3_78651_1) c_f3_78651_2) c_f3_78651_3) c_f3_78651_4) c_f3_78651_5) c_f3_78651_6)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_78651_0 c_f4_78651_1) c_f4_78651_2) c_f4_78651_3) c_f4_78651_4) c_f4_78651_5) c_f4_78651_6))⟩

theorem cnzETWD6_c78651 : CN'zETWD6 78651 :=
  ⟨cl1_78651, cl2_78651, cl3_78651, cl4_78651, cl5_78651, cl6_78651, cl7_78651, cl8_78651, cl9_78651, cl10_78651, cl11_78651, cl12_78651, cl13_78651, cl14_78651, cl15_78651⟩
theorem no_dissection_c78651 (D : CongruentDissection 78651) : False := not_tile_of_conditionsNSQzETWD6 78651 cnzETWD6_c78651 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c78651
