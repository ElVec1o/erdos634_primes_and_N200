/-
Draft/NSQWinC55150.lean -- `no_dissection_c55150` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 5 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_55150 : NQChkW 55150 := by decide +kernel
theorem cl2w_55150 : EllOrAsqW 55150 := by decide +kernel
theorem cl2_55150 : (EllChk2 55150 ∨ AsqChk 55150) := ellAsq_of_W cl2w_55150
theorem cl3_55150 : NSqChkSq 55150 := by decide +kernel
theorem cl4_55150 : HArithChkSq 55150 := by decide +kernel
theorem cl5_55150 : (55150 % 2 = 1 ∨ (55150 % 2 = 0 ∧ NHSqChkSq 55150)) := by decide +kernel
theorem cl6_55150 : LeafEsqW 55150 := by decide +kernel
theorem cl7_55150 : (55150 % 4 = 2 ∨ F1ChkParW 55150) := by decide +kernel
theorem cl10_55150 : IsoH9bChkW 55150 := by decide +kernel
theorem cl12_55150 : GammaChkDW 55150 := by decide +kernel
theorem cl13_55150 : S1t2ChkW 55150 := by decide +kernel
theorem cl14_55150 : RWChkT2W 55150 := by decide +kernel
theorem cl15_55150 : S5wChkW 55150 := by decide +kernel
theorem cf2z_55150 : F2z 55150 := by decide +kernel
theorem c_s2_55150_0 : ChunkP (S2P 55150) 0 210 := by decide +kernel
theorem c_s2_55150_1 : ChunkP (S2P 55150) 210 297 := by decide +kernel
theorem c_s2_55150_2 : ChunkP (S2P 55150) 297 364 := by decide +kernel
theorem c_s2_55150_3 : ChunkP (S2P 55150) 364 420 := by decide +kernel
theorem c_s2_55150_4 : ChunkP (S2P 55150) 420 (Nat.sqrt (4 * 55150) + 1) := by decide +kernel
theorem c_s3_55150_0 : ChunkP (S3P 55150) 0 47 := by decide +kernel
theorem c_s3_55150_1 : ChunkP (S3P 55150) 47 94 := by decide +kernel
theorem c_s3_55150_2 : ChunkP (S3P 55150) 94 141 := by decide +kernel
theorem c_s3_55150_3 : ChunkP (S3P 55150) 141 188 := by decide +kernel
theorem c_s3_55150_4 : ChunkP (S3P 55150) 188 (Nat.sqrt 55150 + 1) := by decide +kernel
theorem c_f4_55150_0 : ChunkP (F4zP 55150) 0 47 := by decide +kernel
theorem c_f4_55150_1 : ChunkP (F4zP 55150) 47 94 := by decide +kernel
theorem c_f4_55150_2 : ChunkP (F4zP 55150) 94 141 := by decide +kernel
theorem c_f4_55150_3 : ChunkP (F4zP 55150) 141 188 := by decide +kernel
theorem c_f4_55150_4 : ChunkP (F4zP 55150) 188 (Nat.sqrt 55150 + 1) := by decide +kernel
theorem c_f2_55150_0 : ChunkP (F2P 55150) 0 47 := by decide +kernel
theorem c_f2_55150_1 : ChunkP (F2P 55150) 47 94 := by decide +kernel
theorem c_f2_55150_2 : ChunkP (F2P 55150) 94 141 := by decide +kernel
theorem c_f2_55150_3 : ChunkP (F2P 55150) 141 188 := by decide +kernel
theorem c_f2_55150_4 : ChunkP (F2P 55150) 188 (Nat.sqrt 55150 + 1) := by decide +kernel
theorem c_f3_55150_0 : ChunkP (F3zP 55150) 0 47 := by decide +kernel
theorem c_f3_55150_1 : ChunkP (F3zP 55150) 47 94 := by decide +kernel
theorem c_f3_55150_2 : ChunkP (F3zP 55150) 94 141 := by decide +kernel
theorem c_f3_55150_3 : ChunkP (F3zP 55150) 141 188 := by decide +kernel
theorem c_f3_55150_4 : ChunkP (F3zP 55150) 188 (Nat.sqrt 55150 + 1) := by decide +kernel

theorem cl8_55150 : S2ChkSq 55150 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s2_55150_0 c_s2_55150_1) c_s2_55150_2) c_s2_55150_3) c_s2_55150_4))
theorem cl9_55150 : S3ChkSq 55150 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s3_55150_0 c_s3_55150_1) c_s3_55150_2) c_s3_55150_3) c_s3_55150_4))
theorem cl11_55150 : (NoF2ChkSq 55150 ∧ NoF3zChkSq 55150 ∧ NoF4zChkSq 55150) :=
  ⟨f2Sq_of_P cf2z_55150 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f2_55150_0 c_f2_55150_1) c_f2_55150_2) c_f2_55150_3) c_f2_55150_4)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f3_55150_0 c_f3_55150_1) c_f3_55150_2) c_f3_55150_3) c_f3_55150_4)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f4_55150_0 c_f4_55150_1) c_f4_55150_2) c_f4_55150_3) c_f4_55150_4))⟩

theorem cnzETWD6_c55150 : CN'zETWD6 55150 :=
  ⟨cl1_55150, cl2_55150, cl3_55150, cl4_55150, cl5_55150, cl6_55150, cl7_55150, cl8_55150, cl9_55150, cl10_55150, cl11_55150, cl12_55150, cl13_55150, cl14_55150, cl15_55150⟩
theorem no_dissection_c55150 (D : CongruentDissection 55150) : False := not_tile_of_conditionsNSQzETWD6 55150 cnzETWD6_c55150 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c55150
