/-
Draft/NSQWinC75484.lean -- `no_dissection_c75484` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 7 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_75484 : NQChkW 75484 := by decide +kernel
theorem cl2w_75484 : EllOrAsqW 75484 := by decide +kernel
theorem cl2_75484 : (EllChk2 75484 ∨ AsqChk 75484) := ellAsq_of_W cl2w_75484
theorem cl3_75484 : NSqChkSq 75484 := by decide +kernel
theorem cl4_75484 : HArithChkSq 75484 := by decide +kernel
theorem cl5_75484 : (75484 % 2 = 1 ∨ (75484 % 2 = 0 ∧ NHSqChkSq 75484)) := by decide +kernel
theorem cl6_75484 : LeafEsqW 75484 := by decide +kernel
theorem cl7_75484 : (75484 % 4 = 2 ∨ F1ChkParW 75484) := by decide +kernel
theorem cl10_75484 : IsoH9bChkW 75484 := by decide +kernel
theorem cl12_75484 : GammaChkDW 75484 := by decide +kernel
theorem cl13_75484 : S1t2ChkW 75484 := by decide +kernel
theorem cl14_75484 : RWChkT2W 75484 := by decide +kernel
theorem cl15_75484 : S5wChkW 75484 := by decide +kernel
theorem cf2z_75484 : F2z 75484 := by decide +kernel
theorem c_s2_75484_0 : ChunkP (S2P 75484) 0 208 := by decide +kernel
theorem c_s2_75484_1 : ChunkP (S2P 75484) 208 294 := by decide +kernel
theorem c_s2_75484_2 : ChunkP (S2P 75484) 294 360 := by decide +kernel
theorem c_s2_75484_3 : ChunkP (S2P 75484) 360 416 := by decide +kernel
theorem c_s2_75484_4 : ChunkP (S2P 75484) 416 465 := by decide +kernel
theorem c_s2_75484_5 : ChunkP (S2P 75484) 465 509 := by decide +kernel
theorem c_s2_75484_6 : ChunkP (S2P 75484) 509 (Nat.sqrt (4 * 75484) + 1) := by decide +kernel
theorem c_s3_75484_0 : ChunkP (S3P 75484) 0 39 := by decide +kernel
theorem c_s3_75484_1 : ChunkP (S3P 75484) 39 79 := by decide +kernel
theorem c_s3_75484_2 : ChunkP (S3P 75484) 79 118 := by decide +kernel
theorem c_s3_75484_3 : ChunkP (S3P 75484) 118 157 := by decide +kernel
theorem c_s3_75484_4 : ChunkP (S3P 75484) 157 196 := by decide +kernel
theorem c_s3_75484_5 : ChunkP (S3P 75484) 196 236 := by decide +kernel
theorem c_s3_75484_6 : ChunkP (S3P 75484) 236 (Nat.sqrt 75484 + 1) := by decide +kernel
theorem c_f4_75484_0 : ChunkP (F4zP 75484) 0 39 := by decide +kernel
theorem c_f4_75484_1 : ChunkP (F4zP 75484) 39 79 := by decide +kernel
theorem c_f4_75484_2 : ChunkP (F4zP 75484) 79 118 := by decide +kernel
theorem c_f4_75484_3 : ChunkP (F4zP 75484) 118 157 := by decide +kernel
theorem c_f4_75484_4 : ChunkP (F4zP 75484) 157 196 := by decide +kernel
theorem c_f4_75484_5 : ChunkP (F4zP 75484) 196 236 := by decide +kernel
theorem c_f4_75484_6 : ChunkP (F4zP 75484) 236 (Nat.sqrt 75484 + 1) := by decide +kernel
theorem c_f2_75484_0 : ChunkP (F2P 75484) 0 39 := by decide +kernel
theorem c_f2_75484_1 : ChunkP (F2P 75484) 39 79 := by decide +kernel
theorem c_f2_75484_2 : ChunkP (F2P 75484) 79 118 := by decide +kernel
theorem c_f2_75484_3 : ChunkP (F2P 75484) 118 157 := by decide +kernel
theorem c_f2_75484_4 : ChunkP (F2P 75484) 157 196 := by decide +kernel
theorem c_f2_75484_5 : ChunkP (F2P 75484) 196 236 := by decide +kernel
theorem c_f2_75484_6 : ChunkP (F2P 75484) 236 (Nat.sqrt 75484 + 1) := by decide +kernel
theorem c_f3_75484_0 : ChunkP (F3zP 75484) 0 39 := by decide +kernel
theorem c_f3_75484_1 : ChunkP (F3zP 75484) 39 79 := by decide +kernel
theorem c_f3_75484_2 : ChunkP (F3zP 75484) 79 118 := by decide +kernel
theorem c_f3_75484_3 : ChunkP (F3zP 75484) 118 157 := by decide +kernel
theorem c_f3_75484_4 : ChunkP (F3zP 75484) 157 196 := by decide +kernel
theorem c_f3_75484_5 : ChunkP (F3zP 75484) 196 236 := by decide +kernel
theorem c_f3_75484_6 : ChunkP (F3zP 75484) 236 (Nat.sqrt 75484 + 1) := by decide +kernel

theorem cl8_75484 : S2ChkSq 75484 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_75484_0 c_s2_75484_1) c_s2_75484_2) c_s2_75484_3) c_s2_75484_4) c_s2_75484_5) c_s2_75484_6))
theorem cl9_75484 : S3ChkSq 75484 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_75484_0 c_s3_75484_1) c_s3_75484_2) c_s3_75484_3) c_s3_75484_4) c_s3_75484_5) c_s3_75484_6))
theorem cl11_75484 : (NoF2ChkSq 75484 ∧ NoF3zChkSq 75484 ∧ NoF4zChkSq 75484) :=
  ⟨f2Sq_of_P cf2z_75484 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_75484_0 c_f2_75484_1) c_f2_75484_2) c_f2_75484_3) c_f2_75484_4) c_f2_75484_5) c_f2_75484_6)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_75484_0 c_f3_75484_1) c_f3_75484_2) c_f3_75484_3) c_f3_75484_4) c_f3_75484_5) c_f3_75484_6)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_75484_0 c_f4_75484_1) c_f4_75484_2) c_f4_75484_3) c_f4_75484_4) c_f4_75484_5) c_f4_75484_6))⟩

theorem cnzETWD6_c75484 : CN'zETWD6 75484 :=
  ⟨cl1_75484, cl2_75484, cl3_75484, cl4_75484, cl5_75484, cl6_75484, cl7_75484, cl8_75484, cl9_75484, cl10_75484, cl11_75484, cl12_75484, cl13_75484, cl14_75484, cl15_75484⟩
theorem no_dissection_c75484 (D : CongruentDissection 75484) : False := not_tile_of_conditionsNSQzETWD6 75484 cnzETWD6_c75484 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c75484
