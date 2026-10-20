/-
Draft/NSQWinC67484.lean -- `no_dissection_c67484` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 6 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_67484 : NQChkW 67484 := by decide +kernel
theorem cl2e_67484 : EllAt 67484 16871 := by decide +kernel
theorem cl2_67484 : (EllChk2 67484 ∨ AsqChk 67484) := Or.inl (ellChk2_of_at cl2e_67484)
theorem cl3_67484 : NSqChkSq 67484 := by decide +kernel
theorem cl4_67484 : HArithChkSq 67484 := by decide +kernel
theorem cl5_67484 : (67484 % 2 = 1 ∨ (67484 % 2 = 0 ∧ NHSqChkSq 67484)) := by decide +kernel
theorem cl6_67484 : LeafEsqW 67484 := by decide +kernel
theorem cl7_67484 : (67484 % 4 = 2 ∨ F1ChkParW 67484) := by decide +kernel
theorem cl10_67484 : IsoH9bChkW 67484 := by decide +kernel
theorem cl12_67484 : GammaChkDW 67484 := by decide +kernel
theorem cl13_67484 : S1t2ChkW 67484 := by decide +kernel
theorem cl14_67484 : RWChkT2W 67484 := by decide +kernel
theorem cl15_67484 : S5wChkW 67484 := by decide +kernel
theorem cf2z_67484 : F2z 67484 := by decide +kernel
theorem c_s2_67484_0 : ChunkP (S2P 67484) 0 212 := by decide +kernel
theorem c_s2_67484_1 : ChunkP (S2P 67484) 212 300 := by decide +kernel
theorem c_s2_67484_2 : ChunkP (S2P 67484) 300 368 := by decide +kernel
theorem c_s2_67484_3 : ChunkP (S2P 67484) 368 425 := by decide +kernel
theorem c_s2_67484_4 : ChunkP (S2P 67484) 425 475 := by decide +kernel
theorem c_s2_67484_5 : ChunkP (S2P 67484) 475 (Nat.sqrt (4 * 67484) + 1) := by decide +kernel
theorem c_s3_67484_0 : ChunkP (S3P 67484) 0 43 := by decide +kernel
theorem c_s3_67484_1 : ChunkP (S3P 67484) 43 87 := by decide +kernel
theorem c_s3_67484_2 : ChunkP (S3P 67484) 87 130 := by decide +kernel
theorem c_s3_67484_3 : ChunkP (S3P 67484) 130 173 := by decide +kernel
theorem c_s3_67484_4 : ChunkP (S3P 67484) 173 217 := by decide +kernel
theorem c_s3_67484_5 : ChunkP (S3P 67484) 217 (Nat.sqrt 67484 + 1) := by decide +kernel
theorem c_f4_67484_0 : ChunkP (F4zP 67484) 0 43 := by decide +kernel
theorem c_f4_67484_1 : ChunkP (F4zP 67484) 43 87 := by decide +kernel
theorem c_f4_67484_2 : ChunkP (F4zP 67484) 87 130 := by decide +kernel
theorem c_f4_67484_3 : ChunkP (F4zP 67484) 130 173 := by decide +kernel
theorem c_f4_67484_4 : ChunkP (F4zP 67484) 173 217 := by decide +kernel
theorem c_f4_67484_5 : ChunkP (F4zP 67484) 217 (Nat.sqrt 67484 + 1) := by decide +kernel
theorem c_f2_67484_0 : ChunkP (F2P 67484) 0 43 := by decide +kernel
theorem c_f2_67484_1 : ChunkP (F2P 67484) 43 87 := by decide +kernel
theorem c_f2_67484_2 : ChunkP (F2P 67484) 87 130 := by decide +kernel
theorem c_f2_67484_3 : ChunkP (F2P 67484) 130 173 := by decide +kernel
theorem c_f2_67484_4 : ChunkP (F2P 67484) 173 217 := by decide +kernel
theorem c_f2_67484_5 : ChunkP (F2P 67484) 217 (Nat.sqrt 67484 + 1) := by decide +kernel
theorem c_f3_67484_0 : ChunkP (F3zP 67484) 0 43 := by decide +kernel
theorem c_f3_67484_1 : ChunkP (F3zP 67484) 43 87 := by decide +kernel
theorem c_f3_67484_2 : ChunkP (F3zP 67484) 87 130 := by decide +kernel
theorem c_f3_67484_3 : ChunkP (F3zP 67484) 130 173 := by decide +kernel
theorem c_f3_67484_4 : ChunkP (F3zP 67484) 173 217 := by decide +kernel
theorem c_f3_67484_5 : ChunkP (F3zP 67484) 217 (Nat.sqrt 67484 + 1) := by decide +kernel

theorem cl8_67484 : S2ChkSq 67484 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_67484_0 c_s2_67484_1) c_s2_67484_2) c_s2_67484_3) c_s2_67484_4) c_s2_67484_5))
theorem cl9_67484 : S3ChkSq 67484 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_67484_0 c_s3_67484_1) c_s3_67484_2) c_s3_67484_3) c_s3_67484_4) c_s3_67484_5))
theorem cl11_67484 : (NoF2ChkSq 67484 ∧ NoF3zChkSq 67484 ∧ NoF4zChkSq 67484) :=
  ⟨f2Sq_of_P cf2z_67484 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_67484_0 c_f2_67484_1) c_f2_67484_2) c_f2_67484_3) c_f2_67484_4) c_f2_67484_5)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_67484_0 c_f3_67484_1) c_f3_67484_2) c_f3_67484_3) c_f3_67484_4) c_f3_67484_5)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_67484_0 c_f4_67484_1) c_f4_67484_2) c_f4_67484_3) c_f4_67484_4) c_f4_67484_5))⟩

theorem cnzETWD6_c67484 : CN'zETWD6 67484 :=
  ⟨cl1_67484, cl2_67484, cl3_67484, cl4_67484, cl5_67484, cl6_67484, cl7_67484, cl8_67484, cl9_67484, cl10_67484, cl11_67484, cl12_67484, cl13_67484, cl14_67484, cl15_67484⟩
theorem no_dissection_c67484 (D : CongruentDissection 67484) : False := not_tile_of_conditionsNSQzETWD6 67484 cnzETWD6_c67484 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c67484
