/-
Draft/NSQWinC83932.lean -- `no_dissection_c83932` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 7 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_83932 : NQChkW 83932 := by decide +kernel
theorem cl2e_83932 : EllAt 83932 20983 := by decide +kernel
theorem cl2_83932 : (EllChk2 83932 ∨ AsqChk 83932) := Or.inl (ellChk2_of_at cl2e_83932)
theorem cl3_83932 : NSqChkSq 83932 := by decide +kernel
theorem cl4_83932 : HArithChkSq 83932 := by decide +kernel
theorem cl5_83932 : (83932 % 2 = 1 ∨ (83932 % 2 = 0 ∧ NHSqChkSq 83932)) := by decide +kernel
theorem cl6_83932 : LeafEsqW 83932 := by decide +kernel
theorem cl7_83932 : (83932 % 4 = 2 ∨ F1ChkParW 83932) := by decide +kernel
theorem cl10_83932 : IsoH9bChkW 83932 := by decide +kernel
theorem cl12_83932 : GammaChkDW 83932 := by decide +kernel
theorem cl13_83932 : S1t2ChkW 83932 := by decide +kernel
theorem cl14_83932 : RWChkT2W 83932 := by decide +kernel
theorem cl15_83932 : S5wChkW 83932 := by decide +kernel
theorem cf2z_83932 : F2z 83932 := by decide +kernel
theorem c_s2_83932_0 : ChunkP (S2P 83932) 0 219 := by decide +kernel
theorem c_s2_83932_1 : ChunkP (S2P 83932) 219 310 := by decide +kernel
theorem c_s2_83932_2 : ChunkP (S2P 83932) 310 380 := by decide +kernel
theorem c_s2_83932_3 : ChunkP (S2P 83932) 380 438 := by decide +kernel
theorem c_s2_83932_4 : ChunkP (S2P 83932) 438 490 := by decide +kernel
theorem c_s2_83932_5 : ChunkP (S2P 83932) 490 537 := by decide +kernel
theorem c_s2_83932_6 : ChunkP (S2P 83932) 537 (Nat.sqrt (4 * 83932) + 1) := by decide +kernel
theorem c_s3_83932_0 : ChunkP (S3P 83932) 0 41 := by decide +kernel
theorem c_s3_83932_1 : ChunkP (S3P 83932) 41 83 := by decide +kernel
theorem c_s3_83932_2 : ChunkP (S3P 83932) 83 124 := by decide +kernel
theorem c_s3_83932_3 : ChunkP (S3P 83932) 124 166 := by decide +kernel
theorem c_s3_83932_4 : ChunkP (S3P 83932) 166 207 := by decide +kernel
theorem c_s3_83932_5 : ChunkP (S3P 83932) 207 249 := by decide +kernel
theorem c_s3_83932_6 : ChunkP (S3P 83932) 249 (Nat.sqrt 83932 + 1) := by decide +kernel
theorem c_f4_83932_0 : ChunkP (F4zP 83932) 0 41 := by decide +kernel
theorem c_f4_83932_1 : ChunkP (F4zP 83932) 41 83 := by decide +kernel
theorem c_f4_83932_2 : ChunkP (F4zP 83932) 83 124 := by decide +kernel
theorem c_f4_83932_3 : ChunkP (F4zP 83932) 124 166 := by decide +kernel
theorem c_f4_83932_4 : ChunkP (F4zP 83932) 166 207 := by decide +kernel
theorem c_f4_83932_5 : ChunkP (F4zP 83932) 207 249 := by decide +kernel
theorem c_f4_83932_6 : ChunkP (F4zP 83932) 249 (Nat.sqrt 83932 + 1) := by decide +kernel
theorem c_f2_83932_0 : ChunkP (F2P 83932) 0 41 := by decide +kernel
theorem c_f2_83932_1 : ChunkP (F2P 83932) 41 83 := by decide +kernel
theorem c_f2_83932_2 : ChunkP (F2P 83932) 83 124 := by decide +kernel
theorem c_f2_83932_3 : ChunkP (F2P 83932) 124 166 := by decide +kernel
theorem c_f2_83932_4 : ChunkP (F2P 83932) 166 207 := by decide +kernel
theorem c_f2_83932_5 : ChunkP (F2P 83932) 207 249 := by decide +kernel
theorem c_f2_83932_6 : ChunkP (F2P 83932) 249 (Nat.sqrt 83932 + 1) := by decide +kernel
theorem c_f3_83932_0 : ChunkP (F3zP 83932) 0 41 := by decide +kernel
theorem c_f3_83932_1 : ChunkP (F3zP 83932) 41 83 := by decide +kernel
theorem c_f3_83932_2 : ChunkP (F3zP 83932) 83 124 := by decide +kernel
theorem c_f3_83932_3 : ChunkP (F3zP 83932) 124 166 := by decide +kernel
theorem c_f3_83932_4 : ChunkP (F3zP 83932) 166 207 := by decide +kernel
theorem c_f3_83932_5 : ChunkP (F3zP 83932) 207 249 := by decide +kernel
theorem c_f3_83932_6 : ChunkP (F3zP 83932) 249 (Nat.sqrt 83932 + 1) := by decide +kernel

theorem cl8_83932 : S2ChkSq 83932 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s2_83932_0 c_s2_83932_1) c_s2_83932_2) c_s2_83932_3) c_s2_83932_4) c_s2_83932_5) c_s2_83932_6))
theorem cl9_83932 : S3ChkSq 83932 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_s3_83932_0 c_s3_83932_1) c_s3_83932_2) c_s3_83932_3) c_s3_83932_4) c_s3_83932_5) c_s3_83932_6))
theorem cl11_83932 : (NoF2ChkSq 83932 ∧ NoF3zChkSq 83932 ∧ NoF4zChkSq 83932) :=
  ⟨f2Sq_of_P cf2z_83932 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f2_83932_0 c_f2_83932_1) c_f2_83932_2) c_f2_83932_3) c_f2_83932_4) c_f2_83932_5) c_f2_83932_6)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f3_83932_0 c_f3_83932_1) c_f3_83932_2) c_f3_83932_3) c_f3_83932_4) c_f3_83932_5) c_f3_83932_6)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append (chunk_append c_f4_83932_0 c_f4_83932_1) c_f4_83932_2) c_f4_83932_3) c_f4_83932_4) c_f4_83932_5) c_f4_83932_6))⟩

theorem cnzETWD6_c83932 : CN'zETWD6 83932 :=
  ⟨cl1_83932, cl2_83932, cl3_83932, cl4_83932, cl5_83932, cl6_83932, cl7_83932, cl8_83932, cl9_83932, cl10_83932, cl11_83932, cl12_83932, cl13_83932, cl14_83932, cl15_83932⟩
theorem no_dissection_c83932 (D : CongruentDissection 83932) : False := not_tile_of_conditionsNSQzETWD6 83932 cnzETWD6_c83932 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c83932
