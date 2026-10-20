/-
Draft/NSQWinC59932.lean -- `no_dissection_c59932` via the windowed chain `CN'zETWD6` (`NSQWin3`) with the double-loop leaves S2, S3, F2, F3z, F4z CHUNKED
(`NSQWin4`, 5 chunk(s) each) and every leaf in its own kernel declaration.  Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin4

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem cl1_59932 : NQChkW 59932 := by decide +kernel
theorem cl2e_59932 : EllAt 59932 14983 := by decide +kernel
theorem cl2_59932 : (EllChk2 59932 ∨ AsqChk 59932) := Or.inl (ellChk2_of_at cl2e_59932)
theorem cl3_59932 : NSqChkSq 59932 := by decide +kernel
theorem cl4_59932 : HArithChkSq 59932 := by decide +kernel
theorem cl5_59932 : (59932 % 2 = 1 ∨ (59932 % 2 = 0 ∧ NHSqChkSq 59932)) := by decide +kernel
theorem cl6_59932 : LeafEsqW 59932 := by decide +kernel
theorem cl7_59932 : (59932 % 4 = 2 ∨ F1ChkParW 59932) := by decide +kernel
theorem cl10_59932 : IsoH9bChkW 59932 := by decide +kernel
theorem cl12_59932 : GammaChkDW 59932 := by decide +kernel
theorem cl13_59932 : S1t2ChkW 59932 := by decide +kernel
theorem cl14_59932 : RWChkT2W 59932 := by decide +kernel
theorem cl15_59932 : S5wChkW 59932 := by decide +kernel
theorem cf2z_59932 : F2z 59932 := by decide +kernel
theorem c_s2_59932_0 : ChunkP (S2P 59932) 0 219 := by decide +kernel
theorem c_s2_59932_1 : ChunkP (S2P 59932) 219 310 := by decide +kernel
theorem c_s2_59932_2 : ChunkP (S2P 59932) 310 380 := by decide +kernel
theorem c_s2_59932_3 : ChunkP (S2P 59932) 380 438 := by decide +kernel
theorem c_s2_59932_4 : ChunkP (S2P 59932) 438 (Nat.sqrt (4 * 59932) + 1) := by decide +kernel
theorem c_s3_59932_0 : ChunkP (S3P 59932) 0 49 := by decide +kernel
theorem c_s3_59932_1 : ChunkP (S3P 59932) 49 98 := by decide +kernel
theorem c_s3_59932_2 : ChunkP (S3P 59932) 98 147 := by decide +kernel
theorem c_s3_59932_3 : ChunkP (S3P 59932) 147 196 := by decide +kernel
theorem c_s3_59932_4 : ChunkP (S3P 59932) 196 (Nat.sqrt 59932 + 1) := by decide +kernel
theorem c_f4_59932_0 : ChunkP (F4zP 59932) 0 49 := by decide +kernel
theorem c_f4_59932_1 : ChunkP (F4zP 59932) 49 98 := by decide +kernel
theorem c_f4_59932_2 : ChunkP (F4zP 59932) 98 147 := by decide +kernel
theorem c_f4_59932_3 : ChunkP (F4zP 59932) 147 196 := by decide +kernel
theorem c_f4_59932_4 : ChunkP (F4zP 59932) 196 (Nat.sqrt 59932 + 1) := by decide +kernel
theorem c_f2_59932_0 : ChunkP (F2P 59932) 0 49 := by decide +kernel
theorem c_f2_59932_1 : ChunkP (F2P 59932) 49 98 := by decide +kernel
theorem c_f2_59932_2 : ChunkP (F2P 59932) 98 147 := by decide +kernel
theorem c_f2_59932_3 : ChunkP (F2P 59932) 147 196 := by decide +kernel
theorem c_f2_59932_4 : ChunkP (F2P 59932) 196 (Nat.sqrt 59932 + 1) := by decide +kernel
theorem c_f3_59932_0 : ChunkP (F3zP 59932) 0 49 := by decide +kernel
theorem c_f3_59932_1 : ChunkP (F3zP 59932) 49 98 := by decide +kernel
theorem c_f3_59932_2 : ChunkP (F3zP 59932) 98 147 := by decide +kernel
theorem c_f3_59932_3 : ChunkP (F3zP 59932) 147 196 := by decide +kernel
theorem c_f3_59932_4 : ChunkP (F3zP 59932) 196 (Nat.sqrt 59932 + 1) := by decide +kernel

theorem cl8_59932 : S2ChkSq 59932 := s2Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s2_59932_0 c_s2_59932_1) c_s2_59932_2) c_s2_59932_3) c_s2_59932_4))
theorem cl9_59932 : S3ChkSq 59932 := s3Sq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_s3_59932_0 c_s3_59932_1) c_s3_59932_2) c_s3_59932_3) c_s3_59932_4))
theorem cl11_59932 : (NoF2ChkSq 59932 ∧ NoF3zChkSq 59932 ∧ NoF4zChkSq 59932) :=
  ⟨f2Sq_of_P cf2z_59932 (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f2_59932_0 c_f2_59932_1) c_f2_59932_2) c_f2_59932_3) c_f2_59932_4)), f3zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f3_59932_0 c_f3_59932_1) c_f3_59932_2) c_f3_59932_3) c_f3_59932_4)), f4zSq_of_P (chunk_full (chunk_append (chunk_append (chunk_append (chunk_append c_f4_59932_0 c_f4_59932_1) c_f4_59932_2) c_f4_59932_3) c_f4_59932_4))⟩

theorem cnzETWD6_c59932 : CN'zETWD6 59932 :=
  ⟨cl1_59932, cl2_59932, cl3_59932, cl4_59932, cl5_59932, cl6_59932, cl7_59932, cl8_59932, cl9_59932, cl10_59932, cl11_59932, cl12_59932, cl13_59932, cl14_59932, cl15_59932⟩
theorem no_dissection_c59932 (D : CongruentDissection 59932) : False := not_tile_of_conditionsNSQzETWD6 59932 cnzETWD6_c59932 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_c59932
