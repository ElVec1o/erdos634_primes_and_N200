/-
Draft/N105.lean -- `N = 105` is NOT a tile count.

`105 = 3 · 5 · 7` is squarefree; every leaf of the squarefree chain holds by kernel-checked arithmetic except
* the equilateral `π/3` leaf, `Eq105.gapE60_105` (two certificates, `thm:eq105`), and
* the `F₁` leaf.  The pairs `(Ma, Mb)`, `1 < Ma < Mb`, `Ma Mb = 105`, are
  `(7, 15)`: discriminant `22² + 12 · 105 = 1744`, not a square (`F1PairCert.f1Pair_of_arith`);
  `(5, 21)`: tile `(8, 7, 13)` on the target `(56, 91, 105)`, certificate `Refl.MF105A.not_dissection` (61,083 nodes);
  `(3, 35)`: tile `(16, 5, 19)` on the target `(80, 95, 105)`, certificate `Refl.MF105B.not_dissection` (46,600 nodes).

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.Eq105
import Erdos634.Draft.F1PairCert
import Erdos634.Refl.MF105ASound
import Erdos634.Refl.MF105BSound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N105

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.CompositeFinal4 Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso
open Erdos634.Draft.CompositeE5Gen Erdos634.Draft.E60Cert Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.R8ZF
open Erdos634.Draft.CompositeF1Gen Erdos634.Draft.F1PairCert

theorem TGT_A : dist (Refl.MF105A.TGT.pts 0) (Refl.MF105A.TGT.pts 1) = 105 ∧
    dist (Refl.MF105A.TGT.pts 1) (Refl.MF105A.TGT.pts 2) = 56 ∧
    dist (Refl.MF105A.TGT.pts 0) (Refl.MF105A.TGT.pts 2) = 91 :=
  model_sides_rp Refl.MF105A.hDn Refl.MF105A.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT_B : dist (Refl.MF105B.TGT.pts 0) (Refl.MF105B.TGT.pts 1) = 105 ∧
    dist (Refl.MF105B.TGT.pts 1) (Refl.MF105B.TGT.pts 2) = 80 ∧
    dist (Refl.MF105B.TGT.pts 0) (Refl.MF105B.TGT.pts 2) = 95 :=
  model_sides_rp Refl.MF105B.hDn Refl.MF105B.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(5, 21)`: tile `(8, 7, 13)`, target `(56, 91, 105)` -/
theorem f1pair_5_21 : F1Pair 105 5 21 := by
  obtain ⟨g1, g2, g3⟩ := TGT_A
  obtain ⟨k1, k2, k3⟩ := Refl.MF105A.MODEL_sides
  exact f1Pair_of_cert 105 5 21 (by norm_num) 8 7 13 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MF105A.TGT Refl.MF105A.MODEL
    (fun T h => congruent_of_hasSides' h (by rw [g1]; norm_num) (by rw [g2]; norm_num) (by rw [g3]; norm_num))
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MF105A.not_dissection D' hT hM)

/-- the pair `(3, 35)`: tile `(16, 5, 19)`, target `(80, 95, 105)` -/
theorem f1pair_3_35 : F1Pair 105 3 35 := by
  obtain ⟨g1, g2, g3⟩ := TGT_B
  obtain ⟨k1, k2, k3⟩ := Refl.MF105B.MODEL_sides
  exact f1Pair_of_cert 105 3 35 (by norm_num) 16 5 19 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Refl.MF105B.TGT Refl.MF105B.MODEL
    (fun T h => congruent_of_hasSides' h (by rw [g1]; norm_num) (by rw [g2]; norm_num) (by rw [g3]; norm_num))
    (fun T h => congruent_of_hasSides' (hasSides_rot h) k1 k2 k3)
    (fun D' hT hM => Refl.MF105B.not_dissection D' hT hM)

/-- the pair `(7, 15)`: `κ = 4`, discriminant `1744` -/
theorem f1pair_7_15 : F1Pair 105 7 15 :=
  f1Pair_of_arith 105 7 15 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num)

/-- **`GapF1 105`.** -/
theorem gapF1_105 : GapF1 105 := by
  refine gapF1_of_MaGt1 105 (by norm_num) (f1MaGt1_of_pairs 105 ?_)
  intro Ma Mb h1 hlt hp
  have hMa : Ma ≤ 10 := by nlinarith
  have key : (Ma = 3 ∧ Mb = 35) ∨ (Ma = 5 ∧ Mb = 21) ∨ (Ma = 7 ∧ Mb = 15) := by
    interval_cases Ma <;> omega
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact f1pair_3_35
  · exact f1pair_5_21
  · exact f1pair_7_15

/-- **`105` is not a tile count** (no `CongruentDissection 105` exists). -/
theorem not_tile_105 (D : CongruentDissection 105) : False :=
  not_tile_sqf_full 105 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (s3Closed_of_isoQRef 105 (isoQRef_of_chk (by norm_num) (by decide +kernel)))
    (isoClosed_of_chk (by norm_num) (by decide +kernel))
    Erdos634.Draft.Eq105.gapE60_105 (gapE120_of_chk (by norm_num) (by decide +kernel)) gapF1_105
    (gapR8_of_chk_z (by decide +kernel) (by decide +kernel) (by decide +kernel)) D

end Erdos634.Draft.N105

#print axioms Erdos634.Draft.N105.not_tile_105
