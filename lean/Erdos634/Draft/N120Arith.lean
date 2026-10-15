/-
Draft/N120Arith.lean -- the leaves of `N = 120` that are closed by kernel-checked arithmetic.

`120 = 2³ · 3 · 5`.  Every leaf of the non-squarefree chain except three holds by arithmetic:
the Case A leaf (`GAUFinal.gapA_120`), the equilateral `π/3` leaf (`E60N120.gapE60_120`, one certificate) and the pair
`(Ma, Mb) = (6, 20)` of the `F₁` leaf (one certificate) are supplied in `Draft/N120.lean`.
The `F₁` pairs of the right parity are `(2, 60)`, `(4, 30)`, `(10, 12)` (non-square discriminants `5284`, `2596`,
`1924`) and `(6, 20)` (discriminant `2116 = 46²`: tile `(7, 8, 13)`, target `(56, 104, 120)`).

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.ChainGapA
import Erdos634.Draft.F1PairPar

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N120

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF
open Erdos634.Draft.F1PairCert

theorem s1_120 : S1Closed 120 := s1Closed_of_free 120 (s1Free_of_chk (by decide +kernel))

theorem s3_120 : S3Closed 120 := s3Closed_of_isoQRef 120 (isoQRef_of_chk (by norm_num) (by decide +kernel))

theorem iso_120 : IsoClosed 120 := isoClosed_of_chk (by norm_num) (by decide +kernel)

theorem s4_120 : RWStatementNsq 120 := rwStatement_nsq 120 (rwFree_of_chk (by decide +kernel))

theorem s5_120 : RAStatementNsq 120 := raStatement_nsqM 120 (s5pFree_of_chk (by decide +kernel))

theorem g_120 : CaseGClosed 120 := caseG_of_gammaArith 120 (gammaArith_of_chk (by decide +kernel))

theorem e120_120 : GapE120 120 := gapE120_of_chk (by norm_num) (by decide +kernel)

theorem r8_120 : GapR8 120 := gapR8_of_chk_z (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`GapF1 120` from the pair `(6, 20)`.** -/
theorem gapF1_120_of_pair (h : F1Pair 120 6 20) : GapF1 120 := by
  refine Erdos634.Draft.NSQF1.gapF1_of_MaGt1par 120 (by norm_num) (f1MaGt1par_of_pairs 120 ?_)
  intro Ma Mb h1 hlt hp hpa hpb
  have hMa : Ma ≤ 10 := by nlinarith
  have key : (Ma = 2 ∧ Mb = 60) ∨ (Ma = 4 ∧ Mb = 30) ∨ (Ma = 6 ∧ Mb = 20) ∨ (Ma = 10 ∧ Mb = 12) := by
    interval_cases Ma <;> omega
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact f1Pair_of_arith 120 2 60 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by norm_num)
  · exact f1Pair_of_arith 120 4 30 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by norm_num)
  · exact h
  · exact f1Pair_of_arith 120 10 12 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by norm_num)

/-- **`120` is not a tile count, given the three non-arithmetic leaves.** -/
theorem not_tile_120_of (gA : GapA 120) (gE60 : GapE60 120) (hF : F1Pair 120 6 20)
    (D : CongruentDissection 120) : False :=
  Erdos634.Draft.ChainGapA.not_tile_nsq_gapA 120 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) s1_120 s3_120 iso_120 s4_120 s5_120 g_120 gA gE60 e120_120 (gapF1_120_of_pair hF) r8_120 D

end Erdos634.Draft.N120

#print axioms Erdos634.Draft.N120.not_tile_120_of
