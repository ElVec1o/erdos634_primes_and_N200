/-
Draft/AllNExclusion.lean — one general theorem, quantified over every N:

    theorem not_tile_of_conditions (N : ℕ) (h : C N) (D : CongruentDissection N) : False

where `C N` is a conjunction of DECIDABLE bounded arithmetic checks on N (the leaves of `chain_gen3`, each discharged by an
N-uniform lemma from `AllNExclusionArith` / `AllNExclusionArith2` or by an already-N-free theorem):

  LeafSqf    Squarefree N
  LeafRange  7 ≤ N ∧ (17 ≤ N ∨ N ≡ 2 mod 4)        (the N-range of `Row2.theoremS_perm_sqfreeE` / `gapA_of_ellE`)
  LeafEll    a prime ℓ ≥ 7 divides N               (odd valuation, N squarefree)      — Case A (Lemma S route)
  LeafNSq    N is not a sum of two squares         — Case B and Case A similar exit
  LeafHAr    `HArith N`                            — Case A, Lemma H
  LeafR      N odd, or N even and N/2 not a sum of two squares  — right tile (`h1Right N` is a theorem for all N, `H1kFinal`)
  LeafE      N ≡ 2 (4), or (11 ≤ N and both equilateral pair tables (π/3, 2π/3))
  LeafF1     N ≡ 2 (4), or the F1 pair list
  LeafS2     global S2 check (A ∣ 4N)
  LeafS3     S3 / `IsoQRef` check
  LeafIso    `IsoH9b` check (2π/3 isosceles)
  LeafR8     NoF2 / NoF3 / NoF4z (F2–F4' shapes of the 2π/3 tile)
and free of any check:  S1 (`s1_arith_sqfree` + I6 for every squarefree N), γ = 2α (`caseG_of_squarefree`), and, for N ≡ 2 (4),
the equilateral / F1 parity leaves.

`C N` holds, by `decide +kernel` (no native_decide), at N = 14, 22, 35, 38, 39, 42, 46, 51, 55, 62, 66, 78, 86 (recovering the
per-N chains as instances of the one general theorem), at 57, 69, and at N not covered by any per-N chain: 91, 94, 95, 110,
133, 209, 217.  An exact search program evaluates `C` for all N ≤ 10000 (cross-validated against `leafVec` for N ≤ 150 in
`AllNExclusionCheck.lean`).  `C 21` (S3), `C 33` (IsoH9b), `C 15` (not in the squarefree range) and `C 70` (S3) are false.
No sorry, no native_decide.
-/
import Erdos634.Draft.AllNExclusionArith2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.AllNExclusion

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3

def LeafSqf (N : ℕ) : Prop := Squarefree N
def LeafRange (N : ℕ) : Prop := 7 ≤ N ∧ (17 ≤ N ∨ N % 4 = 2)
def LeafEll (N : ℕ) : Prop := EllChk N
def LeafNSq (N : ℕ) : Prop := NSqChk N
def LeafHAr (N : ℕ) : Prop := HArithChk N
def LeafR (N : ℕ) : Prop := N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChk N)
def LeafE (N : ℕ) : Prop := N % 4 = 2 ∨ (11 ≤ N ∧ Pairs60Chk N ∧ Pairs120Chk N)
def LeafF1 (N : ℕ) : Prop := N % 4 = 2 ∨ F1Chk N
def LeafS2 (N : ℕ) : Prop := S2Chk N
def LeafS3 (N : ℕ) : Prop := S3Chk N
def LeafIso (N : ℕ) : Prop := IsoH9bChk N
def LeafR8 (N : ℕ) : Prop := NoF2Chk N ∧ NoF3Chk N ∧ NoF4zChk N

/-- **The condition `C N`.** -/
def C (N : ℕ) : Prop :=
  LeafSqf N ∧ LeafRange N ∧ LeafEll N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafE N ∧ LeafF1 N ∧ LeafS2 N ∧
    LeafS3 N ∧ LeafIso N ∧ LeafR8 N

instance (N : ℕ) : Decidable (LeafSqf N) := by unfold LeafSqf; infer_instance
instance (N : ℕ) : Decidable (LeafRange N) := by unfold LeafRange; infer_instance
instance (N : ℕ) : Decidable (LeafEll N) := by unfold LeafEll; infer_instance
instance (N : ℕ) : Decidable (LeafNSq N) := by unfold LeafNSq; infer_instance
instance (N : ℕ) : Decidable (LeafHAr N) := by unfold LeafHAr; infer_instance
instance (N : ℕ) : Decidable (LeafR N) := by unfold LeafR; infer_instance
instance (N : ℕ) : Decidable (LeafE N) := by unfold LeafE; infer_instance
instance (N : ℕ) : Decidable (LeafF1 N) := by unfold LeafF1; infer_instance
instance (N : ℕ) : Decidable (LeafS2 N) := by unfold LeafS2; infer_instance
instance (N : ℕ) : Decidable (LeafS3 N) := by unfold LeafS3; infer_instance
instance (N : ℕ) : Decidable (LeafIso N) := by unfold LeafIso; infer_instance
instance (N : ℕ) : Decidable (LeafR8 N) := by unfold LeafR8; infer_instance
instance (N : ℕ) : Decidable (C N) := by unfold C; infer_instance

/-- S1 for every squarefree `N`: no arithmetic check is needed (`3q²−p² = 4N` is impossible for coprime `p, q`, mod 4). -/
theorem s1Closed_of_sqfree (N : ℕ) (hsq : Squarefree N) (hN0 : 0 < N) : S1Closed N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exact not_baseBetaTiled
    (Erdos634.Draft.CompositeFinal4.s1_baseBetaTiled_of_arith N
      (Erdos634.Draft.CompositeFinal12.s1_arith_sqfree N hsq hN0) D α β a b c r hα hrel hmod har hbr htgt)

/-- **ALLN-1.**  No `N` satisfying the decidable arithmetic conditions `C N` is a tile count. -/
theorem not_tile_of_conditions (N : ℕ) (h : C N) (D : CongruentDissection N) : False := by
  obtain ⟨hsq, ⟨h7, h17⟩, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, ⟨hF2c, hF3c, hF4c⟩⟩ := h
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk hsq hEll
  refine chain_gen3 N hsq (s1Closed_of_sqfree N hsq hN0)
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_isoQRef N (isoQRef_of_chk hN0 hS3))
    (isoH9b_of_chk hN0 hIso)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq h7 h17 hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq h7 h17) hns)
    ?_ (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree N hsq) ?_ ?_ ?_ (gapR8_of_chk hF2c hF3c hF4c) D
  · -- right tile
    rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hE with h4 | ⟨h11, h60, -⟩
    · exact gapE60_of_mod4_two N h4
    · exact gapE60_of_chk h11 h60
  · rcases hE with h4 | ⟨-, -, h120⟩
    · exact gapE120_of_mod4_two N h4
    · exact gapE120_of_chk hN0 h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chk (by omega) hf

/-- The leaf vector `[Sqf, Range, Ell, NSq, HAr, R, E, F1, S2, S3, Iso, R8]` of `C N` (used to cross-validate an
external transcription of `C N`). -/
def leafVec (N : ℕ) : List Bool :=
  [decide (LeafSqf N), decide (LeafRange N), decide (LeafEll N), decide (LeafNSq N), decide (LeafHAr N),
   decide (LeafR N), decide (LeafE N), decide (LeafF1 N), decide (LeafS2 N), decide (LeafS3 N),
   decide (LeafIso N), decide (LeafR8 N)]

/-! ## Instances: `C N` at the thirteen N of the per-N chains (14 … 86), by kernel evaluation -/

theorem C_14 : C 14 := by decide +kernel
theorem C_22 : C 22 := by decide +kernel
theorem C_35 : C 35 := by decide +kernel
theorem C_38 : C 38 := by decide +kernel
theorem C_39 : C 39 := by decide +kernel
theorem C_42 : C 42 := by decide +kernel
theorem C_46 : C 46 := by decide +kernel
theorem C_51 : C 51 := by decide +kernel
theorem C_55 : C 55 := by decide +kernel
theorem C_62 : C 62 := by decide +kernel
theorem C_66 : C 66 := by decide +kernel
theorem C_78 : C 78 := by decide +kernel
theorem C_86 : C 86 := by decide +kernel

theorem C_57 : C 57 := by decide +kernel
theorem C_69 : C 69 := by decide +kernel
/-- N ≡ 3 (4), composite, not among the per-N chains of the repository. -/
theorem C_91 : C 91 := by decide +kernel
theorem C_95 : C 95 := by decide +kernel
/-- N ≡ 1 (4), composite, not among the per-N chains. -/
theorem C_133 : C 133 := by decide +kernel
theorem C_209 : C 209 := by decide +kernel
theorem C_217 : C 217 := by decide +kernel
/-- N ≡ 2 (4) beyond the repository's chains. -/
theorem C_94 : C 94 := by decide +kernel
theorem C_110 : C 110 := by decide +kernel

theorem not_tile_57 (D : CongruentDissection 57) : False := not_tile_of_conditions 57 C_57 D
theorem not_tile_69 (D : CongruentDissection 69) : False := not_tile_of_conditions 69 C_69 D
theorem not_tile_91 (D : CongruentDissection 91) : False := not_tile_of_conditions 91 C_91 D
theorem not_tile_95 (D : CongruentDissection 95) : False := not_tile_of_conditions 95 C_95 D
theorem not_tile_133 (D : CongruentDissection 133) : False := not_tile_of_conditions 133 C_133 D
theorem not_tile_209 (D : CongruentDissection 209) : False := not_tile_of_conditions 209 C_209 D
theorem not_tile_217 (D : CongruentDissection 217) : False := not_tile_of_conditions 217 C_217 D
theorem not_tile_94 (D : CongruentDissection 94) : False := not_tile_of_conditions 94 C_94 D
theorem not_tile_110 (D : CongruentDissection 110) : False := not_tile_of_conditions 110 C_110 D
theorem not_tile_14 (D : CongruentDissection 14) : False := not_tile_of_conditions 14 C_14 D
theorem not_tile_22 (D : CongruentDissection 22) : False := not_tile_of_conditions 22 C_22 D
theorem not_tile_35 (D : CongruentDissection 35) : False := not_tile_of_conditions 35 C_35 D
theorem not_tile_38 (D : CongruentDissection 38) : False := not_tile_of_conditions 38 C_38 D
theorem not_tile_39 (D : CongruentDissection 39) : False := not_tile_of_conditions 39 C_39 D
theorem not_tile_42 (D : CongruentDissection 42) : False := not_tile_of_conditions 42 C_42 D
theorem not_tile_46 (D : CongruentDissection 46) : False := not_tile_of_conditions 46 C_46 D
theorem not_tile_51 (D : CongruentDissection 51) : False := not_tile_of_conditions 51 C_51 D
theorem not_tile_55 (D : CongruentDissection 55) : False := not_tile_of_conditions 55 C_55 D
theorem not_tile_62 (D : CongruentDissection 62) : False := not_tile_of_conditions 62 C_62 D
theorem not_tile_66 (D : CongruentDissection 66) : False := not_tile_of_conditions 66 C_66 D
theorem not_tile_78 (D : CongruentDissection 78) : False := not_tile_of_conditions 78 C_78 D
theorem not_tile_86 (D : CongruentDissection 86) : False := not_tile_of_conditions 86 C_86 D

/-! ## Negative controls (C is not trivially true) -/

/-- N = 21: the S3 leaf fails (base-α member `(2,3,4)` on `(12,12,21)`: `(e,d,m) = (1,1,1)`). -/
theorem not_C_21 : ¬ C 21 := by decide +kernel
/-- N = 33: the 2π/3-isosceles leaf fails (`(a,b,c) = (5,3,7)`). -/
theorem not_C_33 : ¬ C 33 := by decide +kernel
/-- N = 70: the S3 leaf fails. -/
theorem not_C_70 : ¬ C 70 := by decide +kernel
/-- N = 15: below the range of the Case-B / Case-A lemmas (and 15 is the separately-handled N). -/
theorem not_C_15 : ¬ C 15 := by decide +kernel
/-- N = 13 (prime, a sum of two squares): fails. -/
theorem not_C_13 : ¬ C 13 := by decide +kernel
/-- N = 18 (not squarefree): fails. -/
theorem not_C_18 : ¬ C 18 := by decide +kernel
/-- Leaf-level: S3 fails exactly at 21. -/
theorem leafS3_21_false : ¬ LeafS3 21 := by decide +kernel
theorem leafIso_33_false : ¬ LeafIso 33 := by decide +kernel
theorem leafS3_70_false : ¬ LeafS3 70 := by decide +kernel

/-- N = 87: the π/3 equilateral pair table fails at the pair `(29, 9)` (the `E60Pair 87 29 9` residual of `chain_87_final'`). -/
theorem leafE_87_false : ¬ LeafE 87 := by decide +kernel
/-- N = 105: pair tables, F1 list and R8 all fail. -/
theorem leafE_105_false : ¬ LeafE 105 := by decide +kernel
theorem leafF1_105_false : ¬ LeafF1 105 := by decide +kernel
theorem leafR8_105_false : ¬ LeafR8 105 := by decide +kernel
/-- N = 143: R8 fails (only). -/
theorem leafR8_143_false : ¬ LeafR8 143 := by decide +kernel
/-- N = 77: the global S2 check fails (a genuine arithmetic solution). -/
theorem leafS2_77_false : ¬ LeafS2 77 := by decide +kernel
/-- N = 26 = 2·13: right-tile leaf (N/2 = 13 = 2²+3²) and Case B (26 = 1²+5²) fail. -/
theorem leafR_26_false : ¬ LeafR 26 := by decide +kernel
theorem leafNSq_26_false : ¬ LeafNSq 26 := by decide +kernel
/-- N = 10: no prime ≥ 7 divides N. -/
theorem leafEll_10_false : ¬ LeafEll 10 := by decide +kernel
/-- N = 17 (prime, 17 = 1²+4²): Case B leaf fails. -/
theorem leafNSq_17_false : ¬ LeafNSq 17 := by decide +kernel

/-- Bridge from sqrt-bounded R8 sub-checks to LeafR8. -/
theorem leafR8_of_sq {N : ℕ} (h2 : NoF2ChkSq N) (h3 : NoF3ChkSq N) (h4 : NoF4zChkSq N) :
    LeafR8 N :=
  ⟨noF2Chk_of_sq h2, noF3Chk_of_sq h3, noF4zChk_of_sq h4⟩

/-- Bridges from sqrt-bounded leaf checks to their Leaf aliases. -/
theorem leafNSq_of_sq {N : ℕ} (h : NSqChkSq N) : LeafNSq N := nsqChk_of_sq h
theorem leafHAr_of_sq {N : ℕ} (h : HArithChkSq N) : LeafHAr N := hArithChk_of_sq h
theorem leafS2_of_sq {N : ℕ} (h : S2ChkSq N) : LeafS2 N := s2Chk_of_sq h
theorem leafS3_of_sq {N : ℕ} (h : S3ChkSq N) : LeafS3 N := s3Chk_of_sq h

end Erdos634.Draft.AllNExclusion

#print axioms Erdos634.Draft.AllNExclusion.not_tile_of_conditions
#print axioms Erdos634.Draft.AllNExclusion.s1Closed_of_sqfree
#print axioms Erdos634.Draft.AllNExclusion.C_14
#print axioms Erdos634.Draft.AllNExclusion.C_86
#print axioms Erdos634.Draft.AllNExclusion.not_tile_14
#print axioms Erdos634.Draft.AllNExclusion.not_tile_22
#print axioms Erdos634.Draft.AllNExclusion.not_tile_35
#print axioms Erdos634.Draft.AllNExclusion.not_tile_38
#print axioms Erdos634.Draft.AllNExclusion.not_tile_39
#print axioms Erdos634.Draft.AllNExclusion.not_tile_42
#print axioms Erdos634.Draft.AllNExclusion.not_tile_46
#print axioms Erdos634.Draft.AllNExclusion.not_tile_51
#print axioms Erdos634.Draft.AllNExclusion.not_tile_55
#print axioms Erdos634.Draft.AllNExclusion.not_tile_62
#print axioms Erdos634.Draft.AllNExclusion.not_tile_66
#print axioms Erdos634.Draft.AllNExclusion.not_tile_78
#print axioms Erdos634.Draft.AllNExclusion.not_tile_86
#print axioms Erdos634.Draft.AllNExclusion.not_C_21
#print axioms Erdos634.Draft.AllNExclusion.not_tile_133
#print axioms Erdos634.Draft.AllNExclusion.not_tile_110
#print axioms Erdos634.Draft.AllNExclusion.leafE_87_false
