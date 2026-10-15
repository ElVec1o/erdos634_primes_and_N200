/-
Draft/AllN3Cond.lean -- the condition `C3 N` on a squarefree `N`: the condition `R8ZF.C'' N` with two
leaves weakened.

* The `π/3` pair table `Pairs60Chk'` is replaced by `E60Irr.Pairs60ChkSq N []`: every pair is the pin, of the wrong
  parity, or has a non-square discriminant `(m₁ + m₂)² − 16N`.  A pair with a non-square discriminant is excluded for
  every `N` by `E60Irr.e60Pair_of_not_isSquare` (the degree count; Laczkovich's theorem for the angle `π/3`), so the
  side-word condition of `Pairs60Chk'` is not needed.
* The base-`α` check `S3Chk` is replaced by `S3ChkD`: a solution `(e, d, m)` of the reduced equation
  `N d = m² (2e + d)(e² + 4ed + 2d²)` counts only if `d ∣ m` (`Sqfree3Mod8.s3inst_of_not_dvd`, from
  `BADL2.theoremA_L2_full`).

    theorem not_tile_of_conditions3 (N : ℕ) (h : C3 N) (D : CongruentDissection N) : False

`R8ZF.C'' N → C3 N` (`c3_of_c''`): nothing is lost.

Coverage, computed by an exact search program (a transcription of the predicates, not checked value by value by the
kernel): of the 60,789 squarefree `N` in `[7, 10⁵]`, 13,600 are sums of two squares (tile counts), `C'` holds for
39,651, `C''` for 41,054 and `C3` for 46,898; 291 satisfy none of them.  The 18 values `≤ 1000` gained over `C''` are
kernel-checked in `Draft/AllN3Check1.lean`.

No sorry, no native_decide.
-/
import Erdos634.Draft.R8ZFLeaf
import Erdos634.Draft.E60Irr
import Erdos634.Draft.Sqfree3Mod8

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.AllN3

open Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.R8ZF Erdos634.Draft.E60Irr

/-- the equilateral leaf with the discriminant table for the `π/3` pairs -/
def LeafEsq (N : ℕ) : Prop := N % 4 = 2 ∨ (11 ≤ N ∧ Pairs60ChkSq N [] ∧ Pairs120Chk N)

/-- the base-`α` check with the divisibility `d ∣ m` -/
def S3ChkD (N : ℕ) : Prop :=
  ∀ e ≤ N, 1 ≤ e → e * e ≤ N → ∀ d ≤ N, 1 ≤ d → 2 * (d * d) ≤ N → qQ e d ∣ N →
    ¬ (kK e d ∣ N * d ∧ Nat.sqrt (N * d / kK e d) * Nat.sqrt (N * d / kK e d) = N * d / kK e d ∧
      d ∣ Nat.sqrt (N * d / kK e d))

/-- **The condition `C3 N`.** -/
def C3 (N : ℕ) : Prop :=
  LeafSqf N ∧ LeafRange N ∧ LeafEll N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafEsq N ∧ LeafF1 N ∧ LeafS2 N ∧
    S3ChkD N ∧ LeafIso N ∧ LeafR8z N

instance (N : ℕ) : Decidable (LeafEsq N) := by unfold LeafEsq; infer_instance
instance (N : ℕ) : Decidable (S3ChkD N) := by unfold S3ChkD qQ kK; infer_instance
instance (N : ℕ) : Decidable (C3 N) := by unfold C3; infer_instance

theorem s3ChkD_of_s3Chk {N : ℕ} (h : S3Chk N) : S3ChkD N :=
  fun e he h1 h2 d hd h3 h4 hQ hc => h e he h1 h2 d hd h3 h4 hQ ⟨hc.1, hc.2.1⟩

/-! ## Square-root-bounded forms of the two nested checks (small terms for `decide +kernel`) -/

/-- `S3ChkD` with both loops bounded by square roots -/
def S3ChkDSq (N : ℕ) : Prop :=
  ∀ e ≤ Nat.sqrt N, 1 ≤ e → e * e ≤ N →
  ∀ d ≤ Nat.sqrt (N / 2), 1 ≤ d → 2 * (d * d) ≤ N → qQ e d ∣ N →
    ¬ (kK e d ∣ N * d ∧ Nat.sqrt (N * d / kK e d) * Nat.sqrt (N * d / kK e d) = N * d / kK e d ∧
      d ∣ Nat.sqrt (N * d / kK e d))

instance (N : ℕ) : Decidable (S3ChkDSq N) := by unfold S3ChkDSq qQ kK; infer_instance

theorem s3ChkD_of_sq {N : ℕ} (h : S3ChkDSq N) : S3ChkD N :=
  fun e _ he1 he2 d _ hd1 hd2 hQ =>
    h e (Nat.le_sqrt.mpr he2) he1 he2
      d (Nat.le_sqrt.mpr ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith))) hd1 hd2 hQ

/-- `NoF3zChk` with both loops bounded by square roots -/
def NoF3zChkSq (N : ℕ) : Prop :=
  ∀ j ≤ Nat.sqrt N, 0 < j → j * j ≤ N → ∀ s ≤ Nat.sqrt (2 * N), j < s → s * s ≤ 2 * N →
    4 * N = 3 * (s + j) * (s + 3 * j) →
    ¬ ((s * s + 3 * (j * j)) % 4 = 0 ∧
        Nat.sqrt ((s * s + 3 * (j * j)) / 4) * Nat.sqrt ((s * s + 3 * (j * j)) / 4) =
          (s * s + 3 * (j * j)) / 4)

instance (N : ℕ) : Decidable (NoF3zChkSq N) := by unfold NoF3zChkSq; infer_instance

theorem noF3zChk_of_sq {N : ℕ} (h : NoF3zChkSq N) : NoF3zChk N :=
  fun j _ hj hjsq s _ hjs hssq heq =>
    h j (Nat.le_sqrt.mpr hjsq) hj hjsq s (Nat.le_sqrt.mpr hssq) hjs hssq heq

theorem leafR8z_of_sq {N : ℕ} (h2 : NoF2ChkSq N) (h3 : NoF3zChkSq N) (h4 : NoF4zChkSq N) : LeafR8z N :=
  ⟨noF2Chk_of_sq h2, noF3zChk_of_sq h3, noF4zChk_of_sq h4⟩

end Erdos634.Draft.AllN3

open scoped Classical

namespace Erdos634.Draft.AllN3

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.R8ZF
open Erdos634.Draft.E60Irr

/-- **The base-`α` leaf from the check with divisibility.** -/
theorem s3Closed_of_chkD {N : ℕ} (hN0 : 0 < N) (h : S3ChkD N) : S3Closed N := by
  refine s3Closed_of_inst N ?_
  intro e d m he hd hcop heq
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0] at heq
      have hNd : N * d = 0 := by rw [heq]; ring
      have := Nat.mul_pos hN0 hd
      omega
    · exact h0
  rcases Classical.em (d ∣ m) with hdm | hdm
  · exfalso
    obtain ⟨r, rfl⟩ := hdm
    have hKpos : 0 < kK e d := by unfold kK qQ; positivity
    have heq' : N * d = (d * r) * (d * r) * kK e d := by unfold kK qQ; rw [heq]; ring
    have hN : N = d * r * r * kK e d := by
      have h1 : d * N = d * (d * r * r * kK e d) := by rw [mul_comm d N, heq']; ring
      exact Nat.eq_of_mul_eq_mul_left hd h1
    have hQ' : qQ e d ∣ N := ⟨d * r * r * (2 * e + d), by rw [hN]; unfold kK; ring⟩
    have hle : qQ e d ≤ N := Nat.le_of_dvd hN0 hQ'
    have he2 : e * e ≤ N := by unfold qQ at hle; nlinarith
    have hd2 : 2 * (d * d) ≤ N := by unfold qQ at hle; nlinarith
    apply h e (le_trans (Nat.le_mul_self e) he2) he he2 d (by nlinarith [Nat.le_mul_self d]) hd hd2 hQ'
    have hdiv : N * d / kK e d = (d * r) * (d * r) := by
      rw [heq']; exact Nat.mul_div_cancel _ hKpos
    refine ⟨⟨(d * r) * (d * r), by rw [heq']; ring⟩, ?_, ?_⟩
    · rw [hdiv, Nat.sqrt_eq]
    · rw [hdiv, Nat.sqrt_eq]; exact Dvd.intro r rfl
  · have hnd : ¬ (e + d - e) ∣ m := by rwa [Nat.add_sub_cancel_left]
    intro N' D' a0 a1 a2 a3
    exact Erdos634.Draft.Sqfree3Mod8.s3inst_of_not_dvd m e (e + d) he (by omega) hcop hm hnd D' a0 a1 a2 a3

/-- **ALLN-1c.**  No `N` satisfying `C3 N` is a tile count. -/
theorem not_tile_of_conditions3 (N : ℕ) (h : C3 N) (D : CongruentDissection N) : False := by
  obtain ⟨hsq, ⟨h7, h17⟩, hEll, hNSq, hHAr, hR, hE, hF1, hS2, hS3, hIso, ⟨hF2c, hF3c, hF4c⟩⟩ := h
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := ell_of_chk hsq hEll
  refine chain_gen3 N hsq (s1Closed_of_sqfree N hsq hN0)
    (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2))
    (s3Closed_of_chkD hN0 hS3)
    (isoH9b_of_chk hN0 hIso)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq h7 h17 hns (harith_of_chk hHAr) hℓ hℓ7 hodd)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq h7 h17) hns)
    ?_ (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree N hsq) ?_ ?_ ?_
    (gapR8_of_chk_z hF2c hF3c hF4c) D
  · rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hE with h4 | ⟨h11, h60, -⟩
    · exact gapE60_of_mod4_two N h4
    · exact gapE60_of_chk_sq h11 [] h60 (by intro p hp; cases hp)
  · rcases hE with h4 | ⟨-, -, h120⟩
    · exact gapE120_of_mod4_two N h4
    · exact gapE120_of_chk hN0 h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chk (by omega) hf

/-- the discriminant table is weaker than `Pairs60Chk'` -/
theorem pairsSq_of_pairs60' {N : ℕ} (h : Pairs60Chk' N) : Pairs60ChkSq N [] := by
  intro m hm h1 hd ht hlt
  rcases h m hm h1 hd ht hlt with hpin | ⟨hg, -⟩ | hR
  · exact Or.inr (Or.inl hpin)
  · exact Or.inr (Or.inr (Or.inr hg))
  · exact Or.inr (Or.inr (Or.inr fun hc => (hR hc).1))

/-- `R8ZF.C'' N → C3 N`: the new condition covers at least what `C''` covers -/
theorem c3_of_c'' {N : ℕ} (h : C'' N) : C3 N := by
  obtain ⟨a1, a2, a3, a4, a5, a6, hE, a8, a9, a10, a11, a12⟩ := h
  refine ⟨a1, a2, a3, a4, a5, a6, ?_, a8, a9, s3ChkD_of_s3Chk a10, a11, a12⟩
  rcases hE with h4 | ⟨h11, h60, h120⟩
  · exact Or.inl h4
  · exact Or.inr ⟨h11, pairsSq_of_pairs60' h60, h120⟩

/-- `C3 N → ¬ TileCount N` -/
theorem not_tileCount_of_c3 {N : ℕ} (h : C3 N) : ¬ Erdos634.Draft.TileCountFamilies.TileCount N :=
  fun ⟨D⟩ => not_tile_of_conditions3 N h D

/-- the leaf vector of `C3`: `[Sqf, Range, Ell, NSq, HAr, R, Esq, F1, S2, S3D, Iso, R8z]` -/
def leafVec3 (N : ℕ) : List Bool :=
  [decide (LeafSqf N), decide (LeafRange N), decide (LeafEll N), decide (LeafNSq N), decide (LeafHAr N),
   decide (LeafR N), decide (LeafEsq N), decide (LeafF1 N), decide (LeafS2 N), decide (S3ChkD N),
   decide (LeafIso N), decide (LeafR8z N)]

end Erdos634.Draft.AllN3

#print axioms Erdos634.Draft.AllN3.not_tile_of_conditions3
#print axioms Erdos634.Draft.AllN3.c3_of_c''
