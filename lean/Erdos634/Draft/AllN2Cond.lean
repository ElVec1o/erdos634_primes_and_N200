/-
Draft/AllN2Cond.lean -- The condition `C' N` = `C N` with the pi/3 pair table `Pairs60Chk` replaced by
`Pairs60Chk'`, which admits, in addition, a pair `(m1, m2)` whose `D = (m1+m2)^2 - 16 N` is a non-square and `3 ∤ m1`
(killed uniformly by `E60V.e60Pair_of_not_three_dvd`).  One theorem, quantified over every N:

    theorem not_tile_of_conditions' (N : ℕ) (h : C' N) (D : CongruentDissection N) : False

via `gapE60_of_pairs_mod3` and the leaves of `chain_gen3` exactly as in `AllNExclusion.not_tile_of_conditions`.
`C' N ⇐ C N` (so C' covers at least what C covers).  No sorry, no native_decide.
-/
import Erdos634.Draft.AllNExclusion
import Erdos634.Draft.E60VMod3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.AllN2

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion

/-- The π/3 pair table with the extra admissible case `D` non-square and `3 ∤ m₁`. -/
def Pairs60Chk' (N : ℕ) : Prop :=
  ∀ m ≤ N, 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N → 3 * N / m < m →
    (m = N ∧ 3 * N / m = 3) ∨
    ((16 * N ≤ (m + 3 * N / m) ^ 2 → ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N)) ∧ m % 3 ≠ 0) ∨
    (16 * N ≤ (m + 3 * N / m) ^ 2 →
      ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N) ∧
      ∀ p ≤ 2 * N / (m + 3 * N / m),
        ¬ (p * (m + 3 * N / m) ≤ 2 * N ∧ (m - 3 * N / m) ∣ (2 * N - p * (m + 3 * N / m))))

instance (N : ℕ) : Decidable (Pairs60Chk' N) := by unfold Pairs60Chk' sqChk; infer_instance

theorem nonsq_of_guard (N m₁ m₂ : ℕ)
    (hg : 16 * N ≤ (m₁ + m₂) ^ 2 → ¬ sqChk ((m₁ + m₂) ^ 2 - 16 * N)) :
    ¬ IsSquare (((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ)) := by
  by_cases hc : 16 * N ≤ (m₁ + m₂) ^ 2
  · exact not_isSquare_of_chk ((m₁ + m₂) ^ 2 - 16 * N) _
      (by rw [Nat.cast_sub hc]; push_cast; ring) (hg hc)
  · apply Erdos634.Draft.AllNExclusion.not_isSquare_of_neg
    have : (m₁ + m₂) ^ 2 < 16 * N := by omega
    have : (((m₁ + m₂) ^ 2 : ℕ) : ℤ) < ((16 * N : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at this ⊢; linarith

theorem pairs60'_of_chk {N : ℕ} (h : Pairs60Chk' N) :
    ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ N → 1 ≤ m₂ → m₂ ≤ N → m₁ * m₂ = 3 * (N : ℤ) → m₂ < m₁ →
      (m₁ = N ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧ ¬ (3 : ℤ) ∣ m₁) ∨
        (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧
        (0 ≤ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) →
          ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (N : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 hp hlt
  lift m₁ to ℕ using (by omega)
  lift m₂ to ℕ using (by omega)
  have hp' : m₁ * m₂ = 3 * N := by exact_mod_cast hp
  have hm1 : 1 ≤ m₁ := by exact_mod_cast h1
  have hm1N : m₁ ≤ N := by exact_mod_cast h2
  have hm2N : m₂ ≤ N := by exact_mod_cast h4
  have hlt' : m₂ < m₁ := by exact_mod_cast hlt
  have hdvd : m₁ ∣ 3 * N := ⟨m₂, hp'.symm⟩
  have hdiv : 3 * N / m₁ = m₂ := by rw [← hp']; exact Nat.mul_div_cancel_left _ hm1
  rcases h m₁ hm1N hm1 hdvd (by rw [hdiv]; exact hm2N) (by rw [hdiv]; exact hlt') with
    ⟨e1, e2⟩ | ⟨hg, h3⟩ | hR
  · rw [hdiv] at e2
    left
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  · rw [hdiv] at hg
    right; left
    refine ⟨nonsq_of_guard N m₁ m₂ hg, ?_⟩
    intro hd
    have : 3 ∣ m₁ := by exact_mod_cast hd
    omega
  · rw [hdiv] at hR
    right; right
    constructor
    · exact nonsq_of_guard N m₁ m₂ (fun hc => (hR hc).1)
    · intro hD p r hp0 hr0 hcon
      have hc : 16 * N ≤ (m₁ + m₂) ^ 2 := by
        by_contra hc
        have : (m₁ + m₂) ^ 2 < 16 * N := by omega
        have : (((m₁ + m₂) ^ 2 : ℕ) : ℤ) < ((16 * N : ℕ) : ℤ) := by exact_mod_cast this
        push_cast at this hD; linarith
      lift p to ℕ using hp0
      lift r to ℕ using hr0
      have hcon' : 2 * N = p * (m₁ + m₂) + r * (m₁ - m₂) := by
        have e : (2 * N : ℤ) = p * (m₁ + m₂) + r * ((m₁ : ℤ) - m₂) := by exact_mod_cast hcon
        have e2 : (2 * N : ℤ) = ((p * (m₁ + m₂) + r * (m₁ - m₂) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub hlt'.le]; linarith
        exact_mod_cast e2
      have hApos : 0 < m₁ + m₂ := by omega
      refine (hR hc).2 p ?_ ⟨by omega, ⟨r, by rw [show 2 * N - p * (m₁ + m₂) = r * (m₁ - m₂) by omega]; ring⟩⟩
      exact (Nat.le_div_iff_mul_le hApos).mpr (by omega)

/-- `Pairs60Chk' N ⇒ GapE60 N` (for `11 ≤ N`; the statement quantifies over all `N`, the range hypothesis is the one of
`gapE60_of_pairs_mod3`). -/
theorem gapE60_of_chk' {N : ℕ} (hN : 11 ≤ N) (h : Pairs60Chk' N) : GapE60 N :=
  Erdos634.Draft.E60V.gapE60_of_pairs_mod3 N hN (pairs60'_of_chk h)

def LeafE' (N : ℕ) : Prop := N % 4 = 2 ∨ (11 ≤ N ∧ Pairs60Chk' N ∧ Pairs120Chk N)

/-- **The condition `C' N`.** -/
def C' (N : ℕ) : Prop :=
  LeafSqf N ∧ LeafRange N ∧ LeafEll N ∧ LeafNSq N ∧ LeafHAr N ∧ LeafR N ∧ LeafE' N ∧ LeafF1 N ∧ LeafS2 N ∧
    LeafS3 N ∧ LeafIso N ∧ LeafR8 N

instance (N : ℕ) : Decidable (LeafE' N) := by unfold LeafE'; infer_instance
instance (N : ℕ) : Decidable (C' N) := by unfold C'; infer_instance

/-- **ALLN-1b.**  No `N` satisfying `C' N` is a tile count. -/
theorem not_tile_of_conditions' (N : ℕ) (h : C' N) (D : CongruentDissection N) : False := by
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
  · rcases hR with hodd2 | ⟨hev, hnh⟩
    · exact caseR_of_odd N hodd2
    · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)
  · rcases hE with h4 | ⟨h11, h60, -⟩
    · exact gapE60_of_mod4_two N h4
    · exact gapE60_of_chk' h11 h60
  · rcases hE with h4 | ⟨-, -, h120⟩
    · exact gapE120_of_mod4_two N h4
    · exact gapE120_of_chk hN0 h120
  · rcases hF1 with h4 | hf
    · exact gapF1_of_mod4_two N h4
    · exact gapF1_of_chk (by omega) hf

/-- `Pairs60Chk N ⇒ Pairs60Chk' N` (the new table is weaker), hence `C N ⇒ C' N`. -/
theorem pairs60'_of_pairs60 {N : ℕ} (h : Pairs60Chk N) : Pairs60Chk' N := by
  intro m hm h1 hd ht hlt
  rcases h m hm h1 hd ht hlt with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem C'_of_C {N : ℕ} (h : C N) : C' N := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m⟩ := h
  refine ⟨a, b, c, d, e, f, ?_, i, j, k, l, m⟩
  rcases g with g | ⟨g1, g2, g3⟩
  · exact Or.inl g
  · exact Or.inr ⟨g1, pairs60'_of_pairs60 g2, g3⟩

/-- The leaf vector of `C'`: `[Sqf, Range, Ell, NSq, HAr, R, E', F1, S2, S3, Iso, R8]`. -/
def leafVec' (N : ℕ) : List Bool :=
  [decide (LeafSqf N), decide (LeafRange N), decide (LeafEll N), decide (LeafNSq N), decide (LeafHAr N),
   decide (LeafR N), decide (LeafE' N), decide (LeafF1 N), decide (LeafS2 N), decide (LeafS3 N),
   decide (LeafIso N), decide (LeafR8 N)]

end Erdos634.Draft.AllN2

#print axioms Erdos634.Draft.AllN2.gapE60_of_chk'
#print axioms Erdos634.Draft.AllN2.not_tile_of_conditions'
#print axioms Erdos634.Draft.AllN2.C'_of_C
