/-
Draft/WGapLightDefs.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.
LIGHT part of the memory-light route to per-N instances of `NSQM.not_tileCount_of_CNzFixW`.  It imports ONLY the modules that define the conjuncts
(not WGapLink1/WGapStation4: about 2.3 GB less fixed memory at load), and states:
* `cover_divisors` : the O(sqrt K) divisor-pair covering lemma (`m | K` is `d` or `K/d` for some `d <= sqrt K`);
* `Pairs60R`, `Pairs120R` : the two O(N) loops of `LeafEsqS` (Pairs60ChkSq N [], Pairs120ChkSq N []) rewritten over `d <= sqrt (3N)`; `leafEsqS_of_R`;
* `RWChkWl` : a verbatim copy of `RWChkW` (defined in the heavy WGapLink2); `CNzFixWl N` = `CNzFixW N` with `LeafEsqS` -> `LeafEsqSR`, `RWChkW` -> `RWChkWl`.
The heavy link `CNzFixWl N -> CNzFixW N` is in WGapLightLink.lean.  No sorry, no native_decide.  Credit: Beeson-Rosu, Paliy, Laczkovich, Zhang (the checks themselves).
-/
import Erdos634.Draft.NSQWin3
import Erdos634.Draft.LeafFixE
import Erdos634.Draft.LeafFixS3
import Erdos634.Draft.AllN3Cond
import Erdos634.Draft.S1BandLeaf
import Erdos634.Draft.AllNExclusionArith2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain
open Erdos634.Draft.R8ZF Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr
open Erdos634.Draft.NSQRWT2
open Erdos634.Draft.AllN3
open Erdos634.Draft.LeafFix

/-- every divisor `m` of `K > 0` is `d` or `K / d` for a divisor `d <= sqrt K` -/
theorem cover_divisors (K : ℕ) (hK : 0 < K) (Q : ℕ → Prop)
    (h : ∀ d ≤ Nat.sqrt K, 0 < d → d ∣ K → Q d ∧ Q (K / d)) (m : ℕ) (hm : m ∣ K) : Q m := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hK
  by_cases hs : m ≤ Nat.sqrt K
  · exact (h m hs hm0 hm).1
  · push Not at hs
    obtain ⟨d, hd⟩ := hm
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; omega
      · exact h0
    have hKm : K < m * m := by
      have := Nat.lt_succ_sqrt K
      have h2 : Nat.succ (Nat.sqrt K) ≤ m := hs
      calc K < Nat.succ (Nat.sqrt K) * Nat.succ (Nat.sqrt K) := this
        _ ≤ m * m := Nat.mul_le_mul h2 h2
    have hdm : d < m := by
      by_contra hge
      push Not at hge
      have : m * m ≤ m * d := Nat.mul_le_mul_left m hge
      omega
    have hdK : d ∣ K := ⟨m, by rw [hd, Nat.mul_comm]⟩
    have hds : d ≤ Nat.sqrt K := by
      apply Nat.le_sqrt.mpr
      calc d * d ≤ m * d := Nat.mul_le_mul_right d hdm.le
        _ = K := hd.symm
    have hdiv : K / d = m := by rw [hd, Nat.mul_comm, Nat.mul_div_cancel_left m hd0]
    have := (h d hds hd0 hdK).2
    rwa [hdiv] at this

/-- the body of `Pairs60ChkSq N []` at the divisor `m` (all hypotheses of the loop kept) -/
def Q60 (N m : ℕ) : Prop :=
  m ≤ N → 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N → 3 * N / m < m →
    (m = N ∧ 3 * N / m = 3) ∨ (m % 2 ≠ N % 2 ∨ (3 * N / m) % 2 ≠ N % 2) ∨
    (16 * N ≤ (m + 3 * N / m) ^ 2 → ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N))

def Q120 (N m : ℕ) : Prop :=
  m ≤ N → 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N →
    (m % 2 ≠ N % 2 ∨ (3 * N / m) % 2 ≠ N % 2) ∨
    ¬ sqChk ((m + 3 * N / m) ^ 2 + 16 * N - 4 * (3 * N))

def Pairs60R (N : ℕ) : Prop := ∀ d ≤ Nat.sqrt (3 * N), 0 < d → d ∣ 3 * N → Q60 N d ∧ Q60 N (3 * N / d)
def Pairs120R (N : ℕ) : Prop := ∀ d ≤ Nat.sqrt (3 * N), 0 < d → d ∣ 3 * N → Q120 N d ∧ Q120 N (3 * N / d)

instance (N : ℕ) : Decidable (Pairs60R N) := by unfold Pairs60R Q60 sqChk; infer_instance
instance (N : ℕ) : Decidable (Pairs120R N) := by unfold Pairs120R Q120 sqChk; infer_instance

theorem pairs60_of_R {N : ℕ} (hN : 0 < N) (h : Pairs60R N) : Pairs60ChkSq N [] := by
  intro m hmN hm1 hdv h3 hlt
  have := cover_divisors (3 * N) (by omega) (Q60 N) h m hdv hmN hm1 hdv h3 hlt
  rcases this with h1 | h1 | h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem pairs120_of_R {N : ℕ} (hN : 0 < N) (h : Pairs120R N) : Pairs120ChkSq N [] := by
  intro m hmN hm1 hdv h3
  have := cover_divisors (3 * N) (by omega) (Q120 N) h m hdv hmN hm1 hdv h3
  rcases this with h1 | h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

def LeafEsqSR (N : ℕ) : Prop := N % 4 = 2 ∨ (11 ≤ N ∧ Pairs60R N ∧ Pairs120R N)
instance (N : ℕ) : Decidable (LeafEsqSR N) := by unfold LeafEsqSR; infer_instance

theorem leafEsqS_of_R {N : ℕ} (h : LeafEsqSR N) : LeafEsqS N := by
  rcases h with h | ⟨h11, h60, h120⟩
  · exact Or.inl h
  · exact Or.inr ⟨h11, pairs60_of_R (by omega) h60, pairs120_of_R (by omega) h120⟩

/-- verbatim copy of `RWChkW` (WGapLink2), so that it can be decided without the heavy import -/
def RWChkWl (N : ℕ) : Prop :=
  ∀ s ≤ Nat.sqrt N, 2 ≤ s → s * s ∣ N → ∀ f ≤ Nat.sqrt (N / (s * s)), N / (s * s) ≤ 2 * f * f →
    ¬ (sqChk (2 * f * f - N / (s * s)) ∧ 0 < Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < f ∧ Nat.Coprime (Nat.sqrt (2 * f * f - N / (s * s))) f ∧
       f ≤ s * Nat.sqrt (2 * f * f - N / (s * s)) ∧
       ¬ (2 ≤ Nat.sqrt (2 * f * f - N / (s * s)) ∧ s * (f - Nat.sqrt (2 * f * f - N / (s * s))) < f))

instance (N : ℕ) : Decidable (RWChkWl N) := by unfold RWChkWl sqChk; infer_instance

def CNzFixWl (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqSR N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2ChkSq N ∧ S3newChk N ∧ IsoH9bChkW N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ GammaChkDW N ∧ Erdos634.Draft.S1Band.S1UBChkW N ∧ RWChkWl N ∧ S5wChkW N

instance (N : ℕ) : Decidable (CNzFixWl N) := by unfold CNzFixWl; infer_instance

end Erdos634.Draft.NSQM
