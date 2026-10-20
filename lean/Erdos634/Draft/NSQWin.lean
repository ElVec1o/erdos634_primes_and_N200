/-
Draft/NSQWin.lean -- WINDOWED (sqrt-bounded) forms of the quadratic / O(N) decidable leaf checks of the final chain
`CN'zETWD3` (`NSQMMainZETWD3`), so that `decide +kernel` does O(sqrt N * sqrt N) or O(sqrt N) work per leaf.
* `NQChkW`: `NQChk` quantified `exists s <= sqrt N` with `n = N / s^2` (was `exists s <= N, exists n <= N`: quadratic).
* The sqrt-bounded variants of `AllNExclusionArith(2)` / `AllN3Cond` (`NSqChkSq`, `NHSqChkSq`, `HArithChkSq`, `S2ChkSq`, `S3ChkSq`,
  `NoF2ChkSq`, `NoF3zChkSq`, `NoF4zChkSq`) already carry their soundness lemmas; this module packages them into
  `CN'zETWD4 N` and proves `CN'zETWD4 N -> CN'zETWD3 N` for ALL `N` (`cnzETWD3_of_D4`), hence the whole chain theorem.
Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMMainZETWD3
import Erdos634.Draft.AllN3Cond

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.NSQMain

def NQChkW (N : ℕ) : Prop :=
  ∃ s ≤ Nat.sqrt N, 0 < s ∧ s * s ∣ N ∧ Squarefree (N / (s * s)) ∧ 7 ≤ N / (s * s) ∧
    (17 ≤ N / (s * s) ∨ (N / (s * s)) % 4 = 2 ∨ (N / (s * s)) % 4 = 3)

instance (N : ℕ) : Decidable (NQChkW N) := by unfold NQChkW; infer_instance

theorem nqChk_of_W {N : ℕ} (h : NQChkW N) : NQChk N := by
  obtain ⟨s, hs, h0, ⟨k, hk⟩, hsq, h7, hq⟩ := h
  have hdiv : N / (s * s) = k := by rw [hk]; exact Nat.mul_div_cancel_left _ (Nat.mul_pos h0 h0)
  rw [hdiv] at hsq h7 hq
  have hsN : s ≤ N := le_trans hs (Nat.sqrt_le_self N)
  have hk0 : 0 < k := by omega
  have hkN : k ≤ N := by rw [hk]; exact Nat.le_mul_of_pos_left k (Nat.mul_pos h0 h0)
  exact ⟨s, hsN, k, hkN, h0, hsq, by rw [hk]; ring, h7, hq⟩

/-- The windowed final chain. -/
def CN'zETWD4 (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqN N ∧ LeafF1p N ∧ S2ChkSq N ∧ S3ChkSq N ∧ LeafIso N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ Erdos634.Draft.ThmD.GammaChkD N ∧
    Erdos634.Draft.NSQS1T2.S1t2Chk N ∧ Erdos634.Draft.NSQRWT2.RWChkT2 N ∧ S5wChk N

instance (N : ℕ) : Decidable (CN'zETWD4 N) := by unfold CN'zETWD4; infer_instance

theorem cnzETWD3_of_D4 {N : ℕ} (h : CN'zETWD4 N) : CN'zETWD3 N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ⟨a, b, c⟩, h12, h13, h14, h15⟩ := h
  refine ⟨nqChk_of_W h1, h2, nsqChk_of_sq h3, hArithChk_of_sq h4, ?_, h6, h7, s2Chk_of_sq h8, s3Chk_of_sq h9, h10,
    ⟨noF2Chk_of_sq a, noF3zChk_of_sq b, noF4zChk_of_sq c⟩, h12, h13, h14, h15⟩
  rcases h5 with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, nhsqChk_of_sq h'⟩

theorem not_tile_of_conditionsNSQzETWD4 (N : ℕ) (h : CN'zETWD4 N) (D : CongruentDissection N) : False :=
  not_tile_of_conditionsNSQzETWD3 N (cnzETWD3_of_D4 h) D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD4
