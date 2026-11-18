/-
Draft/WGapLightChunk2.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.
Pruning of the S2 divisor loop: `S2B N A q` is vacuous when `2 q^2 <= A` (then `sqrt(2q^2 - A) = 0`, contradicting `0 < p`) and when `A <= q^2` (then `p*p = 2q^2 - A >= q^2`,
contradicting `p < q`).  So only `sqrt(A/2) < q < sqrt A` needs a kernel loop (about 0.29 sqrt A values instead of 2 sqrt N):
`s2B_vac_low : 2*((hi-1)*(hi-1)) <= A -> RangeAll 0 hi (S2B N A)`, `s2B_vac_high : A <= lo*lo -> RangeAll lo hi (S2B N A)`.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLightChunk

namespace Erdos634.Draft.WGapPure

theorem s2B_vac_low {N A hi : ℕ} (h : 2 * ((hi - 1) * (hi - 1)) ≤ A) : RangeAll 0 hi (S2B N A) := by
  intro i hi'
  have hiq : i ≤ hi - 1 := by omega
  have h1 : i * i ≤ (hi - 1) * (hi - 1) := Nat.mul_self_le_mul_self hiq
  have e : 2 * ((0 + i) * (0 + i)) - A = 0 := by
    have : (0 + i) * (0 + i) = i * i := by simp
    rw [this]; omega
  intro _ _ _ h3
  rw [e] at h3
  simp at h3

theorem s2B_vac_high {N A lo hi : ℕ} (h : A ≤ lo * lo) : RangeAll lo hi (S2B N A) := by
  intro i hi'
  have h1 : lo * lo ≤ (lo + i) * (lo + i) := Nat.mul_self_le_mul_self (by omega)
  intro _ h2 h3 _ _
  have h4 := Nat.mul_self_lt_mul_self h3
  exfalso
  omega

end Erdos634.Draft.WGapPure
