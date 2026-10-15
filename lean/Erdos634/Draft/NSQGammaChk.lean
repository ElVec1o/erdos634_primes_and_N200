/-
Draft/NSQGammaChk.lean — decidable bounded form of `NSQLegs.GammaArith` (kept in its own file: `NSQLegs` opens `Classical`).
`GammaChk 56` holds (`decide +kernel`), `¬ GammaChk 76` and `¬ GammaChk 60` (negative controls: `gcd(k, N) = 2`).
`caseG_56 : CaseGClosed 56`.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQLegs

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQLegs

open Erdos634.Geometry Erdos634.Draft.ChainComposite

def GammaChk (N : ℕ) : Prop :=
  ∀ M ≤ N, 0 < M → M ∣ N → 3 * M < N / M → M % 2 = N % 2 → (N / M) % 2 = N % 2 →
    Nat.Coprime (((N / M) - M) / 2) N

instance (N : ℕ) : Decidable (GammaChk N) := by unfold GammaChk; infer_instance

theorem gammaArith_of_chk {N : ℕ} (h : GammaChk N) : GammaArith N := by
  intro M M' hM hNM hlt hMp hM'p
  have hMN : M ≤ N := by rw [← hNM]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hdvd : M ∣ N := ⟨M', hNM.symm⟩
  have hdiv : N / M = M' := by rw [← hNM]; exact Nat.mul_div_cancel_left _ hM
  have := h M hMN hM hdvd (by rw [hdiv]; exact hlt) hMp (by rw [hdiv]; exact hM'p)
  rwa [hdiv] at this

theorem gammaChk_56 : GammaChk 56 := by decide +kernel
/-- Negative controls: `gcd(k, N) = 2` at `N = 76` (M = 2, M' = 38, k = 18) and `N = 60` (M = 2, M' = 30, k = 14). -/
theorem not_gammaChk_76 : ¬ GammaChk 76 := by decide +kernel
theorem not_gammaChk_60 : ¬ GammaChk 60 := by decide +kernel

theorem caseG_56 : CaseGClosed 56 := caseG_of_gammaArith 56 (gammaArith_of_chk gammaChk_56)

end Erdos634.Draft.NSQLegs

#print axioms Erdos634.Draft.NSQLegs.gammaArith_of_chk
#print axioms Erdos634.Draft.NSQLegs.caseG_56
