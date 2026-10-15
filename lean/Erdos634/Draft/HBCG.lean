/-
Draft/HBCG.lean -- HBG: `hbSimilar'_all : forall N, HBSimilar' N`, i.e. HBSimilar N for every N not of the form 3 s^2.
Case analysis on the squarefree part n: n in {1,2,5} sum of two squares trivially; n = 3 excluded; every other
squarefree n lies in NQ'' (n = 6, 13 explicit; the rest 7 <= n with n >= 17 or n % 4 in {2,3}).
-/
import Erdos634.Draft.HBCS13
import Erdos634.Draft.HBCNQ
import Erdos634.Draft.CaseAComposite

open scoped Classical

namespace Erdos634.Draft.HBCG

open Erdos634.Geometry Erdos634.Draft.ChainComposite Erdos634.Draft.HBCNQ

theorem hbSimilar_of_NQ'' {N : ℕ} (h : NQ'' N) : HBSimilar N :=
  fun D μ τ hs => Row2.theoremS_perm_nsq'' D μ τ hs h

theorem hbSimilar'_all (N : ℕ) : HBSimilar' N := by
  intro h3
  by_cases hN0 : N = 0
  · intro D μ τ hs; exact ⟨0, 0, by simp [hN0]⟩
  obtain ⟨n, s, hn0, hs0, hNs, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hN0)
  -- hNs : s^2 * n = N
  have hN : N = s ^ 2 * n := hNs.symm
  by_cases h1 : n = 1
  · subst h1; intro D μ τ hs; exact ⟨s, 0, by rw [hN]; ring⟩
  by_cases h2 : n = 2
  · subst h2; intro D μ τ hs; exact ⟨s, s, by rw [hN]; ring⟩
  by_cases h5 : n = 5
  · subst h5; intro D μ τ hs; exact ⟨s, 2 * s, by rw [hN]; ring⟩
  by_cases h3' : n = 3
  · exact absurd (by rw [hN, h3']; ring : N = 3 * s ^ 2) (h3 s)
  apply hbSimilar_of_NQ''
  by_cases h6 : n = 6
  · subst h6; exact Or.inl (Or.inr ⟨s, hs0, hN⟩)
  by_cases h13 : n = 13
  · subst h13; exact Or.inr ⟨s, hs0, hN⟩
  refine Or.inl (Or.inl ⟨s, n, hs0, hsq, hN, ?_, ?_⟩)
  · by_contra hlt
    have : n ≤ 6 := by omega
    interval_cases n <;> first | omega | exact absurd hsq (by decide +kernel)
  · by_contra hc
    have h7 : 7 ≤ n := by
      by_contra hlt
      have : n ≤ 6 := by omega
      interval_cases n <;> first | omega | exact absurd hsq (by decide +kernel)
    have : n ≤ 16 := by omega
    interval_cases n <;> first | omega | exact absurd hsq (by decide +kernel)

theorem gB_38 : HBSimilar 38 := hbSimilar'_all 38 (by
  intro s h; generalize s ^ 2 = t at h; omega)
theorem gB_86 : HBSimilar 86 := hbSimilar'_all 86 (by
  intro s h; generalize s ^ 2 = t at h; omega)

/-- Consistency: the pre-existing `CaseAComposite` statements are the same Prop. -/
example : gB_38 = Erdos634.CaseA.RComposite.hbSimilar_38 := rfl

end Erdos634.Draft.HBCG

#print axioms Erdos634.Draft.HBCG.hbSimilar'_all
#print axioms Erdos634.Draft.HBCG.gB_86
