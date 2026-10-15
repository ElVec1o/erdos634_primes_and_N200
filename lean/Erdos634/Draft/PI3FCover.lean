/-
Draft/PI3FCover.lean -- the bridge from Theorem T (`PI3FT.theoremT`) to `GapE60 N` for a concrete `N`.

`gapE60_of_T`   : if every invariant pair `(m₁, m₂)` of `N` (`m₁ m₂ = 3N`, `m₂ < m₁ ≤ N`) is either the pinned pair `(N, 3)` or
                  satisfies the two arithmetic hypotheses of Theorem T (`D` non-square, `ℓκ > 2N`), then `GapE60 N`.
`coverCheck`    : a kernel-decidable Bool check of exactly that hypothesis, over `Nat.divisors (3N)`, with soundness
                  `gapE60_of_coverCheck`.
Examples (checked by kernel `decide`, no native_decide): `N = 87`.
-/
import Erdos634.Draft.PI3FT

namespace Erdos634.Draft.PI3F

open Erdos634.Geometry Erdos634.Draft.CompositeE5Gen Erdos634.Draft.Chain15

theorem gapE60_of_T (N : ℕ) (hN : 11 ≤ N)
    (hpairs : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ N → 1 ≤ m₂ → m₂ ≤ N → m₁ * m₂ = 3 * (N : ℤ) → m₂ < m₁ →
      (m₁ = N ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧
        2 * (N : ℤ) * (Int.gcd (m₁ + m₂) (m₁ - m₂) : ℤ) < (m₁ + m₂) * (m₁ - m₂))) : GapE60 N := by
  intro D α a b c hα h hE
  obtain ⟨m₁, m₂, -, -, hm1, hm1N, hm2, hm2N, hS1, hS2, harea, hprod, hlt, -⟩ := Row5.theoremE_sixty D hα h hE
  rcases hpairs m₁ m₂ hm1 hm1N hm2 hm2N hprod hlt with ⟨e1, e2⟩ | ⟨hD, hfl⟩
  · subst e1; subst e2
    exact sixty_pinned_false D hα h hE hN (by exact_mod_cast hS1) (by exact_mod_cast hS2) harea
  · exact theoremT N m₁ m₂ (by omega) hprod hD hfl D α a b c hα h hE hS1 hS2

/-- Kernel-decidable form of the hypothesis of `gapE60_of_T`. -/
def pairT (N m₁ m₂ : ℕ) : Bool :=
  (m₁ == N && m₂ == 3) ||
  ((decide ((m₁ + m₂) ^ 2 < 16 * N) || Nat.sqrt ((m₁ + m₂) ^ 2 - 16 * N) ^ 2 != (m₁ + m₂) ^ 2 - 16 * N) &&
    decide (2 * N * Nat.gcd (m₁ + m₂) (m₁ - m₂) < (m₁ + m₂) * (m₁ - m₂)))

def coverCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun m₁ => decide (1 ≤ m₁ ∧ m₁ * (3 * N / m₁) = 3 * N ∧ 3 * N / m₁ < m₁) → pairT N m₁ (3 * N / m₁)

theorem pairT_sound {N m₁ m₂ : ℕ} (h : pairT N m₁ m₂ = true) (hlt : m₂ < m₁) :
    ((m₁ : ℤ) = N ∧ (m₂ : ℤ) = 3) ∨ (¬ IsSquare (((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ)) ∧
      2 * (N : ℤ) * (Int.gcd ((m₁ : ℤ) + m₂) ((m₁ : ℤ) - m₂) : ℤ) < ((m₁ : ℤ) + m₂) * ((m₁ : ℤ) - m₂)) := by
  unfold pairT at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  rcases h with ⟨e1, e2⟩ | ⟨hns, hg⟩
  · left; subst e1; subst e2; simp
  · right
    have hgcd : Int.gcd ((m₁ : ℤ) + m₂) ((m₁ : ℤ) - m₂) = Nat.gcd (m₁ + m₂) (m₁ - m₂) := by
      have : ((m₁ : ℤ) - m₂) = ((m₁ - m₂ : ℕ) : ℤ) := by omega
      rw [this]; rw [← Nat.cast_add]; rfl
    have hcast : ((m₁ : ℤ) + m₂) = ((m₁ + m₂ : ℕ) : ℤ) := by push_cast; rfl
    have hdiff : ((m₁ : ℤ) - m₂) = ((m₁ - m₂ : ℕ) : ℤ) := by omega
    refine ⟨?_, ?_⟩
    · rintro ⟨r, hr⟩
      have hle : 16 * N ≤ (m₁ + m₂) ^ 2 := by
        by_contra hc
        push_neg at hc
        have h' : (((m₁ + m₂) ^ 2 : ℕ) : ℤ) < ((16 * N : ℕ) : ℤ) := by exact_mod_cast hc
        push_cast at h'
        nlinarith [mul_self_nonneg r]
      rcases hns with hlt2 | hne
      · omega
      · apply hne
        have h0 : (((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ)) = ((((m₁ + m₂) ^ 2 - 16 * N : ℕ)) : ℤ) := by
          rw [Nat.cast_sub hle]; push_cast; ring
        have hr2 : ((((m₁ + m₂) ^ 2 - 16 * N : ℕ)) : ℤ) = r * r := by rw [← h0]; exact hr
        have hr3 : (m₁ + m₂) ^ 2 - 16 * N = r.natAbs * r.natAbs := by
          have := congrArg Int.natAbs hr2
          simpa [Int.natAbs_mul] using this
        rw [hr3, Nat.sqrt_eq]; ring
    · rw [hgcd]
      have h' : ((2 * N * Nat.gcd (m₁ + m₂) (m₁ - m₂) : ℕ) : ℤ) < (((m₁ + m₂) * (m₁ - m₂) : ℕ) : ℤ) := by
        exact_mod_cast hg
      rw [hcast, hdiff]
      push_cast at h' ⊢
      exact h'

theorem gapE60_of_coverCheck (N : ℕ) (hN : 11 ≤ N) (h : coverCheck N = true) : GapE60 N := by
  apply gapE60_of_T N hN
  intro m₁ m₂ h1 hm1N h2 hm2N hprod hlt
  lift m₁ to ℕ using (by omega)
  lift m₂ to ℕ using (by omega)
  have hprodN : m₁ * m₂ = 3 * N := by exact_mod_cast hprod
  have hmem : m₁ ∈ List.range (N + 1) := by rw [List.mem_range]; omega
  have hm2e : 3 * N / m₁ = m₂ := by
    apply Nat.div_eq_of_eq_mul_right (by omega); linarith
  unfold coverCheck at h
  have := List.all_eq_true.mp h m₁ hmem
  simp only [decide_eq_true_eq] at this
  have hc := this ⟨by omega, by rw [hm2e]; exact hprodN, by rw [hm2e]; exact_mod_cast hlt⟩
  rw [hm2e] at hc
  exact pairT_sound hc (by exact_mod_cast hlt)

theorem gapE60_87 : GapE60 87 := gapE60_of_coverCheck 87 (by norm_num) (by decide +kernel)

/-- `N = 1440` (a realized tiling) is NOT certified by the checker. -/
theorem coverCheck_1440_false : coverCheck 1440 = false := by decide +kernel

end Erdos634.Draft.PI3F

#print axioms Erdos634.Draft.PI3F.gapE60_of_T
#print axioms Erdos634.Draft.PI3F.gapE60_of_coverCheck
#print axioms Erdos634.Draft.PI3F.gapE60_87
#print axioms Erdos634.Draft.PI3F.coverCheck_1440_false
