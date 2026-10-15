/-
Draft/PI3HArithLink.lean -- link of the Bool pair table of `PI3HArithDefs` to the existing Lean pair-table branches.

* `pairT'_eq`        : `pairT'` is definitionally `PI3F.pairT` (the Theorem-T branch of `gapE60_of_T`); soundness inherited from `PI3F.pairT_sound`.
* `pairExisting_sound` : the pinned pair `(N,3)` and the `D < 0` pairs are exactly the shapes dispatched by the existing branches of
                         `CompositeE5Gen.gapE60_of_pairs_exc` (pinned: `sixty_pinned_false`; `D < 0`: `¬ IsSquare D` and the vacuous `0 ≤ D → ...`).
So `pairCovered N m1 m2 = true` has, for the first two disjuncts, a proved meaning; the third disjunct (`stripLevelKill`) is the arithmetic
side of the strip/level/T2 kill, whose geometric side is not formalized.  No sorry, no native_decide.
-/
import Erdos634.Draft.PI3HArithKill
import Erdos634.Draft.PI3FCover

namespace Erdos634.Draft.PI3H

theorem pairT'_eq : pairT' = PI3F.pairT := rfl

theorem pairExisting_sound {N m₁ m₂ : ℕ} (h : pairExisting N m₁ m₂ = true) :
    ((m₁ : ℤ) = N ∧ (m₂ : ℤ) = 3) ∨
      (¬ IsSquare (((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ)) ∧
        (0 ≤ ((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ) → ∀ p r : ℤ, 0 ≤ p → 0 ≤ r →
          2 * (N : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  unfold pairExisting at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨e1, e2⟩ | hlt
  · left; subst e1; subst e2; simp
  · right
    have hlt' : ((m₁ : ℤ) + m₂) ^ 2 < 16 * (N : ℤ) := by exact_mod_cast hlt
    refine ⟨?_, fun h0 => absurd h0 (by linarith)⟩
    rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]

/-- the covered-pair predicate, first two disjuncts: proved meaning. -/
theorem pairCovered_cases {N m₁ m₂ : ℕ} (h : pairCovered N m₁ m₂ = true) (hlt : m₂ < m₁) :
    pairExisting N m₁ m₂ = true ∨ pairT' N m₁ m₂ = true ∨
      ((m₂ % 3 == 0) && xUnc N (m₂ / 3) && (N / (m₂ / 3) == m₁) && pairKill N (m₂ / 3)) = true := by
  unfold pairCovered at h
  simp only [Bool.or_eq_true] at h
  tauto

end Erdos634.Draft.PI3H

#print axioms Erdos634.Draft.PI3H.pairT'_eq
#print axioms Erdos634.Draft.PI3H.pairExisting_sound
#print axioms Erdos634.Draft.PI3H.pairCovered_cases
