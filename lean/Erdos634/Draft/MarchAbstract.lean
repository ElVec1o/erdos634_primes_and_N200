import Mathlib.Tactic

/-!
# Two refutations of abstract formulations of the march obligations

Two ways of stating the remaining obligations of the march, by quantifying over an abstract advance
function or an abstract refutation predicate, are false; both refutations are machine-checked here.

* `abstract_advance_false` : "`adv flush = 1` and `adv crossed = 2` for every `adv`" is refuted by
  `adv ≡ 0`;
* `abstract_step_false` : "`R (bp − 1) → R bp` for every `R`" is refuted at `bp = 2` by
  `R n = (n ≤ 1)`.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.MarchAbstract

/-- The two chiralities, `true` for flush and `false` for crossed. -/
theorem abstract_advance_false : ¬ ∀ adv : Bool → ℕ, adv true = 1 ∧ adv false = 2 := by
  intro h
  have := (h (fun _ => 0)).1
  omega

theorem abstract_step_false : ¬ ∀ R : ℕ → Prop, R (2 - 1) → R 2 := by
  intro h
  have := h (fun n => n ≤ 1) (by norm_num)
  omega

end Erdos634.Draft.MarchAbstract
