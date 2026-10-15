import Erdos634.FanPruneSound

/-!
# Soundness of the fan-collapse prune: wrapper

`FanPruneSound.fan_prune_sound` and `.corner_unfillable` are pure real arithmetic.

Key theorems in `FanPruneSound.lean`:

1. **`fan_prune_sound`**: If W < β and W is not a multiple of α, then no multiset
   from {α,β,γ} with β≤γ sums to W.
2. **`residue_trapped`**: The residue W−⌊W/α⌋·α is in (0,α) when W is not a multiple.
3. **`corner_unfillable`**: W < β and W not a multiple ⟹ fan-corner is dead.

Pure real arithmetic, no geometry: no sorry, standard axioms.
-/

namespace Erdos634.Draft.FanPruneSoundWrap

open Erdos634.FanPruneSound

/-- Fan prune soundness: W < β and not a multiple of α → multiset from {α,β,γ} cannot sum to W. -/
theorem fanprune_sound {α β γ W : ℝ} (hα : 0 ≤ α) (hβγ : β ≤ γ) (hW : W < β)
    (hnotmul : ∀ k : ℕ, W ≠ (k : ℝ) * α)
    (angles : Multiset ℝ) (hmem : ∀ x ∈ angles, x = α ∨ x = β ∨ x = γ)
    (hnn : ∀ x ∈ angles, 0 ≤ x) (hsum : angles.sum = W) : False :=
  fan_prune_sound hα hβγ hW hnotmul angles hmem hnn hsum

/-- Residue trapped: W−⌊W/α⌋·α ∈ (0,α) when W is not an α-multiple. -/
theorem fanprune_residue {α W : ℝ} (hα : 0 < α) (hW : 0 < W)
    (hnotmul : W - (⌊W / α⌋₊ : ℝ) * α ≠ 0) :
    0 < W - (⌊W / α⌋₊ : ℝ) * α ∧ W - (⌊W / α⌋₊ : ℝ) * α < α :=
  residue_trapped hα hW hnotmul

/-- Non-vacuity: the hypotheses are satisfiable for α=1, β=2, W=0.5. -/
theorem fanprune_witness : (0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 2 ∧ (0.5:ℝ) < 2 ∧
    (∀ k : ℕ, (0.5:ℝ) ≠ (k : ℝ) * 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun k => ?_⟩
  intro h
  have : (k : ℝ) = 0.5 := by linarith
  have : (2 : ℤ) * k = 1 := by exact_mod_cast (by linarith : (2 : ℝ) * k = 1)
  omega

#print axioms fanprune_sound
#print axioms fanprune_residue

end Erdos634.Draft.FanPruneSoundWrap
