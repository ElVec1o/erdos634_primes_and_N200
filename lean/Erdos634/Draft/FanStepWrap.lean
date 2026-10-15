import Erdos634.FanStep

/-!
# FanStep — fan step exhaustion (γ/β/through never fit): wrapper

Key results:
- `gamma_never_fits`: γ never fits in the wedge at any stage
- `beta_only_at_start`: β fits only at step k=0
- `step_exhaustion`: in wedge after k≥1 steps, any tile must contribute α
- `alpha_advances`: α-step advances remainder by exactly α

No sorry, standard axioms.
-/

namespace Erdos634.Draft.FanStepWrap

open Erdos634.FanStep

theorem fs_gamma_never_fits (a b : ℝ) (ha : 0 < a) (k : ℕ) :
    b - (k : ℝ) * a < 2 * a + b := gamma_never_fits a b ha k

theorem fs_beta_only_at_start (a b : ℝ) (ha : 0 < a) (k : ℕ)
    (h : b ≤ b - (k : ℝ) * a) : k = 0 := beta_only_at_start a b ha k h

theorem fs_alpha_advances (a b : ℝ) (k : ℕ) :
    b - ((k : ℝ) + 1) * a = (b - (k : ℝ) * a) - a := alpha_advances a b k

theorem fs_step_exhaustion (a b g p θ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hg : g = 2 * a + b) (hp : p = 3 * a + 2 * b) (k : ℕ) (hk : 1 ≤ k)
    (hfit : θ ≤ b - (k : ℝ) * a)
    (hcase : θ = a ∨ θ = b ∨ θ = g ∨ θ = p) : θ = a :=
  step_exhaustion a b g p θ ha hb hg hp k hk hfit hcase

-- Non-vacuity: gamma_never_fits at a=1, b=2, k=0
example : (2 : ℝ) - (0 : ℕ) * 1 < 2 * 1 + 2 := fs_gamma_never_fits 1 2 one_pos 0

#print axioms fs_step_exhaustion

end Erdos634.Draft.FanStepWrap
