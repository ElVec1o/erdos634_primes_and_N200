import Erdos634.MarchStep
namespace Erdos634.Draft.MarchStepWrap
open Erdos634.MarchStep

theorem wrap_polar_extremes {α φ ψ : ℝ}
    (hφ : φ ∈ Set.Icc (0:ℝ) α) (hψ : ψ ∈ Set.Icc (0:ℝ) α) (hsep : |φ - ψ| = α) :
    (φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0) :=
  polar_extremes hφ hψ hsep

theorem wrap_two_placements {b c s t : ℝ} (hbc : b ≠ c)
    (hs : s = b ∨ s = c) (ht : t = b ∨ t = c) (hst : s ≠ t) :
    (s = b ∧ t = c) ∨ (s = c ∧ t = b) :=
  two_placements hbc hs ht hst

theorem wrap_lengths_distinct (f : ℕ) : ((f * f : ℝ) - 1) ≠ (f * f : ℝ) :=
  lengths_distinct f

theorem wrap_march_dies (S : ℕ → Prop) (h0 : S 0) (h1 : S 1)
    (hstep : ∀ n, S n → S (n + 1) → S (n + 2)) : ∀ n, S n :=
  march_dies S h0 h1 hstep

theorem wrap_tree_size_bound (T : ℕ → ℤ) (n : ℕ)
    (hb : T (n + 2) ≤ T (n + 1) + T n + 2) :
    T (n + 2) - T (n + 1) - T n ≤ 2 :=
  tree_size_bound T n hb

theorem wrap_overshoot_le_one (L p s : ℕ) (hp : p < L) (hs : s = 1 ∨ s = 2) (hover : L ≤ p + s) :
    p + s ≤ L + 1 :=
  overshoot_le_one L p s hp hs hover

theorem wrap_terminal_residue_cases (L p s : ℕ) (hp : p < L) (hs : s = 1 ∨ s = 2) (hover : L ≤ p + s) :
    p + s - L = 0 ∨ p + s - L = 1 :=
  terminal_residue_cases L p s hp hs hover

theorem wrap_offset_terminal_dies (f x y z : ℕ) (hf : 2 ≤ f) (L p s : ℕ)
    (hp : p < L) (hs : s = 1 ∨ s = 2) (hover : L ≤ p + s) (hres : p + s - L = 1)
    (hcover : x * f + y * (f ^ 2 - 1) + z * f ^ 2 = p + s - L) : False :=
  offset_terminal_dies f x y z hf L p s hp hs hover hres hcover

theorem wrap_offset_terminal_witness :
    (4 : ℕ) < 5 ∧ ((2 : ℕ) = 1 ∨ (2 : ℕ) = 2) ∧ (5 : ℕ) ≤ 4 + 2 ∧ (4 + 2 - 5 : ℕ) = 1 :=
  offset_terminal_witness

example : True := trivial
#print axioms wrap_march_dies
end Erdos634.Draft.MarchStepWrap
