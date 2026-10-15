import Erdos634.MarchJunctions
namespace Erdos634.Draft.MarchJunctionsWrap
open Erdos634.MarchJunctions

theorem wrap_gamma_gamma_impossible (a b g p : ℝ) (ha : 0 < a)
    (hg : g = 2*a + b) (hp : p = 3*a + 2*b) : p < 2 * g :=
  gamma_gamma_impossible a b g p ha hg hp

theorem wrap_three_alpha_fill {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 3 * α) :
    x = 3 ∧ y = 0 ∧ z = 0 :=
  three_alpha_fill hrel hirr x y z hsum

theorem wrap_gamma_wedge_fill {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 2 * α + β) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 2 ∧ y = 1 ∧ z = 0) :=
  gamma_wedge_fill hrel hirr x y z hsum

open Erdos634.Interface in
theorem wrap_a_edge_ends_pair (w e : Corner)
    (hw : (flanks w).1 = Edge.a ∨ (flanks w).2 = Edge.a)
    (he : (flanks e).1 = Edge.a ∨ (flanks e).2 = Edge.a)
    (hne : w ≠ e) :
    (w = Corner.beta ∧ e = Corner.gamma) ∨ (w = Corner.gamma ∧ e = Corner.beta) :=
  a_edge_ends_pair w e hw he hne

open Erdos634.Interface in
theorem wrap_march_orientation_propagates (n : ℕ)
    (west east : ℕ → Corner)
    (hflank : ∀ k ≤ n, ((flanks (west k)).1 = Edge.a ∨ (flanks (west k)).2 = Edge.a) ∧
                       ((flanks (east k)).1 = Edge.a ∨ (flanks (east k)).2 = Edge.a))
    (hpair : ∀ k ≤ n, west k ≠ east k)
    (hnogg : ∀ k < n, ¬ (east k = Corner.gamma ∧ west (k+1) = Corner.gamma))
    (hseed : east 0 = Corner.gamma) :
    ∀ k ≤ n, east k = Corner.gamma :=
  march_orientation_propagates n west east hflank hpair hnogg hseed

example : True := trivial
#print axioms wrap_march_orientation_propagates
end Erdos634.Draft.MarchJunctionsWrap
