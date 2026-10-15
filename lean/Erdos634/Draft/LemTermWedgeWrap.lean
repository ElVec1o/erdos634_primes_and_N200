import Erdos634.AngleArithmetic
import Erdos634.VertexFigureReal

/-!
# The terminal wedge decomposes as γ+α+β: arithmetic kernel

The terminal wedge of a base-reaching column decomposes as
the figure {γ, α, β}, one tile of each angle. Two arithmetic facts underlie this:

1. **`alpha_beta_corner`**: na+2ng=1, nb+ng=1 ⟹ (na,nb,ng)=(1,1,0) — the {α,β} corner.
2. **`boundary_figure_cases`**: at a real boundary point (sum=π), the figure is one of
   (straight: s=1,p=q=r=0), (3α,2β), or (α,β,γ).

A base-reaching column and its terminal wedge are placement notions (a column, its anchor offset x₀, its last
filler, its last column tile) with no definition in this file.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.LemTermWedgeWrap

open Erdos634.AngleArithmetic Erdos634.VertexFigureReal

/-- The α-β corner: na+2ng=1, nb+ng=1 ⟹ (na,nb,ng)=(1,1,0). -/
theorem termwedge_alpha_beta_corner (na nb ng : ℕ) (hx : na + 2 * ng = 1) (hy : nb + ng = 1) :
    na = 1 ∧ nb = 1 ∧ ng = 0 :=
  alpha_beta_corner na nb ng hx hy

/-- Boundary figure: for 3α+2β=π with γ=2α+β, the figures at a boundary point are
    straight (s=1), {3α,2β}, or {α,β,γ}. -/
theorem termwedge_boundary_cases {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi) :
    (s = 1 ∧ p = 0 ∧ q = 0 ∧ r = 0) ∨
      (s = 0 ∧ ((p = 3 ∧ q = 2 ∧ r = 0) ∨ (p = 1 ∧ q = 1 ∧ r = 1))) :=
  boundary_figure_cases hγ hrel hirr p q r s hsum

/-- Non-vacuity for alpha_beta_corner: (1,1,0) satisfies the conditions. -/
theorem termwedge_witness :
    (1 : ℕ) + 2 * 0 = 1 ∧ (1 : ℕ) + 0 = 1 := by norm_num

#print axioms termwedge_alpha_beta_corner
#print axioms termwedge_boundary_cases

end Erdos634.Draft.LemTermWedgeWrap
