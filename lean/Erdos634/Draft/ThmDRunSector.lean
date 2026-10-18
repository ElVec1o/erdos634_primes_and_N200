import Erdos634.Draft.APrimeLegBuild

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module 4: the figure lemma (F) and its sectors for the gamma = 2 alpha tile  (DRAFT, NOT COMPILED, )

Written 2026-10-18 while the Lean slot was busy; never run through `lake`/`lean`.  Not in `All`.

Port target: `Draft/SideRunGSources.lean` (`gamma_alpha_alpha`, `four_alpha`, `two_bg`, `three_beta`, `corner_two_alpha`,
`corner_two_beta`, ...) -- the angle-arithmetic half: which multisets `{α^X, β^Y, γ^Z}` fill a given sector.  For the
base-beta tile (`γ = 2α + β`, `3α + 2β = π`) these are different statements; for `β = π − 3α`, `γ = 2α` they all follow
from `APrimeLegBuild.cnt_eq` (the relation lattice of `α, β, γ, π` with `α/π` irrational):

    X α + Y β + Z γ = m α + n π   ⟺   X − 3Y + 2Z = m  ∧  Y = n.

Sectors proved (`(X,Y,Z)` = numbers of `α, β, γ` tiles):

| sector            | value        | solutions                                   | name                      |
|-------------------|--------------|---------------------------------------------|---------------------------|
| α                 | α            | (1,0,0)                                     | `sector_alpha`            |
| β                 | β            | (0,1,0)                                     | `sector_beta`             |
| γ                 | 2α           | (2,0,0), (0,0,1)                            | `sector_gamma`            |
| α+β = π − γ       | π − 2α       | (1,1,0)  [atomic]                           | `sector_ab`               |
| π − α             | π − α        | (2,1,0), (0,1,1)                            | `sector_pi_minus_alpha`   |
| π − β             | 3α           | (3,0,0), (1,0,1)                            | `sector_pi_minus_beta`    |
| straight          | π            | (3,1,0), (1,1,1)  [= `straight_vertex`]     | `sector_straight`         |
| full              | 2π           | (6,2,0),(4,2,1),(2,2,2),(0,2,3)             | `sector_full`             |

Consequences used by Lemma K (hand proof, conjV2.md §1): the sector at `P` between the diagonal and the side `S′` is `π − γ = α + β`,
atomic (`sector_ab`): ONE α-tile and ONE β-tile and no γ.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Draft.APrimeLegBuild

variable {α : ℝ}

theorem sector_alpha (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = α) : X = 1 ∧ Y = 0 ∧ Z = 0 := by
  have := cnt_eq α hirr X Y Z 1 0 (by push_cast; linarith)
  omega

theorem sector_beta (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = Real.pi - 3 * α) :
    X = 0 ∧ Y = 1 ∧ Z = 0 := by
  have := cnt_eq α hirr X Y Z (-3) 1 (by push_cast; linarith)
  omega

theorem sector_gamma (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = 2 * α) :
    (X = 2 ∧ Y = 0 ∧ Z = 0) ∨ (X = 0 ∧ Y = 0 ∧ Z = 1) := by
  have := cnt_eq α hirr X Y Z 2 0 (by push_cast; linarith)
  omega

/-- **The sector `π − γ = α + β` is atomic**: one `α`-tile, one `β`-tile, no `γ`. -/
theorem sector_ab (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = Real.pi - 2 * α) :
    X = 1 ∧ Y = 1 ∧ Z = 0 := by
  have := cnt_eq α hirr X Y Z (-2) 1 (by push_cast; linarith)
  omega

theorem sector_pi_minus_alpha (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = Real.pi - α) :
    (X = 2 ∧ Y = 1 ∧ Z = 0) ∨ (X = 0 ∧ Y = 1 ∧ Z = 1) := by
  have := cnt_eq α hirr X Y Z (-1) 1 (by push_cast; linarith)
  omega

theorem sector_pi_minus_beta (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = 3 * α) :
    (X = 3 ∧ Y = 0 ∧ Z = 0) ∨ (X = 1 ∧ Y = 0 ∧ Z = 1) := by
  have := cnt_eq α hirr X Y Z 3 0 (by push_cast; linarith)
  omega

theorem sector_straight (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = Real.pi) :
    (X = 3 ∧ Y = 1 ∧ Z = 0) ∨ (X = 1 ∧ Y = 1 ∧ Z = 1) := by
  have := cnt_eq α hirr X Y Z 0 1 (by push_cast; linarith)
  omega

theorem sector_full (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = 2 * Real.pi) :
    Y = 2 ∧ X + 2 * Z = 6 := by
  have := cnt_eq α hirr X Y Z 0 2 (by push_cast; linarith)
  omega

/-- two `γ`'s never share a straight angle, nor a sector smaller than it (cf. `rGG`, `gamma_alpha_alpha`) -/
theorem straight_at_most_one_gamma (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = Real.pi) : Z ≤ 1 := by
  rcases sector_straight hirr h with ⟨-, -, h3⟩ | ⟨-, -, h3⟩ <;> omega

/-- the figure at an interior point of a side is `{α,β,γ}` or `{α³,β}`: in particular a `γ` is never accompanied by
`α α α` (the latter occurs: real tilings 19600/130977 show only `{α,β,γ}`; both are allowed by the arithmetic) -/
theorem straight_cases (hirr : Irrational (α / Real.pi)) {X Y Z : ℕ}
    (h : (X : ℝ) * α + Y * (Real.pi - 3 * α) + Z * (2 * α) = Real.pi) :
    Y = 1 ∧ X + 2 * Z = 3 := by
  rcases sector_straight hirr h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

/-! ### Witnesses (non-vacuity)

Every sector hypothesis is satisfiable for the genuine angle `α = π √2 / 10` of `APrimeSeat1.straight_vertex_hyp_witness`
(irrational `α/π`, `0 < α`, `3α < π`), e.g. `sector_ab` at `(X,Y,Z) = (1,1,0)`: `α + (π − 3α) = π − 2α` holds by `ring`; the
hypotheses `hirr` of these theorems are discharged by that witness. -/

theorem sector_ab_witness (hirr : Irrational (α / Real.pi)) :
    ((1 : ℕ) : ℝ) * α + ((1 : ℕ) : ℝ) * (Real.pi - 3 * α) + ((0 : ℕ) : ℝ) * (2 * α) = Real.pi - 2 * α := by
  push_cast; ring

end Erdos634.Draft.ThmDRun

#print axioms Erdos634.Draft.ThmDRun.sector_alpha
#print axioms Erdos634.Draft.ThmDRun.sector_beta
#print axioms Erdos634.Draft.ThmDRun.sector_gamma
#print axioms Erdos634.Draft.ThmDRun.sector_ab
#print axioms Erdos634.Draft.ThmDRun.sector_pi_minus_alpha
#print axioms Erdos634.Draft.ThmDRun.sector_pi_minus_beta
#print axioms Erdos634.Draft.ThmDRun.sector_straight
#print axioms Erdos634.Draft.ThmDRun.sector_full
#print axioms Erdos634.Draft.ThmDRun.straight_at_most_one_gamma
#print axioms Erdos634.Draft.ThmDRun.straight_cases
#print axioms Erdos634.Draft.ThmDRun.sector_ab_witness
