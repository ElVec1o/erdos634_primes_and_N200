-- Draft/PropReductionFull.lean
-- The reduction statement for ALL prime N ≥ 2 (2π/3-tile, IrrPi).
--
-- Combines:
--   * PropReductionN3.tp_prime_excluded_ge3  — prime N ≥ 3, any target → False  (0 extra axioms)
--   * PropReductionN2.tp_two_excluded         — N = 2 → False (corner-angle counting; no axiom)
--
-- Statement:
--   "Let T be a tile with angles (α, β, 2π/3), α/π irrational.  If T N-tiles a triangle
--    and N is prime, then ABC is isosceles and not equilateral."
-- Lean proves False (stronger); the conclusion follows by False.elim.
-- Standard axioms only, for every prime N.
--
-- NOTE: this file imports FluxCRow12, which has a large transitive import closure.

import Erdos634.Draft.PropReductionN3
import Erdos634.Draft.PropReductionN2
import Erdos634.TPTwoTiles
import Erdos634.Draft.FluxCRow12

open scoped Classical
open Real
open Erdos634.Geometry Erdos634.FCTwoTiles Erdos634.TPTwoTiles
open Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.PropReductionN3

namespace Erdos634.Draft.PropReductionFull

/-- **N = 2 is impossible for a 2π/3-tile with irrational angle.**  No axiom: the former plane-topology
    axiom `two_piece_cut_of_twoPiThree` is REMOVED; this is `PropReductionN2.tp_two_excluded` (corner-angle counting +
    the tile-similar exclusion). -/
theorem tp_two_excluded (D : CongruentDissection 2) {α a b c : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) : False :=
  Erdos634.Draft.PropReductionN2.tp_two_excluded D hirr hm

/-- **The reduction for ALL prime N ≥ 2.**
    For any prime N and a 2π/3-tile with irrational angle, any target → False.
    The paper statement (ABC isosceles and not equilateral) follows by `False.elim`.
    - N ≥ 3: `tp_prime_excluded_ge3` (standard axioms only).
    - N = 2: `PropReductionN2.tp_two_excluded` (standard axioms only). -/
theorem tp_prime_excluded_all {N : ℕ} (D : CongruentDissection N) (hN : N.Prime)
    {α a b c : ℝ} (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) : False := by
  by_cases h2 : N = 2
  · subst h2
    exact tp_two_excluded D hirr hm
  · have h3 : 3 ≤ N := by
      have h2le : 2 ≤ N := hN.two_le
      omega
    exact tp_prime_excluded_ge3 D hN h3 hirr hm

#check @tp_prime_excluded_all
#print axioms tp_prime_excluded_all

/-- **`prop:reduction`, as written in the paper**: a tile with angles `(α, β, 2π/3)`, `α/π` irrational, that `N`-tiles a
    triangle with `N` prime forces the triangle to be isosceles and not equilateral.  (The hypotheses are in fact
    inconsistent: `tp_prime_excluded_all`; so the statement holds vacuously, and this is recorded in the paper tag.) -/
theorem prop_reduction {N : ℕ} (D : CongruentDissection N) (hN : N.Prime)
    {α a b c : ℝ} (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) :
    (∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) ∧
      ¬ (∀ i, D.target.angleAt i = Real.pi / 3) :=
  (tp_prime_excluded_all D hN hirr hm).elim

end Erdos634.Draft.PropReductionFull

#print axioms Erdos634.Draft.PropReductionFull.prop_reduction
