import Erdos634.CornerRule
import Erdos634.SideNoB

/-!
# The apex lemma: arithmetic cores

The apex lemma has two arithmetic cores:

* `CornerRule.apex_figure`: the apex-figure count equation forces
  (x, y, z) = (3, 0, 0), i.e. only α-tiles.
* `SideNoB.side_no_b_uncond`: the side-walk equation with a γ-tile
  forces Q = 0, i.e. no b-edge tile in the side walk.

Both are pure arithmetic.  The geometric claim, that the apex figure is
accessible and that the walk hypothesis is satisfiable in a real dissection,
requires the placement layer and is not part of this module.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ApexWrap

/-- Apex figure forces (x,y,z) = (3,0,0): the three tiles are all α-tiles. -/
theorem apex_figure_unique (x y z : ℕ)
    (h1 : x + 2 * z = 3) (h2 : y + z = 0) :
    x = 3 ∧ y = 0 ∧ z = 0 :=
  Erdos634.CornerRule.apex_figure x y z h1 h2

/-- Side walk: if a b-edge tile appears in the walk (Q ≥ 1), contradiction with γ present (R ≥ 1). -/
theorem side_no_b_in_walk {e f : ℕ} (b P Q R : ℕ)
    (hco : Nat.Coprime e f) (hef : e < f)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) : Q = 0 :=
  Erdos634.SideNoB.side_no_b_uncond hco hef hb hwalk hgamma

/-- Non-vacuity: apex figure hypotheses are satisfiable. -/
theorem apex_witness : ∃ (x y z : ℕ), x + 2 * z = 3 ∧ y + z = 0 :=
  ⟨3, 0, 0, by norm_num, by norm_num⟩

/-- Non-vacuity: side walk hypotheses are satisfiable. -/
theorem side_walk_witness : ∃ (e f b P Q R : ℕ),
    Nat.Coprime e f ∧ e < f ∧ b + e * e = f * f ∧
    P * (e * f) + Q * b + R * (f * f) = f * f * f ∧ 1 ≤ R :=
  ⟨1, 2, 3, 0, 0, 2,
   by decide, by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms apex_figure_unique
#print axioms side_no_b_in_walk

end Erdos634.Draft.ApexWrap
