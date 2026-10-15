-- No sorry, no native_decide.
-- Instantiation of the two headline statements of Theorem E:
--   `Row5.theoremE_sixty_full`       (FluxCRow5Hr0)          on the 1440-tiling (equilateral, tile (5,8,7)),
--   `Row5.theoremE_twoPiThree_full`  (FluxCRow5TwoPiThreeFull) on the 1215-tiling (equilateral, tile (3,5,7)).
-- Every structural hypothesis (hα, SixtyData / TwoPiThreeData, all target angles = pi/3) is discharged by the
-- G3C premise lemmas; the conclusion `¬ (N.Prime ∧ 3 < N)` is obtained at the concrete N and is true
-- (1440 = 2^5*45, 1215 = 5*3^5), so the premises are jointly satisfiable. The prime-free strengthening
-- (conclusion `False`) is refuted by the same tilings.
import Erdos634.Draft.G3CSixtyControl
import Erdos634.Draft.G3CEqui135Control
import Erdos634.Draft.FluxCRow5Hr0
import Erdos634.Draft.FluxCRow5TwoPiThreeFull

open scoped Classical

namespace Erdos634.Draft.G3HThmE

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

/-- Literal Theorem E, pi/3 branch, applied to the real 1440-tiling. -/
theorem thmE_sixty_1440 :
    ¬ ((Erdos634.Draft.G3CEqui60n1440.cert.leaves.length).Prime ∧
        3 < Erdos634.Draft.G3CEqui60n1440.cert.leaves.length) :=
  Row5Hr0.Row5.theoremE_sixty_full Erdos634.Draft.G3CSixtyControl.D Erdos634.Draft.G3CSixtyControl.α_irr
    Erdos634.Draft.G3CSixtyControl.data Erdos634.Draft.G3CSixtyControl.t_angle

theorem thmE_sixty_1440' : ¬ (Nat.Prime 1440 ∧ 3 < 1440) := by
  have := thmE_sixty_1440
  rwa [Erdos634.Draft.G3CEqui60n1440.cert_len] at this

/-- Literal Theorem E, 2pi/3 branch, applied to the real 1215-tiling. -/
theorem thmE_twoPiThree_1215 :
    ¬ ((Erdos634.Draft.G3CEqui135.cert.leaves.length).Prime ∧
        3 < Erdos634.Draft.G3CEqui135.cert.leaves.length) :=
  Row5TwoPiThreeFull.Row5.theoremE_twoPiThree_full Erdos634.Draft.G3CEqui135Control.D Erdos634.Draft.G3CEqui135Control.α_irr
    Erdos634.Draft.G3CEqui135Control.data Erdos634.Draft.G3CEqui135Control.t_angle

theorem thmE_twoPiThree_1215' : ¬ (Nat.Prime 1215 ∧ 3 < 1215) := by
  have := thmE_twoPiThree_1215
  rwa [Erdos634.Draft.G3CEqui135.cert_len] at this

/-- The prime-free strengthening of Theorem E (pi/3 branch) is refuted by the real 1440-tiling. -/
theorem not_thmE_sixty_primeFree :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), IrrPi α → D.model.SixtyData α a b c →
        Equilateral D → False) := fun h =>
  h _ Erdos634.Draft.G3CSixtyControl.D _ _ _ _ Erdos634.Draft.G3CSixtyControl.α_irr
    Erdos634.Draft.G3CSixtyControl.data Erdos634.Draft.G3CSixtyControl.equilateral

/-- The prime-free strengthening of Theorem E (2pi/3 branch) is refuted by the real 1215-tiling. -/
theorem not_thmE_twoPiThree_primeFree :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c →
        Equilateral D → False) := fun h =>
  h _ Erdos634.Draft.G3CEqui135Control.D _ _ _ _ Erdos634.Draft.G3CEqui135Control.α_irr
    Erdos634.Draft.G3CEqui135Control.data Erdos634.Draft.G3CEqui135Control.equilateral

/-- `Row5.theoremE_full` (both halves, "as written") on both real tilings. -/
theorem thmE_full_1440 : ¬ (Nat.Prime 1440 ∧ 3 < 1440) := by
  have := Row5TwoPiThreeFull.Row5.theoremE_full Erdos634.Draft.G3CSixtyControl.D
    Erdos634.Draft.G3CSixtyControl.α_irr (Or.inl Erdos634.Draft.G3CSixtyControl.data)
    Erdos634.Draft.G3CSixtyControl.t_angle
  rwa [Erdos634.Draft.G3CEqui60n1440.cert_len] at this

theorem thmE_full_1215 : ¬ (Nat.Prime 1215 ∧ 3 < 1215) := by
  have := Row5TwoPiThreeFull.Row5.theoremE_full Erdos634.Draft.G3CEqui135Control.D
    Erdos634.Draft.G3CEqui135Control.α_irr (Or.inr Erdos634.Draft.G3CEqui135Control.data)
    Erdos634.Draft.G3CEqui135Control.t_angle
  rwa [Erdos634.Draft.G3CEqui135.cert_len] at this

end Erdos634.Draft.G3HThmE

#print axioms Erdos634.Draft.G3HThmE.thmE_sixty_1440'
#print axioms Erdos634.Draft.G3HThmE.thmE_twoPiThree_1215'
#print axioms Erdos634.Draft.G3HThmE.not_thmE_sixty_primeFree
#print axioms Erdos634.Draft.G3HThmE.not_thmE_twoPiThree_primeFree
#print axioms Erdos634.Draft.G3HThmE.thmE_full_1440
#print axioms Erdos634.Draft.G3HThmE.thmE_full_1215
