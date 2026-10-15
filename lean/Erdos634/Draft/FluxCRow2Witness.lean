-- Draft/FluxCRow2Witness.lean: non-vacuity witness for `Row2.area_scale`, `Row2.lemmaW_square`,
-- `Row2.lemmaW_not_prime` (Draft/FluxCRow2.lean).  Imported by `All`.
--
-- `FluxRow2Witness.D2`: `Subdivision.ladderDissection` of the doubled `(2,3,4)·8` model tile of the
-- 44-tiling, a `CongruentDissection 4` with target `= 2·model` (`D2_sim`, `μ = 2`) and
-- `π ∉ 2Λ` (`D2_pi`, `Λ = ℤπ + ℤθ`, `θ = α/2 + π/2 ∉ ℚπ`).  Every hypothesis is exhibited; the
-- conclusions evaluate to `4 = 2²`, `m = 2`, `¬ Nat.Prime 4`.
-- No Lean dissection with `π ∈ 2Λ` and a tile-similar target is available (e.g. the right isosceles
-- 2-tiling, `N = 2`), so the check that dropping `π ∉ 2Λ` breaks the square conclusion is not made;
-- the area half needs no such hypothesis and holds on every tile-similar target.
import Erdos634.Draft.FluxCRow2
import Erdos634.Draft.FluxRow2Witness

open scoped Classical

namespace Erdos634.Draft.FluxCRow2Witness

open Erdos634.Geometry Erdos634.Draft.FluxRow2Witness

/-- **The area half on a real dissection: `N = 4 = μ²`.** -/
theorem area_scale_D2 : ((2 * 2 : ℕ) : ℝ) = (2 : ℝ) ^ 2 :=
  Row2.area_scale D2 2 (fun k => (D2_sim k).2)

/-- **Lemma W, complete, on a real dissection: `N = m²` with `m = μ = 2`.** -/
theorem lemmaW_square_D2 : ∃ m : ℕ, m = 2 ∧ 2 * 2 = m ^ 2 := by
  obtain ⟨m, h1, h2⟩ := Row2.lemmaW_square D2 2 D2_sim D2_pi
  exact ⟨m, by exact_mod_cast h2.symm, h1⟩

theorem lemmaW_not_prime_D2 : ¬ Nat.Prime (2 * 2) :=
  Row2.lemmaW_not_prime D2 2 D2_sim D2_pi

/-- The real area equation `|det P| = N·|det T|` on `D2` (`N = 4`). -/
theorem abs_detTri_D2 :
    |Erdos634.AreaDet.detTri D2.target| = ((2 * 2 : ℕ) : ℝ) * |Erdos634.AreaDet.detTri D2.model| :=
  D2.abs_detTri_target

end Erdos634.Draft.FluxCRow2Witness

#print axioms Erdos634.Draft.FluxCRow2Witness.area_scale_D2
#print axioms Erdos634.Draft.FluxCRow2Witness.lemmaW_square_D2
#print axioms Erdos634.Draft.FluxCRow2Witness.lemmaW_not_prime_D2
