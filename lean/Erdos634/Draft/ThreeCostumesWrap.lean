import Erdos634.A2BranchRow3
import Erdos634.Draft.VacuousCompanionWrap

/-!
# Arithmetic spine of the base run with `e = 1`

Lean content:
1. **`threecostumes_span_all_a`**: a run of k≥f letters totaling f² is exactly f a-edges
   (`A2BranchRow3.span_all_a`).
2. **`threecostumes_row_three_dies`**: the A₂ branch dies at row 3 given the span (`A2BranchRow3.row_three_dies_of_span`).

Only the arithmetic of the `e = 1` case is covered; the geometric statements about the crossing at the column footprint are not formalized here.
0 sorry, standard axioms.
-/

namespace Erdos634.Draft.ThreeCostumesWrap

open Erdos634.A2BranchRow3 Finset

/-- prop:threecostumes (i, span): a base run of k≥f letters summing to f² is all a-edges. -/
theorem threecostumes_span_all_a (f B x y z : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hsum : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z) : y = 0 ∧ z = 0 ∧ x = f :=
  span_all_a f B x y z hf hB hsum hk

/-- prop:threecostumes (i, landing): A₂ branch dies at row 3 given span (row_three_dies_of_span). -/
theorem threecostumes_row_three_dies (f B x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (h0 : isA 0) (hlast : isA (f + 1))
    (hspan : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hAcount : ((range (x + y + z)).filter (fun i => isA (j + i))).card = x) :
    False :=
  row_three_dies_of_span f B x y z j hf hB isA base_count h0 hlast hspan hk hfit hAcount

#print axioms threecostumes_span_all_a
#print axioms threecostumes_row_three_dies

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord in
/-- prop:threecostumes (ii+iii, vacuous): parts (ii) and (iii) hold because no base-β
    tiling exists (basebeta_full_unc). -/
theorem threecostumes_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  Erdos634.Draft.VacuousCompanionWrap.base_beta_false D hco he hef htgt h0 h1 h2

end Erdos634.Draft.ThreeCostumesWrap
