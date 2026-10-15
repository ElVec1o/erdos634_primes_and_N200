import Erdos634.Crux1

/-!
# Crux1: ladder crux arithmetic, wrapper

Key results:
- `crux1_clears_four_two`: the (4,2) descent is impossible
- `four_two_is_the_level`: (4,2) and its reflection are the only escapes at level R+2
- `interior_level_area_not_integral`: interior level lines have non-integral area
- `endpoint_systems_solvable`: endpoint angle systems are always solvable
- `endpoint_systems_solvable_gamma`: endpoint systems also have γ-bearing solutions
- `column_fits_bound`: column footprint fit bound (j ≤ f - f/3)

No sorry, standard axioms.
-/

namespace Erdos634.Draft.Crux1Wrap

open Erdos634.Crux1

theorem cx1_crux1_clears_four_two (f B x y z j : ℕ) (hf : 3 ≤ f) (hB : B + 1 = f * f)
    (hspan : x * f + y * B + z * (B + 1) = B + 1)
    (hk : f ≤ x + y + z)
    (hfit : j + (x + y + z) ≤ f + 2)
    (hletters : ∀ i, i < x + y + z → A2BranchRow3.isA42 (j + i)) :
    False :=
  crux1_clears_four_two f B x y z j hf hB hspan hk hfit hletters

theorem cx1_four_two_is_the_level {R bp cp : ℕ} (hR : 4 ≤ R)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ R + 2) (hc2 : 2 ≤ cp) (hcf : cp ≤ R + 3) (hne : bp ≠ cp)
    (hesc : ¬ PincerLadder.Kill (R + 2) bp cp R) :
    (bp = 4 ∧ cp = 2) ∨ (bp = R + 1 ∧ cp = R + 3) :=
  four_two_is_the_level hR hb3 hbf hc2 hcf hne hesc

theorem cx1_interior_level_area_not_integral {N f u : ℕ} (hf : 0 < f) (hcop : Nat.Coprime N f)
    (h1 : 1 ≤ u) (h2 : u < f) : ¬ (f ^ 4 ∣ N * (f * u) ^ 2) :=
  interior_level_area_not_integral hf hcop h1 h2

theorem cx1_endpoint_systems_solvable :
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 2) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 2 ∧ nb + ng = 2) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 1) :=
  endpoint_systems_solvable

theorem cx1_endpoint_systems_solvable_gamma :
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 2 ∧ ng = 1) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 2 ∧ nb + ng = 2 ∧ ng = 1) ∧
    (∃ na nb ng : ℕ, na + 2 * ng = 3 ∧ nb + ng = 1 ∧ ng = 1) :=
  endpoint_systems_solvable_gamma

theorem cx1_column_fits_bound (f u Y : ℕ) (hf : 3 ≤ f) (hY : Y + 1 = 3 * f ^ 2)
    (hfit : f ^ 3 ≤ Y * u) : f ≤ 3 * u :=
  column_fits_bound f u Y hf hY hfit

-- Non-vacuity: f=5, u=2, Y=74 → 5^3=125 ≤ 74*2=148, so 5 ≤ 6
example : 5 ≤ 3 * 2 := cx1_column_fits_bound 5 2 74 (by norm_num) (by norm_num) (by norm_num)

#print axioms cx1_crux1_clears_four_two
#print axioms cx1_four_two_is_the_level
#print axioms cx1_endpoint_systems_solvable

end Erdos634.Draft.Crux1Wrap
