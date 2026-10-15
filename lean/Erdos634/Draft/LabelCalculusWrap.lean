import Erdos634.LabelCalculus
namespace Erdos634.Draft.LabelCalculusWrap
open Erdos634.LabelCalculus

theorem wrap_label_shift (x y : ℤ) : L (x + 3) (y + 2) = L x y :=
  label_shift x y

theorem wrap_label_ker (x y : ℤ) : L x y = 0 ↔ ∃ k : ℤ, x = 3 * k ∧ y = 2 * k :=
  label_ker x y

theorem wrap_label_surjective (n : ℤ) : L (2 * n) n = n :=
  label_surjective n

theorem wrap_label_target_sides : L 0 0 = 0 ∧ L 0 1 = -3 ∧ L 0 (-1) = 3 :=
  label_target_sides

theorem wrap_label_tile_angles : L 1 0 = 2 ∧ L 0 1 = -3 ∧ L 2 1 = 1 :=
  label_tile_angles

theorem wrap_alpha_is_two_gamma : L 1 0 = 2 * L 2 1 :=
  alpha_is_two_gamma

theorem wrap_beta_is_neg_three_gamma : L 0 1 = -3 * L 2 1 :=
  beta_is_neg_three_gamma

example : True := trivial
#print axioms wrap_label_shift
end Erdos634.Draft.LabelCalculusWrap
