import Erdos634.CevianUnique
namespace Erdos634.Draft.CevianUniqueWrap
open Erdos634.CevianUnique

theorem wrap_rival_absent_by_length :
    (1:ℤ) * (3 * 4 ^ 2 - 1 ^ 2) < 4 ^ 3 ∧
    (1:ℤ) * (3 * 6 ^ 2 - 1 ^ 2) < 6 ^ 3 ∧
    (1:ℤ) * (3 * 8 ^ 2 - 1 ^ 2) < 8 ^ 3 ∧
    (2:ℤ) * (3 * 9 ^ 2 - 2 ^ 2) < 9 ^ 3 :=
  rival_absent_by_length

theorem wrap_rival_absent_by_semigroup :
    (∀ i j k : Fin 2, ¬ (10 * (i:ℕ) + 21 * (j:ℕ) + 25 * (k:ℕ) = 17)) ∧
    (∀ i j k : Fin 3, ¬ (36 * (i:ℕ) + 65 * (j:ℕ) + 81 * (k:ℕ) = 179)) :=
  rival_absent_by_semigroup

theorem wrap_rival_present_at_83 :
    (216:ℤ) ≤ 415 ∧ 216 = 6 * 36 ∧ 415 - 216 = 5 * 11 + 4 * 36 :=
  rival_present_at_83

example : True := trivial
#print axioms wrap_rival_absent_by_length
end Erdos634.Draft.CevianUniqueWrap
