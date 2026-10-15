import Erdos634.GammaCascade

namespace Erdos634.Draft.GammaCascadeWrap

open Erdos634.GammaCascade

theorem gc_cascade (n : ℕ) (hn : 1 ≤ n) (place : ℕ → ℕ)
    (hplace : ∀ i, 1 ≤ i → i ≤ n → place i = i - 1 ∨ place i = i)
    (hinj : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → place i ≠ place j)
    (hends : ∀ i, 1 ≤ i → i ≤ n → place i ≠ 0 ∧ place i ≠ n) : False :=
  cascade n hn place hplace hinj hends

theorem gc_cascade_witness (n : ℕ) :
    (∀ i, 1 ≤ i → i ≤ n → (fun j => j) i = i - 1 ∨ (fun j => j) i = i) ∧
    (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → (fun k => k) i ≠ (fun k => k) j) :=
  cascade_witness n

example : True := trivial

#print axioms gc_cascade

end Erdos634.Draft.GammaCascadeWrap
