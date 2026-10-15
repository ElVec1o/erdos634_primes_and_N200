import Erdos634.ChordFinsetPrependInj

namespace Erdos634.Draft.ChordFinsetPrependInjWrap
open Erdos634.ChordTraceReal

theorem wrap_injective_prepend_two {Plane : Type*} {g_old : ℕ → Plane} {B : ℕ} {p r : Plane}
    (hinj_old : ∀ a b, a ≤ B → b ≤ B → a ≠ b → g_old a ≠ g_old b)
    (hpr : p ≠ r)
    (hp_old : ∀ i, i ≤ B → p ≠ g_old i)
    (hr_old : ∀ i, i ≤ B → r ≠ g_old i) :
    ∀ a b, a ≤ B + 2 → b ≤ B + 2 → a ≠ b →
      (fun i => if i = 0 then p else if i = 1 then r else g_old (i - 2)) a
        ≠ (fun i => if i = 0 then p else if i = 1 then r else g_old (i - 2)) b :=
  injective_prepend_two hinj_old hpr hp_old hr_old

example : True := trivial
#check @wrap_injective_prepend_two

end Erdos634.Draft.ChordFinsetPrependInjWrap
