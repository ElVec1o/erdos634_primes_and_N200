import Erdos634.SpectrumLattice

namespace Erdos634.Draft.SpectrumLatticeWrap
open Erdos634.SpectrumLattice

theorem wrap_admissible_set_eq (e r d a2b g e1 r1 : ℕ) (hg : 0 < g) (he1pos : 0 < e1)
    (he : e = g * e1) (hr : r = g * r1) (hcop : Nat.Coprime e1 r1) :
    {w : ℕ | 0 < w ∧ e ∣ w * r ∧
      ((w * r / e : ℕ) : ZMod 2) = (d : ZMod 2) * (w : ZMod 2) ^ 2 * (a2b : ZMod 2)}
    = {w : ℕ | ∃ u : ℕ, 0 < u ∧
        w = (if (r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2 * (a2b : ZMod 2) = 0
             then e1 else 2 * e1) * u} :=
  admissible_set_eq e r d a2b g e1 r1 hg he1pos he hr hcop

example : True := trivial
#check @wrap_admissible_set_eq

end Erdos634.Draft.SpectrumLatticeWrap
