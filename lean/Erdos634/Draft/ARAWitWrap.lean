import Erdos634.ARAWit

namespace Erdos634.Draft.ARAWitWrap
open Erdos634.ARA
open Erdos634.Geometry

/-- N-form witness at N = 84: exists D with 84 = r²·3·7, r² = 4. -/
theorem wrap_nform_at_84 : ∃ D : CongruentDissection 84, Erdos634.B84.Hyp 1 2 24 42 D ∧
    ∃ r : ℤ, ((84 : ℕ) : ℤ) = r ^ 2 * (2 ^ 2 - 1 ^ 2) * (2 * 2 ^ 2 - 1 ^ 2) ∧ r ^ 2 = 4 :=
  nform_at_84

/-- Atom N-form witness at A4 (48 tiles): exists D with 3·48 = μ², μ = 12, 48 = 3·r², r² = 16. -/
theorem wrap_atom_nform_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    Erdos634.ATDL2.AHyp 1 2 24 12 D ∧ ∃ μ r : ℤ, μ = 12 ∧
      (2 ^ 2 - 1 ^ 2 : ℤ) * ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = μ ^ 2 ∧
      ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = (2 ^ 2 - 1 ^ 2) * r ^ 2 ∧ r ^ 2 = 16 :=
  atom_nform_A4

example : True := trivial

#print axioms wrap_nform_at_84

end Erdos634.Draft.ARAWitWrap
