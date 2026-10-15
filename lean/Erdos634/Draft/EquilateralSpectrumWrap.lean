import Erdos634.EquilateralSpectrum

namespace Erdos634.Draft.EquilateralSpectrumWrap
open Erdos634.EquilateralSpectrum

theorem wrap_spectrum_union (N : ℕ) :
    inSpectrum N ↔
      ((∃ k, N = k ^ 2) ∨ (∃ k, N = 2 * k ^ 2) ∨ (∃ k, N = 3 * k ^ 2) ∨ (∃ k, N = 6 * k ^ 2)) :=
  spectrum_union N

example : True := trivial
#print axioms wrap_spectrum_union

end Erdos634.Draft.EquilateralSpectrumWrap
