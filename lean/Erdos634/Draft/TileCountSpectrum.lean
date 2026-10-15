-- Corollaries assembling the existence families with theoremP_6:
-- 7 m² and 11 m² are tile counts (of some triangle by some tile) exactly when m ≥ 2.
-- The m = 1 halves are theoremP_6 (7, 11 are primes ≡ 3 mod 4).
import Erdos634.Draft.PrimeCharacterization
import Erdos634.Draft.WFamily
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.TileCountSpectrum
open Erdos634.Draft.TileCountFamilies

theorem not_tileCount_prime {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) : ¬ TileCount p :=
  fun ⟨D⟩ => Erdos634.Draft.TheoremP6.theoremP_6 p D hp h4 h3

theorem tileCount_seven_sq_iff {m : ℕ} (hm : 1 ≤ m) : TileCount (7 * (m * m)) ↔ 2 ≤ m := by
  constructor
  · intro h
    by_contra hlt
    have : m = 1 := by omega
    subst this
    exact not_tileCount_prime (p := 7) (by norm_num) (by norm_num) (by norm_num) (by simpa using h)
  · exact Erdos634.Draft.WFamily.tileCount_seven_sq

theorem tileCount_eleven_sq_iff {m : ℕ} (hm : 1 ≤ m) : TileCount (11 * (m * m)) ↔ 2 ≤ m := by
  constructor
  · intro h
    by_contra hlt
    have : m = 1 := by omega
    subst this
    exact not_tileCount_prime (p := 11) (by norm_num) (by norm_num) (by norm_num) (by simpa using h)
  · exact tileCount_eleven_sq

end Erdos634.Draft.TileCountSpectrum

#print axioms Erdos634.Draft.TileCountSpectrum.tileCount_seven_sq_iff
#print axioms Erdos634.Draft.TileCountSpectrum.tileCount_eleven_sq_iff
