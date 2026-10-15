import Erdos634.Draft.PrimeCharacterization

/-!
# Decidability of the tile-count question (prime case)

It is decidable, given N, whether some triangle can be cut into N congruent triangles.  This module covers prime N only;
the general case needs the classification for composite N.

The prime case follows from `prime_tile_count_iff`:
  ∀ p prime, Nonempty(CongruentDissection p) ↔ (p = 3 ∨ p % 4 ≠ 3)
The right-hand side is a decidable arithmetic condition, so the iff gives decidability.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.DecidableWrap

open Erdos634.Geometry Erdos634.Draft.PrimeCharacterization

/-- thm:decidable (prime case): the tile-count question is decidable for prime N.
Follows immediately from prime_tile_count_iff and decidability of (p = 3 ∨ p % 4 ≠ 3). -/
noncomputable def decidable_prime_tile_count (p : ℕ) (hp : p.Prime) :
    Decidable (Nonempty (CongruentDissection p)) :=
  if h : p = 3 ∨ p % 4 ≠ 3 then
    isTrue ((prime_tile_count_iff p hp).mpr h)
  else
    isFalse fun hD => h ((prime_tile_count_iff p hp).mp hD)

end Erdos634.Draft.DecidableWrap
