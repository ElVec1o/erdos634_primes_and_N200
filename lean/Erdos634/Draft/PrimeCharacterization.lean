-- Draft/PrimeCharacterization.lean — a prime p is the tile count of a congruent-triangle
-- dissection of a triangle iff p = 3 or p % 4 ≠ 3 (i.e. p = 2, p = 3, or p ≡ 1 mod 4).
-- Existence: Fermat (PrimeArithmetic) + SumTwoSquares, and Equilateral3.  Exclusion: theoremP_6.
-- Imported by All.lean.
import Erdos634.Draft.TheoremP6
import Erdos634.Draft.SumTwoSquares
import Erdos634.Draft.Equilateral3
import Erdos634.PrimeArithmetic

namespace Erdos634.Draft.PrimeCharacterization
open Erdos634.Geometry

theorem prime_tile_count_iff (p : ℕ) (hp : p.Prime) :
    Nonempty (CongruentDissection p) ↔ (p = 3 ∨ p % 4 ≠ 3) := by
  constructor
  · rintro ⟨D⟩
    by_contra h
    push Not at h
    exact Erdos634.Draft.TheoremP6.theoremP_6 p D hp h.2 (by
      have := hp.two_le; omega)
  · rintro (rfl | h4)
    · exact Erdos634.Draft.Equilateral3.exists_dissection_3
    · obtain ⟨e, f, he, hf, hef⟩ := Erdos634.PrimeArithmetic.prime_sum_two_pos_squares p hp h4
      have := Erdos634.Draft.SumTwoSquares.sum_two_squares_tiling e f he hf
      rwa [show e * e + f * f = p by rw [← hef]; ring] at this

end Erdos634.Draft.PrimeCharacterization

#print axioms Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff
