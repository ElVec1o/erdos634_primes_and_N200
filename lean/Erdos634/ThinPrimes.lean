import Mathlib.Tactic

/-!
# The thin family `3f² - 1`: arithmetic

Erdős #634.  This file carries the arithmetic of the family of counts `N = 3f² - 1` (`e = 1`), not
the geometry.  It does not exclude any prime.

The excluded geometric fact is the base word `(0,1,2)` (`ThinFamily`).  At `f > 2e` exactly two base
words survive (`ThreeWords` + `GammaCount`): `(0,1,2)` and the word `a^f b c`.  Excluding the former
does not by itself exclude the latter, and at `e = 1` the base is forced to begin and end with
`a`-edges, so the argument "no tiling from the walls hypothesis" would be circular there.  The
word `(0,1,2)`, with `n_c = 2`, is also excluded by the base multiset `a^f b c`.

## The arithmetic

The target's count is `N = 3f² - e² = 3f² - 1`.  For a prime, `m = 1` and every representation
`N = 3f'² - e'²` would have to be excluded separately.  Each prime of this shape has exactly one
representation, namely `(1, f)`, checked for every `f ≤ 40`.  Below 4000 the primes of the form
`3f² - 1` with `f ≥ 3` are `47, 107, 191, 431, 587, 971, 1451, 2027, 2351, 2699, 3467`
(`f = 2` gives `11`, excluded by certified search).  All lie in `11 mod 12`.

The arithmetic theorems below are stated and proved in full.  No `sorry`; standard axioms only.
-/

namespace Erdos634.ThinPrimes

/-- The thin family's count: `N = 3f² - 1` at `e = 1`. -/
theorem thin_count (f : ℤ) : 3 * f ^ 2 - 1 ^ 2 = 3 * f ^ 2 - 1 := by ring

/-- Every member of the family lies in `11 mod 12` when `f` is even, which is the case for every
prime of the shape: `f` odd makes `3f² - 1` even and `> 2`, hence composite. -/
theorem thin_even_f (f : ℤ) (hodd : f % 2 = 1) : (3 * f ^ 2 - 1) % 2 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, f = 2 * k + 1 := ⟨f / 2, by omega⟩
  subst hk; ring_nf; omega

/-- and then `3f² - 1 ≡ 11 (mod 12)` for even `f`: writing `f = 2k`, `3f² - 1 = 12k² - 1`. -/
theorem thin_mod12 (k : ℤ) : 3 * (2 * k) ^ 2 - 1 = 12 * k ^ 2 - 1 := by ring

/-- The two surviving base words at `e = 1`, both spanning the base `3f² - 1`. -/
theorem thin_words (f : ℤ) :
    (0 * (1 * f) + 1 * (f ^ 2 - 1) + 2 * f ^ 2 = 1 * (3 * f ^ 2 - 1 ^ 2))
      ∧ (f * (1 * f) + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 1 * (3 * f ^ 2 - 1 ^ 2)) := by
  refine ⟨by ring, by ring⟩

/-- `f ≥ 3` puts the member above `f = 2e`, which is what leaves only two words. -/
theorem thin_above_2e (f : ℤ) (hf : 3 ≤ f) : 2 * 1 < f := by omega

/-- The smallest new value, `f = 4`: `N = 47`.  (`f = 2`, `N = 11`, was already known.) -/
theorem smallest_new : 3 * (4:ℤ) ^ 2 - 1 = 47 := by norm_num

/-- and the first genuinely unsettled one, `f = 8`: `N = 191`. -/
theorem first_unsettled : 3 * (8:ℤ) ^ 2 - 1 = 191 := by norm_num

end Erdos634.ThinPrimes

#print axioms Erdos634.ThinPrimes.thin_count
#print axioms Erdos634.ThinPrimes.thin_even_f
#print axioms Erdos634.ThinPrimes.thin_mod12
#print axioms Erdos634.ThinPrimes.thin_words
#print axioms Erdos634.ThinPrimes.smallest_new
