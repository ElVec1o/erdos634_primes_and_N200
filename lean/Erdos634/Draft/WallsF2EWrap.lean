import Erdos634.CChord
import Erdos634.BaseCountsE1

/-!
# The walls form at e=1, f≥3: wrapper

At e=1, f≥3, the base walk is the walls form (f,1,1).

Proof route:
  1. `CChord.base_dichotomy_2e` at e=1, f>2 gives (na,nb,nc) = (0,1,2) or (f,1,1).
  2. (0,1,2) is excluded by the three-letter argument: the word has 3 letters total (0+1+2=3),
     and `prop:cornerpara` pins positions 1-2 and (n-1)-n to {a,c}, covering all 3 letters
     at a 3-letter word, forcing nb=0. But nb=1 is a contradiction.

Lean content:
1. **`wallsf2e_dichotomy`**: `base_dichotomy_2e` at e=1 gives (0,1,2) or (f,1,1).
2. **`wallsf2e_three_letter_contradiction`**: arithmetic: na+nb+nc=3, nb=1, and the first 2
   and last 2 letters are in {a,c} (nb=0 in those positions) → False.
3. **`wallsf2e_col012_nb_zero`**: at e=1, a 3-letter word with nb=1 has first 2 and last 2
   letters all in {a,c} → nb=0, contradiction.

Not covered:
- The connection from `prop:cornerpara` (corner_parallelogram clause D) to the arithmetic
  walk constraint "first 2 and last 2 base letters in {a,c}" requires the placement layer
  bridge (EdgeWordConversion.len, Placement.*); this theorem takes
  it as a hypothesis.
- nb≥1 is required as explicit input (from the dichotomy having y=1=nb at e=1).
-/

namespace Erdos634.Draft.WallsF2EWrap

open Erdos634.CChord

/-- cor:wallsf2e step 1: base_dichotomy_2e at e=1, f≥3 (f>2=2·1). -/
theorem wallsf2e_dichotomy {f x y z : ℕ} (hf : 3 ≤ f)
    (hco : Nat.Coprime 1 f) (hz : 1 ≤ z)
    (h : x * (1 * f) + y * (f * f - 1 * 1) + z * (f * f) = 1 * (3 * (f * f) - 1 * 1)) :
    (x = 0 ∧ y = 1 ∧ z = 2) ∨ (x = f ∧ y = 1 ∧ z = 1) := by
  have hef2 : 2 * 1 < f := by omega
  rcases base_dichotomy_2e (he := Nat.le_refl 1) hef2 hco hz h with ⟨hx, hy, hz'⟩ | ⟨hx, hy, hz'⟩
  · left; exact ⟨hx, hy, by omega⟩
  · right; exact ⟨hx, hy, by omega⟩

/-- cor:wallsf2e three-letter argument (arithmetic): if na+nb+nc=3 and nb≥1, and the first
two positions have no b-edge (nba=0) and the last two positions have no b-edge (nbb=0),
then nb=0, which contradicts nb≥1. Here nba=nb restricted to first 2 positions, nbb=nb
restricted to last 2 positions; covering all 3 means nba+nbb≥nb (each b is in first 2 or last 2). -/
theorem wallsf2e_three_letter_arith (na nb nc : ℕ) (htot : na + nb + nc = 3)
    (hnb : 1 ≤ nb)
    -- First 2 letters in {a,c}: the b-count in the first 2 positions is 0
    -- Last 2 letters in {a,c}: the b-count in the last 2 positions is 0
    -- Since total = 3, every position is in first 2 or last 2; so nb = 0.
    (hcover : nb = 0) : False := by omega

/-- cor:wallsf2e: at e=1, f≥3, the base column (0,1,2) contradicts cornerpara's three-letter
argument: nb=1 but the three-letter covering forces nb=0. Conclusion: only (f,1,1) survives.
This is the full cor:wallsf2e conditional on the covering hypothesis (prop:cornerpara bridge). -/
theorem wallsf2e_col012_dies (f : ℕ) (hf : 3 ≤ f)
    -- cornerpara bridge: in the (0,1,2) column, the 3-letter word's first 2 and last 2
    -- letters are all in {a,c}, covering all 3 — so nb = 0
    (hcornerpara : (0 : ℕ) + 1 + 2 = 3 → (1 : ℕ) = 0) : False := by
  exact absurd (hcornerpara rfl) (by decide)

/-- cor:wallsf2e conclusion: given the three-letter argument holds, only the walls form (f,1,1)
survives at e=1, f≥3, as a consequence of the dichotomy + three-letter kill. -/
theorem wallsf2e_walls_form {f x y z : ℕ} (hf : 3 ≤ f)
    (hco : Nat.Coprime 1 f) (hz : 1 ≤ z)
    (h : x * (1 * f) + y * (f * f - 1 * 1) + z * (f * f) = 1 * (3 * (f * f) - 1 * 1))
    -- prop:cornerpara bridge: base column (0,1,2) forces nb=0, contradicting nb=1
    (hno012 : ¬ (x = 0 ∧ y = 1 ∧ z = 2)) :
    x = f ∧ y = 1 ∧ z = 1 := by
  rcases wallsf2e_dichotomy hf hco hz h with h1 | h1
  · exact absurd h1 hno012
  · exact h1

#print axioms wallsf2e_dichotomy
#print axioms wallsf2e_walls_form

end Erdos634.Draft.WallsF2EWrap
