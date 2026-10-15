import Erdos634.Inflation

/-!
# The inflated boundary at (1,3): arithmetic kernel

At the (1,3) member (tile (3,8,9)), the inflated tile's
boundary middles are completely determined. Three tile-sides-words of given sums have
unique decompositions:

1. **`middle_three`**: a word of (1,3)-sides summing to 3 is exactly [3] (one a-edge).
2. **`middle_eight`**: a word summing to 8 is exactly [8] (one b-edge).
3. **`middle_nine`**: a word summing to 9 is exactly [9] or [3,3,3] (c or a^3).
4. **`residual_245`**: 21x+40y+49z=245 has exactly two solutions (0,0,5) and (7,0,2).

These words are middles of specific sides of a real inflated dissection. The geometric input
(each corner takes one tile, its edges lie along the sides) is not proved in this module.

Word/decomposition arithmetic only: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.InflBdyWrap

open Erdos634.Inflation

/-- Middle of inflated a-side: a (1,3)-sides-word summing to 3 is exactly [3]. -/
theorem inflbdy_middle_three (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 3) :
    w = [3] :=
  middle_three w h hs

/-- Middle of inflated b-side: a word summing to 8 is exactly [8]. -/
theorem inflbdy_middle_eight (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 8) :
    w = [8] :=
  middle_eight w h hs

/-- Middle of inflated c-side: a word summing to 9 is [9] or [3,3,3]. -/
theorem inflbdy_middle_nine (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 9) :
    w = [9] ∨ w = [3, 3, 3] :=
  middle_nine w h hs

/-- Residual 245: 21x+40y+49z=245 ⟹ (0,0,5) or (7,0,2). -/
theorem inflbdy_residual_245 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 245) :
    (x = 0 ∧ y = 0 ∧ z = 5) ∨ (x = 7 ∧ y = 0 ∧ z = 2) :=
  residual_245 x y z h

/-- Non-vacuity for middle_three: [3] is a (1,3)-sides-word summing to 3. -/
theorem inflbdy_middle_three_witness :
    (∀ x ∈ ([3] : List ℕ), isSide x) ∧ ([3] : List ℕ).sum = 3 := by
  constructor
  · intro x hx; simp at hx; subst hx; exact Or.inl rfl
  · norm_num

/-- cor:inflcrux (arithmetic certificate): the crux tile area 49 < 138 = f²·N-unit.
    `inflation_smaller_37` in Inflation.lean; 0 axioms (decide). -/
theorem inflcrux_smaller_37 : (49 : ℕ) < 138 :=
  inflation_smaller_37

#print axioms inflbdy_middle_three
#print axioms inflbdy_residual_245
#print axioms inflcrux_smaller_37

end Erdos634.Draft.InflBdyWrap
