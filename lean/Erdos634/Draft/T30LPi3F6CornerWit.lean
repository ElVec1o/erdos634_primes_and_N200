import Mathlib.Tactic
import Erdos634.Draft.T30LPi3F6Corner

/-!
# Witness for `corner_far_reflection` on the 1440-tiling

`G3CSixtyControl.D` (equilateral side `240·3360 = 806400`, tile `(5,8,7)·3360`, `α ∉ ℚπ`): every hypothesis of `corner_far_reflection`
is discharged (word lemma `5x+8y+7z = 7 → x+y+z = 1` by `omega`, sides `806400 ∉ {16800, 26880}`), at each of the three corners.  The conclusion is then a
statement about the real tiling: the tile across the corner tile's `c`-edge is its point reflection.

`word_fails_12`: `5x+8y+7z = 12` has the word `(1,0,1)` with `x+y+z = 2`, so the single-edge hypothesis is not automatic.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry Erdos634.Draft.G3CSixtyControl Erdos634.Pi3Tile

theorem hword_1440 (x y z : ℕ)
    (h : (x : ℝ) * (3360 * 5) + y * (3360 * 8) + z * (3360 * 7) = 3360 * 7) : x + y + z = 1 := by
  have h' : (5 * x + 8 * y + 7 * z : ℕ) = 7 := by
    have : ((5 * x + 8 * y + 7 * z : ℕ) : ℝ) = 7 := by push_cast; linarith
    exact_mod_cast this
  omega

theorem tside (k : Fin 3) : dist (D.target.pts k) (D.target.pts (k + 1)) = 806400 := by
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have h : D.target.oppLen (k + 2) = 806400 := by
    fin_cases k
    · exact t_opp2
    · exact t_opp0
    · exact t_opp1
  unfold Tri.oppLen at h
  rw [e4, e5] at h
  exact h

theorem tside2 (k : Fin 3) : dist (D.target.pts k) (D.target.pts (k + 2)) = 806400 := by
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  have h : D.target.oppLen (k + 1) = 806400 := by
    fin_cases k
    · exact t_opp1
    · exact t_opp2
    · exact t_opp0
  unfold Tri.oppLen at h
  rw [e3, e6] at h
  rw [dist_comm]; exact h

/-- **WITNESS.**  On the real 1440-tiling, at every corner, the tile across the corner tile's `c`-edge is the point reflection of the corner tile. -/
theorem witness_corner_far_reflection (k : Fin 3) :
    ∃ i j, (D.tile i).pts j = D.target.pts k ∧
      ∃ j', j' ≠ i ∧ ∃ X : Plane,
        (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
        (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
          (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} :=
  corner_far_reflection D (hirr := α_irr) data (by norm_num) (by norm_num) hword_1440 k (t_angle k)
    (by rw [tside]; norm_num) (by rw [tside]; norm_num) (by rw [tside2]; norm_num) (by rw [tside2]; norm_num)

/-- **Control.**  The single-edge word lemma is not automatic on the rational tile `(5,8,7)`: the length `12` has the word `(1,0,1)`
(`5 + 7`) with `x + y + z = 2 ≠ 1`. -/
theorem word_fails_12 : ∃ x y z : ℕ, 5 * x + 8 * y + 7 * z = 12 ∧ x + y + z ≠ 1 := ⟨1, 0, 1, by norm_num, by norm_num⟩

end Erdos634.Pi3F6

#print axioms Erdos634.Pi3F6.corner_far_reflection
#print axioms Erdos634.Pi3F6.witness_corner_far_reflection
