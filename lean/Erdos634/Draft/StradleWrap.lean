import Erdos634.ChordDecomp

/-!
# Area arithmetic for junction chords

Every junction chord is straddled; the arithmetic part is:

* `ChordDecomp.area_not_integral`: ¬ (2401 ∣ 138·n²) for 1 ≤ n ≤ 48.
* `ChordDecomp.admissible_range`: the admissible heights 3i+7j satisfy this.

Both are decidable finite arithmetic checks.  The geometric conclusion
(some tile meets both open sides of the chord) is not stated in Lean.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.StradleWrap

/-- For any admissible junction height 1 ≤ n ≤ 48: 2401 does not divide 138·n². -/
theorem straddle_area_gap (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 48) :
    ¬ (2401 ∣ 138 * n ^ 2) :=
  Erdos634.ChordDecomp.area_not_integral n h1 h2

/-- The heights 3i + 7j (i ≤ 7, j ≤ 4, 1 ≤ 3i+7j < 49) also satisfy the gap. -/
theorem straddle_admissible_heights {i j : ℕ} (hi : i ≤ 7) (hj : j ≤ 4)
    (hpos : 1 ≤ 3 * i + 7 * j) (hlt : 3 * i + 7 * j < 49) :
    ¬ (2401 ∣ 138 * (3 * i + 7 * j) ^ 2) :=
  Erdos634.ChordDecomp.admissible_range hi hj hpos hlt

/-- Non-vacuity: n = 1 satisfies the hypotheses. -/
theorem straddle_witness : ∃ n : ℕ, 1 ≤ n ∧ n ≤ 48 ∧ ¬ (2401 ∣ 138 * n ^ 2) :=
  ⟨1, by norm_num, by norm_num, straddle_area_gap 1 (by norm_num) (by norm_num)⟩

#print axioms straddle_area_gap
#print axioms straddle_admissible_heights

end Erdos634.Draft.StradleWrap
