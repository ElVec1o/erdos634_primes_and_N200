import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational

/-!
# `ChordWord`: the arithmetic word layer for the π/3 pair (30,6) at N = 60

Tile (a,b,c) = (9+√21, 9−√21, 12) (`c² = a²+b²−ab`, `ab = 60 = N`).  A *word* is `(p,q,r) ∈ ℕ³`
standing for the length `p·a + q·b + r·c`.

* `word_eq_iff`: the irrational split: `p a + q b + r c = p' a + q' b + r' c` iff
  `p − q = p' − q'` and `9(p+q) + 12 r = 9(p'+q') + 12 r'` (uses `√21 ∉ ℚ`).
* The chord lengths, as exact words:
  `chord_c` (`c` is only the single `c`-edge), `chord_2c` (`2c` is exactly two `c`-edges),
  `chord_a_sub_b` (`a − b = 2√21` is not a word), `side60` (side 60: `(0,0,5)` or `(2,2,2)`),
  `chord_a`, `chord_b` (a single `a`/`b` only).
* Comparison with the REAL rational tile (5,8,7) of the N = 1440 equilateral tiling
  (`Draft/G3CEqui60n1440`, 7² = 5²+8²−5·8): the corresponding lengths `7`, `14` have the same unique
  words (checked by `decide` on a bounded box, and unbounded by `omega`), so the analogous
  conclusions for `c` and `2c` are consistent with a real tiling; the irrational split of course does not apply
  there (`a+b ≠ 2c` is the only input the `2c` case needs from the pair `(13,7)`: `13 ≠ 14`).
-/

namespace Erdos634.ChordWord

/-- `√21` is irrational. -/
theorem sqrt21_irrational : Irrational (Real.sqrt 21) := by
  have h : Irrational (Real.sqrt ((21 : ℕ) : ℝ)) :=
    (irrational_sqrt_natCast_iff).mpr (by
      rintro ⟨n, hn⟩
      have h5 : n ≤ 5 := by nlinarith
      interval_cases n <;> omega)
  simpa using h

/-- Coordinates in `ℤ + ℤ√21` are unique. -/
theorem coord_unique (x y x' y' : ℤ)
    (h : (x : ℝ) + y * Real.sqrt 21 = x' + y' * Real.sqrt 21) : x = x' ∧ y = y' := by
  have hy : y = y' := by
    by_contra hne
    have hne' : ((y : ℝ) - y') ≠ 0 := by
      intro h0; apply hne; exact_mod_cast sub_eq_zero.mp h0
    have : Real.sqrt 21 = ((x' : ℝ) - x) / ((y : ℝ) - y') := by
      field_simp; linarith
    apply sqrt21_irrational
    refine ⟨((x' - x : ℤ) : ℚ) / ((y - y' : ℤ) : ℚ), ?_⟩
    rw [this]; push_cast; ring
  subst hy
  refine ⟨?_, rfl⟩
  have : (x : ℝ) = x' := by linarith
  exact_mod_cast this

/-- The three sides of the π/3 tile. -/
noncomputable def sa : ℝ := 9 + Real.sqrt 21
noncomputable def sb : ℝ := 9 - Real.sqrt 21
def sc : ℝ := 12

/-- The tile is a real triangle with `c² = a² + b² − ab` and `ab = 60`. -/
theorem tile_relations : sc ^ 2 = sa ^ 2 + sb ^ 2 - sa * sb ∧ sa * sb = 60 := by
  have h : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  unfold sc sa sb
  constructor <;> nlinarith [h]

/-- The length of the word `(p,q,r)`. -/
noncomputable def wordLen (p q r : ℕ) : ℝ := p * sa + q * sb + r * sc

theorem wordLen_coords (p q r : ℕ) :
    wordLen p q r = ((9 * (p + q) + 12 * r : ℤ) : ℝ) + ((p - q : ℤ) : ℝ) * Real.sqrt 21 := by
  unfold wordLen sa sb sc; push_cast; ring

/-- **(I), the irrational split**, in full form. -/
theorem word_eq_iff (p q r p' q' r' : ℕ) :
    wordLen p q r = wordLen p' q' r' ↔
      ((p : ℤ) - q = (p' : ℤ) - q' ∧ 9 * ((p : ℤ) + q) + 12 * r = 9 * ((p' : ℤ) + q') + 12 * r') := by
  constructor
  · intro h
    rw [wordLen_coords, wordLen_coords] at h
    obtain ⟨h1, h2⟩ := coord_unique _ _ _ _ h
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    rw [wordLen_coords, wordLen_coords, h1, h2]

/-- Length `x + y√21` as a word-comparison target. -/
noncomputable def lenXY (x y : ℤ) : ℝ := (x : ℝ) + y * Real.sqrt 21

theorem wordLen_eq_lenXY_iff (p q r : ℕ) (x y : ℤ) :
    wordLen p q r = lenXY x y ↔ (p : ℤ) - q = y ∧ 9 * ((p : ℤ) + q) + 12 * r = x := by
  rw [wordLen_coords, lenXY]
  constructor
  · intro h; obtain ⟨h1, h2⟩ := coord_unique _ _ _ _ h; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]

/-! ### The chord lengths of T30 -/

/-- **L1.** The chord `PR` has length `c`: it is covered by a single `c`-edge. -/
theorem chord_c (p q r : ℕ) (h : wordLen p q r = sc) : p = 0 ∧ q = 0 ∧ r = 1 := by
  have : wordLen p q r = lenXY 12 0 := by rw [h]; simp [lenXY, sc]
  obtain ⟨h1, h2⟩ := (wordLen_eq_lenXY_iff _ _ _ _ _).mp this
  omega

/-- **L3.** The chord `P₂Q₁` has length `2c`: exactly two `c`-edges. -/
theorem chord_2c (p q r : ℕ) (h : wordLen p q r = 2 * sc) : p = 0 ∧ q = 0 ∧ r = 2 := by
  have : wordLen p q r = lenXY 24 0 := by rw [h]; simp [lenXY, sc]; norm_num
  obtain ⟨h1, h2⟩ := (wordLen_eq_lenXY_iff _ _ _ _ _).mp this
  omega

/-- **L4.** The remainder `a − b = 2√21` of the segment `RZ` is not a word. -/
theorem chord_a_sub_b (p q r : ℕ) : wordLen p q r ≠ sa - sb := by
  intro h
  have : wordLen p q r = lenXY 0 2 := by rw [h]; simp [lenXY, sa, sb]; ring
  obtain ⟨h1, h2⟩ := (wordLen_eq_lenXY_iff _ _ _ _ _).mp this
  omega

/-- A chord of length `a` is a single `a`-edge. -/
theorem chord_a (p q r : ℕ) (h : wordLen p q r = sa) : p = 1 ∧ q = 0 ∧ r = 0 := by
  have : wordLen p q r = lenXY 9 1 := by rw [h]; simp [lenXY, sa]
  obtain ⟨h1, h2⟩ := (wordLen_eq_lenXY_iff _ _ _ _ _).mp this
  omega

/-- A chord of length `b` is a single `b`-edge. -/
theorem chord_b (p q r : ℕ) (h : wordLen p q r = sb) : p = 0 ∧ q = 1 ∧ r = 0 := by
  have : wordLen p q r = lenXY 9 (-1) := by rw [h]; simp [lenXY, sb]; ring
  obtain ⟨h1, h2⟩ := (wordLen_eq_lenXY_iff _ _ _ _ _).mp this
  omega

/-- **Side words at N = 60.**  A side of length 60 is `(0,0,5)` or `(2,2,2)`; with a corner edge
(`p + q ≥ 1`) it is `(2,2,2)`. -/
theorem side60 (p q r : ℕ) (h : wordLen p q r = 60) :
    (p = 0 ∧ q = 0 ∧ r = 5) ∨ (p = 2 ∧ q = 2 ∧ r = 2) := by
  have : wordLen p q r = lenXY 60 0 := by rw [h]; simp [lenXY]
  obtain ⟨h1, h2⟩ := (wordLen_eq_lenXY_iff _ _ _ _ _).mp this
  omega

theorem side60_with_corner (p q r : ℕ) (h : wordLen p q r = 60) (hc : 1 ≤ p + q) :
    p = 2 ∧ q = 2 ∧ r = 2 := by
  rcases side60 p q r h with ⟨h1, h2, _⟩ | h
  · omega
  · exact h

/-- Converse (non-vacuity of the word layer): the words found really have those lengths. -/
theorem wordLen_c : wordLen 0 0 1 = sc := by simp [wordLen]
theorem wordLen_2c : wordLen 0 0 2 = 2 * sc := by simp [wordLen]
theorem wordLen_side : wordLen 2 2 2 = 60 := by
  have := (word_eq_iff 2 2 2 0 0 5).mpr (by omega)
  rw [this]; simp [wordLen, sc]; norm_num

/-- L3's input: `a + b ≠ 2c` (`18 ≠ 24`), the source of "no `a+b` in the chord" there. -/
theorem a_add_b_ne_two_c : sa + sb ≠ 2 * sc := by
  unfold sa sb sc; intro h; linarith

/-! ### Control on the real tile (5,8,7) — the N = 1440 equilateral tiling

Words over ℕ with sides (5,8,7).  Bounded `decide` first, then the unbounded `omega` forms. -/

theorem real_tile_relation : 7 ^ 2 = 5 ^ 2 + 8 ^ 2 - 5 * 8 := by decide

theorem real_decide_7 :
    ∀ p : Fin 3, ∀ q : Fin 2, ∀ r : Fin 3,
      5 * p.val + 8 * q.val + 7 * r.val = 7 → (p.val = 0 ∧ q.val = 0 ∧ r.val = 1) := by decide

theorem real_decide_14 :
    ∀ p : Fin 4, ∀ q : Fin 3, ∀ r : Fin 3,
      5 * p.val + 8 * q.val + 7 * r.val = 14 → (p.val = 0 ∧ q.val = 0 ∧ r.val = 2) := by decide

theorem real_word_7 (p q r : ℕ) (h : 5 * p + 8 * q + 7 * r = 7) : p = 0 ∧ q = 0 ∧ r = 1 := by
  omega

theorem real_word_14 (p q r : ℕ) (h : 5 * p + 8 * q + 7 * r = 14) : p = 0 ∧ q = 0 ∧ r = 2 := by
  omega

/-- On the real tile `a + b = 13 ≠ 14 = 2c`, the same input as `a_add_b_ne_two_c`. -/
theorem real_a_add_b_ne_two_c : 5 + 8 ≠ 2 * 7 := by decide

end Erdos634.ChordWord

#print axioms Erdos634.ChordWord.word_eq_iff
#print axioms Erdos634.ChordWord.chord_c
#print axioms Erdos634.ChordWord.chord_2c
#print axioms Erdos634.ChordWord.chord_a_sub_b
#print axioms Erdos634.ChordWord.side60_with_corner
#print axioms Erdos634.ChordWord.wordLen_side
#print axioms Erdos634.ChordWord.real_word_14
