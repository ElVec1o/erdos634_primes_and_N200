/-
Draft/F3All.lean — **the F3 family (angle `2π/3`, `a < b`) for ALL Eisenstein triples**: for naturals `0 < a < b`, `c` with
`c² = a² + a b + b²`, the triangle with sides `(c², 3 b (a + b), c (a + 2 b))` is tiled by `3 (a + b) (a + 2 b)` copies of the tile
`(a, b, c)`, hence `3 (a+b)(a+2b)` is a tile count (and `3 (a+b)(a+2b) k²` for every `k`).

The construction is due to **D. Paliy** (`github.com/DenisUkranian/erdos-634-tilings`, "F3 with a < b": the F4 triangle of
`Draft.F4All` plus an "ideal trapezoid" `T(2ab + b², ab)`, itself a seed `T(a²+b²-a d, ab)` with `d = a+b-c` plus a parallelogram strip);
decoded in `private/ROOM/R8ROWS/src/F3_SMALL_A.md`, `private/ROOM/R8ROWS/src/trap/PROOF.md`, `private/ROOM/R8ROWS/rows.py` (`F3_small`).
What is added here is the symbolic proof (all `a, b, c`) in Lean: twelve regions in the skew Eisenstein frame scaled by `c`, with the
three positive parameters `d = a+b-c`, `y = 2c-a-2b`, `t = b-a` (so `a = 2d+y`, `b = 2d+y+t`, `c = 3d+2y+t`, `3d² = y²+yt`);
the F4 triangle is taken from `Draft.F4All.f4_family_sides` and moved into place by an isometry (SSS).
Generated modules: `F3Defs`, `F3Disj1..4`, `F3Sub`, `F3Tile`, `F3Asm` (generator `private/ROOM/F3ALL/gen.py`); generic layer `F3Core`.

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.F3Asm
import Erdos634.Draft.F4All

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.F3All
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.F3Core Erdos634.Draft.F3Geom
open Erdos634.Draft.S2L (pack_exists)

theorem hHyp (nd ny nt : ℕ) (hnd : 0 < nd) (hny : 0 < ny) (hnt : 0 < nt) (hR : 3 * nd ^ 2 = ny ^ 2 + ny * nt) :
    Hyp (nd : ℝ) (ny : ℝ) (nt : ℝ) :=
  ⟨by exact_mod_cast hnd, by exact_mod_cast hny, by exact_mod_cast hnt, by exact_mod_cast hR⟩

theorem hc_nat (nd ny nt : ℕ) (hR : 3 * nd ^ 2 = ny ^ 2 + ny * nt) :
    (3 * nd + 2 * ny + nt) ^ 2 = (2 * nd + ny) ^ 2 + (2 * nd + ny) * (2 * nd + ny + nt) + (2 * nd + ny + nt) ^ 2 := by
  have hz : 3 * (nd : ℤ) ^ 2 = (ny : ℤ) ^ 2 + ny * nt := by exact_mod_cast hR
  zify
  linear_combination (-1 : ℤ) * hz

theorem sum_cnt (nd ny nt : ℕ) :
    ∑ i, cnt nd ny nt i = 3 * ((2 * nd + ny) + (2 * nd + ny + nt)) * ((2 * nd + ny) + 2 * (2 * nd + ny + nt)) := by
  simp only [cnt]
  rw [Fin.sum_univ_eq_sum_range (fun n => cntN nd ny nt n) 12]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cntN]
  ring

/-- **The F3 layout, real parameters** (`d = nd`, `y = ny`, `t = nt`). -/
theorem f3_real (nd ny nt : ℕ) (hnd : 0 < nd) (hny : 0 < ny) (hnt : 0 < nt) (hR : 3 * nd ^ 2 = ny ^ 2 + ny * nt) :
    ∃ D : CongruentDissection (3 * ((2 * nd + ny) + (2 * nd + ny + nt)) * ((2 * nd + ny) + 2 * (2 * nd + ny + nt))),
      D.model = M3 (hHyp nd ny nt hnd hny hnt hR) ∧ D.target = tgtT (hHyp nd ny nt hnd hny hnt hR) := by
  have H := hHyp nd ny nt hnd hny hnt hR
  obtain ⟨D4, h1, h2, h3, h4, h5, h6⟩ := Erdos634.Draft.F4All.f4_family_sides (2 * nd + ny) (2 * nd + ny + nt)
    (3 * nd + 2 * ny + nt) (by omega) (by omega) (hc_nat nd ny nt hR)
  have hM : D4.model.Congruent (M3 H) := by
    refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · rw [h4, M3_d01 H]; simp only [ea, eb, ec]; push_cast; ring
    · rw [h5, M3_d12 H]; simp only [ea, eb, ec]; push_cast; ring
    · rw [h6, M3_d20 H]; simp only [ea, eb, ec]; push_cast; ring
  obtain ⟨RF4⟩ := f4_geom H D4 hM (by rw [h1]; simp only [ea, eb, ec]; push_cast; ring)
    (by rw [h2]; simp only [ea, eb, ec]; push_cast; ring) (by rw [h3]; simp only [ea, eb, ec]; push_cast; ring)
  have hsum := sum_cnt nd ny nt
  rw [← hsum]
  refine pack_exists (M := M3 H) (T := tgtT H) (regionOf (nd : ℝ) ny nt) (cnt nd ny nt) ?_ (hS_all H) (hsub_all H) ?_
  · exact fun i => match i with
    | ⟨0, _⟩ => RT_T1 H (3 * nd + 2 * ny + nt) (by omega) (by push_cast; ring)
    | ⟨1, _⟩ => RT_T2 H (2 * nd + ny + nt) (by omega) (by push_cast; ring)
    | ⟨2, _⟩ => RT_T3 H (2 * nd + ny + nt) (by omega) (by push_cast; ring)
    | ⟨3, _⟩ => RF4
    | ⟨4, _⟩ => RT_Z1 H nd (by omega) (by push_cast; ring)
    | ⟨5, _⟩ => RT_Z2 H (2 * nd + 2 * ny + nt) nd (by omega) (by omega) (by push_cast; ring) (by push_cast; ring)
    | ⟨6, _⟩ => RT_Z3 H (2 * nd + ny) (by omega) (by push_cast; ring)
    | ⟨7, _⟩ => RT_Z4 H (nd + ny + nt) (by omega) (by push_cast; ring)
    | ⟨8, _⟩ => RT_Z5 H nd (2 * nd + ny + nt) (by omega) (by omega) (by push_cast; ring) (by push_cast; ring)
    | ⟨9, _⟩ => RT_Z6 H (nd + ny) (by omega) (by push_cast; ring)
    | ⟨10, _⟩ => RT_Z7 H (2 * nd + ny + nt) (by omega) (by push_cast; ring)
    | ⟨11, _⟩ => RT_Z8 H (3 * nd + ny + 2 * nt) (2 * nd + ny) (by omega) (by omega) (by push_cast; ring) (by push_cast; ring)
    | ⟨k + 12, h⟩ => absurd h (by omega)
  · apply hvol_all H
    rw [hsum]
    push_cast
    ring

/-! ### the theorems for naturals `0 < a < b`, `c² = a² + ab + b²` -/

/-- the three positive parameters of a triple with `0 < a < b`: `a + b = c + d`, `2 c = a + 2 b + y`, `b = a + t`, `3d² = y² + y t`. -/
theorem params (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ∃ nd ny nt : ℕ, 0 < nd ∧ 0 < ny ∧ 0 < nt ∧ 3 * nd ^ 2 = ny ^ 2 + ny * nt ∧
      a = 2 * nd + ny ∧ b = 2 * nd + ny + nt ∧ c = 3 * nd + 2 * ny + nt := by
  have h1 : c < a + b := by
    by_contra h
    have h' : a + b ≤ c := not_lt.mp h
    nlinarith [Nat.mul_le_mul h' h', Nat.mul_pos ha (by omega : 0 < b)]
  have h2 : a + 2 * b < 2 * c := by
    by_contra h
    have h' : 2 * c ≤ a + 2 * b := not_lt.mp h
    nlinarith [Nat.mul_le_mul h' h', Nat.mul_pos ha ha]
  obtain ⟨nd, hnd⟩ : ∃ nd, a + b = c + nd := ⟨a + b - c, by omega⟩
  obtain ⟨ny, hny⟩ : ∃ ny, 2 * c = a + 2 * b + ny := ⟨2 * c - (a + 2 * b), by omega⟩
  obtain ⟨nt, hnt⟩ : ∃ nt, b = a + nt := ⟨b - a, by omega⟩
  have ea : a = 2 * nd + ny := by omega
  have eb : b = 2 * nd + ny + nt := by omega
  have ec : c = 3 * nd + 2 * ny + nt := by omega
  subst ea eb ec
  refine ⟨nd, ny, nt, by omega, by omega, by omega, ?_, rfl, rfl, rfl⟩
  have hz : ((3 * nd + 2 * ny + nt : ℕ) : ℤ) ^ 2 = ((2 * nd + ny : ℕ) : ℤ) ^ 2 + ((2 * nd + ny : ℕ) : ℤ) * ((2 * nd + ny + nt : ℕ) : ℤ)
      + ((2 * nd + ny + nt : ℕ) : ℤ) ^ 2 := by exact_mod_cast hc
  have : 3 * (nd : ℤ) ^ 2 = (ny : ℤ) ^ 2 + ny * nt := by
    push_cast at hz
    linear_combination (-1 : ℤ) * hz
  exact_mod_cast this

theorem f3_family_dissection (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Nonempty (CongruentDissection (3 * (a + b) * (a + 2 * b))) := by
  obtain ⟨nd, ny, nt, hnd, hny, hnt, hR, rfl, rfl, rfl⟩ := params a b c ha hab hc
  obtain ⟨D, -, -⟩ := f3_real nd ny nt hnd hny hnt hR
  exact ⟨D⟩

/-- **F3 for all Eisenstein triples with `a < b`** (construction of D. Paliy): `3 (a+b)(a+2b)` is a tile count. -/
theorem f3_family (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Erdos634.Draft.TileCountFamilies.TileCount (3 * (a + b) * (a + 2 * b)) :=
  f3_family_dissection a b c ha hab hc

/-- with the side lengths: the target has sides `c·(c², 3b(a+b), c(a+2b))` and the tile `c·(b, a, c)`. -/
theorem f3_family_sides (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ∃ D : CongruentDissection (3 * (a + b) * (a + 2 * b)),
      dist (D.target.pts 0) (D.target.pts 1) = (c : ℝ) * ((c : ℝ) * c) ∧
      dist (D.target.pts 1) (D.target.pts 2) = (c : ℝ) * (3 * (b : ℝ) * ((a : ℝ) + b)) ∧
      dist (D.target.pts 2) (D.target.pts 0) = (c : ℝ) * ((c : ℝ) * ((a : ℝ) + 2 * b)) ∧
      dist (D.model.pts 0) (D.model.pts 1) = (c : ℝ) * b ∧
      dist (D.model.pts 1) (D.model.pts 2) = (c : ℝ) * a ∧
      dist (D.model.pts 2) (D.model.pts 0) = (c : ℝ) * c := by
  obtain ⟨nd, ny, nt, hnd, hny, hnt, hR, rfl, rfl, rfl⟩ := params a b c ha hab hc
  obtain ⟨D, hM, hT⟩ := f3_real nd ny nt hnd hny hnt hR
  have H := hHyp nd ny nt hnd hny hnt hR
  obtain ⟨s1, s2, s3⟩ := sides_tgt H
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, s1]; simp only [ea, eb, ec]; push_cast; ring
  · rw [hT, s2]; simp only [ea, eb, ec]; push_cast; ring
  · rw [hT, s3]; simp only [ea, eb, ec]; push_cast; ring
  · rw [hM, M3_d01 H]; simp only [ea, eb, ec]; push_cast; ring
  · rw [hM, M3_d12 H]; simp only [ea, eb, ec]; push_cast; ring
  · rw [hM, M3_d20 H]; simp only [ea, eb, ec]; push_cast; ring

end Erdos634.Draft.F3All

/-- witness: `(a, b, c) = (11, 24, 31)` gives `3·35·59 = 6195`, the smallest member of the family. -/
theorem Erdos634.Draft.F3All.tileCount_6195 :
    Erdos634.Draft.TileCountFamilies.TileCount 6195 := by
  have := f3_family 11 24 31 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- the `(11, 24, 31)` instance with its side lengths: target `31·(961, 2520, 1829)`, tile `31·(24, 11, 31)`. -/
theorem Erdos634.Draft.F3All.sides_11_24_31 :
    ∃ D : CongruentDissection 6195,
      dist (D.target.pts 0) (D.target.pts 1) = 29791 ∧ dist (D.target.pts 1) (D.target.pts 2) = 78120 ∧
      dist (D.target.pts 2) (D.target.pts 0) = 56699 ∧
      dist (D.model.pts 0) (D.model.pts 1) = 744 ∧ dist (D.model.pts 1) (D.model.pts 2) = 341 ∧
      dist (D.model.pts 2) (D.model.pts 0) = 961 := by
  have h := f3_family_sides 11 24 31 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

#print axioms Erdos634.Draft.F3All.f3_family
#print axioms Erdos634.Draft.F3All.f3_family_sides
#print axioms Erdos634.Draft.F3All.tileCount_6195
#print axioms Erdos634.Draft.F3All.sides_11_24_31
