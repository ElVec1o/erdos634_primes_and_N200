/-
Draft/SideRunGThick.lean  In `AllThreshold`.  Module W1 (second file) of the plan for
`cor:thickw`: **THE COROLLARY**.

PAPER.  `cor:thickw` ("Below the scale `f`, every member: the side `AQ`"): "Let `1 ≤ e < f` be coprime integers, `(a, b, c) = (ef, f² − e², f²)`, and `M ≥ 1`, with the notation of Corollary `cor:ebelow`.
(a) If `M (f − e) ≤ e`, then a segment of length `|AQ| = M f b` that is a union of segments of lengths `a`, `b`, `c` contains at most `M (f − e) ≤ e` of length `c`, and the triangle `W_M(e, f)` cannot be cut into copies of `(a, b, c)`.
(b) For every `f ≥ 2` and every `M ≥ 1`, the triangle `W_M(f − 1, f)` can be cut into copies of `(f (f − 1), 2f − 1, f²)` if and only if `M ≥ f`; the existence is Theorem `thm:residueseeds`.
(c) The triangle `W_2(3, 5)`, with sides `160`, `246`, `250`, cannot be cut into copies of `(15, 16, 25)`."
Proof in the paper: (a) the side `AQ` of `W_M(e, f)` carries at most `e` tiles laying `c`: no run of length `f` and no run of length `e + 1`, against `thm:cornerrun`; (b) for `M ≤ f − 1` this is (a) with `e = f − 1`, for `M ≥ f` the tiling is `Draft.Residue.wTilable_ge`;
(c) the representations of `160` by `15`, `16`, `25` have at most `4` tiles laying `c`, the member has `a = 15 < b = 16` and `A` is a corner `2α`, so `thm:cornerrun` with the addendum gives `5` consecutive tiles laying `c`, or `C1^k`, `k ≥ e + 2 = 5`.

THE FORMS.  Two forms of each part.
* For an ARBITRARY `CongruentDissection` (any number `N` of tiles, reflections allowed) with the target given by its three sides, as `ebelow_a` (`HasSides D₀.target (M f b) (M e (2f² − e²)) (M f³)`, `HasSides D₀.model (ef) (f² − e²) (f²)`): `thickw_a`, `thickw_b` (and `thickw_b_f`, with the numbers of the paper), `thickw_c`.  **`N` is free.**
* For the library predicate `Draft.CollarG.WTilable e f M` (the same triangle, tiles counted: `N = (2f² − e²) M²` is FIXED): `thickw_a_pred`, `thickw_b_pred`, `thickw_c_pred`.
The first sentence of (a) is `thickw_a_count` (natural numbers: `x a + y b + z c = M f b` gives `z ≤ M (f − e)`, `SideRunGArith.C_AQ`).  `thickw_count_tiling` is the counting step: in EVERY tiling of `W_M(e, f)`, any `M`, the side `AQ` is a union of `x`, `y`, `z` segments of
lengths `a`, `b`, `c` with `z ≥ e + 1` (`z ≥ e + 2` if `e + 2 ≤ f` and `a < b`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGThickCount
import Erdos634.Draft.SideRunGArith
import Erdos634.Draft.ResidueSeed

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Set

variable {N : ℕ}

/-- the sides of a triangle, replaced by equal numbers -/
theorem hasSides_of_eq {T : Erdos634.Geometry.Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c)
    (ha : a = a') (hb : b = b') (hc : c = c') : HasSides T a' b' c' := by
  subst ha hb hc
  exact h

/-! ## 1. The counting step -/

/-- **THE COUNTING STEP, for every tiling of `W_M(e, f)`**: in every congruent dissection of the triangle with sides `M f b`, `M e (2f² − e²)`, `M f³` (any number of tiles, reflections allowed) the side `AQ`, of length `M f b`, is a union of `x`, `y`, `z`
segments of lengths `a`, `b`, `c` with `z ≥ e + 1`; and `z ≥ e + 2` if `e + 2 ≤ f` and `a < b` (`thm:cornerrun` and its addendum: the corner `A` is `2α`, the corner `Q` is `α + β`). -/
theorem thickw_count_tiling (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ x y z : ℕ, x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2) ∧ e + 1 ≤ z ∧
      (e + 2 ≤ f → (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 → e + 2 ≤ z) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨hA, hQ, hB⟩ := W_corners_of_sides e f he hef hMr D₀ τ h1 h2 h3
  obtain ⟨x, y, z, hsum, hz1, hz2⟩ := cornerrun_counts e f he hef hco D₀ hMod (rotA.trans τ)
    (Or.inl hA) (Or.inr hQ)
  have hd : dist (D₀.target.pts ((rotA.trans τ) 0)) (D₀.target.pts ((rotA.trans τ) 1)) =
      (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := h2
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
  refine ⟨x, y, z, ?_, hz1, fun h hab => hz2 h hab hA⟩
  have h' : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℝ) =
      ((M * f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
    linear_combination hsum.trans hd
  exact_mod_cast h'

/-! ## 2. Part (a) -/

/-- **`cor:thickw` (a), first sentence** (natural numbers): a segment of length `M f b` that is a union of `x`, `y`, `z` segments of lengths `a`, `b`, `c` contains at most `M (f − e)` of length `c`, when `M (f − e) ≤ e`
(`SideRunGArith.C_AQ`). -/
theorem thickw_a_count {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hMe : M * (f - e) ≤ e)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2)) :
    z ≤ M * (f - e) ∧ M * (f - e) ≤ e :=
  ⟨(SideRunGArith.C_AQ he hef hco h).2 hMe, hMe⟩

/-- **`cor:thickw` (a), second sentence, for an arbitrary congruent dissection** (`N` free): if `M (f − e) ≤ e`, the triangle `W_M(e, f)` (sides `M f (f² − e²)`, `M e (2f² − e²)`, `M f³`) cannot be cut into copies of
`(ef, f² − e², f²)`. -/
theorem thickw_a (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hMe : M * (f - e) ≤ e) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : False := by
  obtain ⟨x, y, z, hN, hz1, -⟩ := thickw_count_tiling e f M he hef hco hM D₀ hT hMod
  have hz2 := (thickw_a_count he hef hco hMe hN).1
  omega

/-- **`cor:thickw` (a) for the project predicate `WTilable e f M`** (`N = (2f² − e²) M²` fixed): if `M (f − e) ≤ e`, `W_M(e, f)` has no tiling. -/
theorem thickw_a_pred (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hMe : M * (f - e) ≤ e) : ¬ Erdos634.Draft.CollarG.WTilable e f M := by
  rintro ⟨D, hT, hMod⟩
  exact thickw_a e f M he hef hco hM hMe D hT hMod

/-! ## 3. Part (b) -/

/-- **`cor:thickw` (b), for an arbitrary congruent dissection** (`N` free): for `f = e + 1` (`e ≥ 1`, that is `f ≥ 2`) and `M ≥ 1`, the triangle `W_M(f − 1, f)` can be cut into copies of `(f (f − 1), 2f − 1, f²) = (ef, f² − e², f²)`
if and only if `M ≥ f`.  (Only if: `thickw_a` with `M (f − e) = M ≤ f − 1 = e`; if: `Draft.Residue.wTilable_ge`.) -/
theorem thickw_b (e f M : ℕ) (he : 1 ≤ e) (hthick : e + 1 = f) (hM : 1 ≤ M) :
    (∃ (N : ℕ) (D₀ : CongruentDissection N),
      HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3) ∧
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) ↔ f ≤ M := by
  have hef : e < f := by omega
  have hco : Nat.Coprime e f := by
    rw [← hthick]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right e)
  constructor
  · rintro ⟨N, D₀, hT, hMod⟩
    by_contra hlt
    have hf1 : f - e = 1 := by omega
    have hMe : M * (f - e) ≤ e := by rw [hf1]; omega
    exact thickw_a e f M he hef hco hM hMe D₀ hT hMod
  · intro hMf
    obtain ⟨D, hT, hMod⟩ := Erdos634.Draft.Residue.wTilable_ge e f he hef hco M hMf
    exact ⟨_, D, hT, hMod⟩

/-- **`cor:thickw` (b), with the numbers of the paper** (`N` free): for `f ≥ 2` and `M ≥ 1` the triangle `W_M(f − 1, f)` (sides `M f (2f − 1)`, `M (f − 1)(f² + 2f − 1)`, `M f³`) can be cut into copies of `(f (f − 1), 2f − 1, f²)` if and only if `M ≥ f`
(`thickw_b` with `e = f − 1`). -/
theorem thickw_b_f (f M : ℕ) (hf : 2 ≤ f) (hM : 1 ≤ M) :
    (∃ (N : ℕ) (D₀ : CongruentDissection N),
      HasSides D₀.target ((M : ℝ) * ((f : ℝ) * (2 * (f : ℝ) - 1)))
        ((M : ℝ) * (((f : ℝ) - 1) * ((f : ℝ) ^ 2 + 2 * (f : ℝ) - 1))) ((M : ℝ) * (f : ℝ) ^ 3) ∧
      HasSides D₀.model ((f : ℝ) * ((f : ℝ) - 1)) (2 * (f : ℝ) - 1) ((f : ℝ) ^ 2)) ↔ f ≤ M := by
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have he : 1 ≤ e := by omega
  have key := thickw_b e (e + 1) M he rfl hM
  constructor
  · rintro ⟨N, D₀, hT, hMod⟩
    exact key.mp ⟨N, D₀, hasSides_of_eq hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
      hasSides_of_eq hMod (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩
  · intro h
    obtain ⟨N, D₀, hT, hMod⟩ := key.mpr h
    exact ⟨N, D₀, hasSides_of_eq hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
      hasSides_of_eq hMod (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩

/-- **`cor:thickw` (b) for the project predicate `WTilable`** (`N = (2f² − e²) M²` fixed): for `f = e + 1`, `M ≥ 1`, `WTilable e f M ↔ f ≤ M`. -/
theorem thickw_b_pred (e f M : ℕ) (he : 1 ≤ e) (hthick : e + 1 = f) (hM : 1 ≤ M) :
    Erdos634.Draft.CollarG.WTilable e f M ↔ f ≤ M := by
  have hef : e < f := by omega
  have hco : Nat.Coprime e f := by
    rw [← hthick]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right e)
  constructor
  · rintro ⟨D, hT, hMod⟩
    exact (thickw_b e f M he hthick hM).mp ⟨_, D, hT, hMod⟩
  · intro hMf
    exact Erdos634.Draft.Residue.wTilable_ge e f he hef hco M hMf

/-! ## 4. Part (c) -/

/-- the representations of `160` by `15`, `16`, `25`: at most `4` of length `25` (`a^9 c`, `a^4 c^4`, `a^2 b^5 c^2`, `b^10`) -/
theorem thickw_c_arith (x y z : ℕ) (h : x * 15 + y * 16 + z * 25 = 160) : z ≤ 4 := by
  by_contra hz
  have hz5 : 5 ≤ z := by omega
  have hz6 : z ≤ 6 := by omega
  have hx : x ≤ 10 := by omega
  have hy : y ≤ 10 := by omega
  interval_cases z <;> interval_cases x <;> omega

/-- the counts of `thickw_count_tiling` at `(e, f, M) = (3, 5, 2)` are impossible -/
theorem thickw_c_counts (x y z : ℕ)
    (hN : x * (3 * 5) + y * (5 ^ 2 - 3 ^ 2) + z * 5 ^ 2 = 2 * 5 * (5 ^ 2 - 3 ^ 2))
    (hz : 3 + 2 ≤ z) : False := by
  have h : x * 15 + y * 16 + z * 25 = 160 := by norm_num at hN; omega
  have := thickw_c_arith x y z h
  omega

/-- **`cor:thickw` (c), for an arbitrary congruent dissection** (`N` free): the triangle `W_2(3, 5)`, with sides `160`, `246`, `250`, cannot be cut into copies of `(15, 16, 25)`. -/
theorem thickw_c (D₀ : CongruentDissection N) (hT : HasSides D₀.target 160 246 250)
    (hMod : HasSides D₀.model 15 16 25) : False := by
  obtain ⟨x, y, z, hN, -, hz⟩ := thickw_count_tiling 3 5 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) D₀ (hasSides_of_eq hT (by norm_num) (by norm_num) (by norm_num))
    (hasSides_of_eq hMod (by norm_num) (by norm_num) (by norm_num))
  exact thickw_c_counts x y z hN (hz (by norm_num) (by norm_num))

/-- **`cor:thickw` (c) for the project predicate `WTilable`** (`N = (2·5² − 3²)·2² = 164` fixed): `¬ WTilable 3 5 2`. -/
theorem thickw_c_pred : ¬ Erdos634.Draft.CollarG.WTilable 3 5 2 := by
  rintro ⟨D, hT, hMod⟩
  obtain ⟨x, y, z, hN, -, hz⟩ := thickw_count_tiling 3 5 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) D hT hMod
  exact thickw_c_counts x y z hN (hz (by norm_num) (by norm_num))

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.thickw_count_tiling
#print axioms Erdos634.Draft.SideRunGA.thickw_a_count
#print axioms Erdos634.Draft.SideRunGA.thickw_a
#print axioms Erdos634.Draft.SideRunGA.thickw_a_pred
#print axioms Erdos634.Draft.SideRunGA.thickw_b
#print axioms Erdos634.Draft.SideRunGA.thickw_b_f
#print axioms Erdos634.Draft.SideRunGA.thickw_b_pred
#print axioms Erdos634.Draft.SideRunGA.thickw_c_arith
#print axioms Erdos634.Draft.SideRunGA.thickw_c
#print axioms Erdos634.Draft.SideRunGA.thickw_c_pred
