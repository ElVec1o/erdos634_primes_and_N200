import Erdos634.Draft.SumTwoSquares
import Erdos634.Draft.WtoDeltaF
import Erdos634.Draft.BaseBetaFullUnc
import Erdos634.Draft.ColumnLinesGeom

/-!
# The middle region of the walk `(0, e, 2e)` has no tiling

In the `m = 1` base-`β` target of a coprime pair `1 ≤ e < f`, remove the two *dual blocks*, the triangles at the two base corners
that are copies of the tile at scale `e` (base part `e·c = e f²`, side part `e·a = e² f`,
hypotenuse `e·b`).  The remaining middle region (a pentagon: base `e·b`, two dual hypotenuses
`e·b`, two side segments `f·b`, apex `3α`) admits no tiling by copies of the tile.

The region is a Lean object here, and the statement is proved by gluing:

* `Wtri`, `Etri` : the two dual blocks, in the coordinates of `baseBetaTarget e f`;
* `pentagon` : the closure of the target minus the two blocks;
* `W_tiling`, `E_tiling` : each block is tiled by `e²` copies of the tile (the ladder dissection,
  through `SumTwoSquares.ladder_piece`);
* `pentagon_no_tiling` : a tiling of `pentagon` by `n` copies of the tile, for any `n`, glued with
  the tilings of the two blocks (`RegionTiling.union`), is a `CongruentDissection` of the target,
  which `BaseBetaFullUnc.basebeta_full_unc` excludes.

So the proof is the non-existence theorem of the `m = 1`
target, transported to the pentagon.  `pentagon_lengths` records the side lengths of the region.

Standard axioms, no `sorry`.
-/

open scoped Classical
open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
  Erdos634.TilePlacement
open Erdos634.Draft.RegionTiling
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)
open Erdos634.Draft.ColumnLinesGeom (plane_ext base_point_mem)

namespace Erdos634.Draft.PentagonNoTiling

/-! ## Two topological facts -/

theorem union_closure_diff {T A : Set Plane} (hT : IsClosed T) (hA : A ⊆ T) :
    A ∪ closure (T \ A) = T := by
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact hA hx
    · exact (closure_minimal Set.diff_subset hT) hx
  · intro x hx
    by_cases h : x ∈ A
    · exact Or.inl h
    · exact Or.inr (subset_closure ⟨hx, h⟩)

theorem disjoint_interior_closure_diff (T A : Set Plane) :
    Disjoint (interior A) (interior (closure (T \ A))) := by
  rw [Set.disjoint_left]
  intro x hxA hxC
  have hopen : IsOpen (interior A ∩ interior (closure (T \ A))) :=
    isOpen_interior.inter isOpen_interior
  have hxcl : x ∈ closure (T \ A) := interior_subset hxC
  rw [mem_closure_iff] at hxcl
  obtain ⟨y, hy, hyTA⟩ := hxcl _ hopen ⟨hxA, hxC⟩
  exact hyTA.2 (interior_subset hy.1)

/-! ## The two dual blocks -/

theorem detW {e f : ℝ} (he : 0 < e) (hef : e < f) :
    det3 (e * f ^ 2) 0 0 0 (e ^ 2 * baseLen e f / (2 * f ^ 2)) (e ^ 2 * height e f / f ^ 2) ≠ 0 := by
  have hf : 0 < f := lt_trans he hef
  have hH := height_pos he hef
  have : det3 (e * f ^ 2) 0 0 0 (e ^ 2 * baseLen e f / (2 * f ^ 2)) (e ^ 2 * height e f / f ^ 2)
      = -(e ^ 3 * height e f) := by
    unfold det3; field_simp; ring
  rw [this]
  have : 0 < e ^ 3 * height e f := by positivity
  linarith

theorem detE {e f : ℝ} (he : 0 < e) (hef : e < f) :
    det3 (baseLen e f - e * f ^ 2) 0 (baseLen e f) 0
      (baseLen e f - e ^ 2 * baseLen e f / (2 * f ^ 2)) (e ^ 2 * height e f / f ^ 2) ≠ 0 := by
  have hf : 0 < f := lt_trans he hef
  have hH := height_pos he hef
  have : det3 (baseLen e f - e * f ^ 2) 0 (baseLen e f) 0
      (baseLen e f - e ^ 2 * baseLen e f / (2 * f ^ 2)) (e ^ 2 * height e f / f ^ 2)
      = e ^ 3 * height e f := by
    unfold det3; field_simp; ring
  rw [this]
  have : 0 < e ^ 3 * height e f := by positivity
  linarith

/-- The west dual block: vertices `(e f², 0)`, the corner `(0,0)`, and the point of the left side
at distance `e² f` from the corner. -/
noncomputable def Wtri (e f : ℝ) (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (e * f ^ 2) 0 0 0 (e ^ 2 * baseLen e f / (2 * f ^ 2)) (e ^ 2 * height e f / f ^ 2)
    (detW he hef)

/-- The east dual block, the mirror image of the west one. -/
noncomputable def Etri (e f : ℝ) (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (baseLen e f - e * f ^ 2) 0 (baseLen e f) 0
    (baseLen e f - e ^ 2 * baseLen e f / (2 * f ^ 2)) (e ^ 2 * height e f / f ^ 2) (detE he hef)

/-- The middle region: the closure of the target minus the two dual blocks. -/
noncomputable def pentagon (e f : ℝ) (he : 0 < e) (hef : e < f) : Set Plane :=
  closure ((baseBetaTarget e f he hef).carrier \
    ((Wtri e f he hef).carrier ∪ (Etri e f he hef).carrier))

/-- The key squared length: the dual hypotenuse is `e·b`. -/
theorem hyp_sq {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (e ^ 2 * baseLen e f / (2 * f ^ 2) - e * f ^ 2) ^ 2 + (e ^ 2 * height e f / f ^ 2) ^ 2
      = (e * (f ^ 2 - e ^ 2)) ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  have hD : Real.sqrt (Dr e f) ^ 2 = 4 * f ^ 2 - e ^ 2 := sq_sqrtD he hef
  have e1 : e ^ 2 * baseLen e f / (2 * f ^ 2) - e * f ^ 2
      = -(e * (2 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2)) / (2 * f ^ 2) := by
    unfold baseLen Nq; field_simp; ring
  have e2 : e ^ 2 * height e f / f ^ 2
      = e ^ 2 * (f ^ 2 - e ^ 2) * Real.sqrt (Dr e f) / (2 * f ^ 2) := by
    unfold height; ring
  rw [e1, e2, div_pow, div_pow, ← add_div, div_eq_iff (by positivity)]
  linear_combination e ^ 4 * (f ^ 2 - e ^ 2) ^ 2 * hD

/-- The side part: the third vertex is at distance `e² f` from the corner. -/
theorem side_sq {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (e ^ 2 * baseLen e f / (2 * f ^ 2)) ^ 2 + (e ^ 2 * height e f / f ^ 2) ^ 2
      = (e ^ 2 * f) ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  have hD : Real.sqrt (Dr e f) ^ 2 = 4 * f ^ 2 - e ^ 2 := sq_sqrtD he hef
  have e1 : e ^ 2 * baseLen e f / (2 * f ^ 2) = e ^ 3 * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 2) := by
    unfold baseLen Nq; ring
  have e2 : e ^ 2 * height e f / f ^ 2
      = e ^ 2 * (f ^ 2 - e ^ 2) * Real.sqrt (Dr e f) / (2 * f ^ 2) := by
    unfold height; ring
  rw [e1, e2, div_pow, div_pow, ← add_div, div_eq_iff (by positivity)]
  linear_combination e ^ 4 * (f ^ 2 - e ^ 2) ^ 2 * hD

theorem W_d01 {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((Wtri e f he hef).pts 0) ((Wtri e f he hef).pts 1) = e * f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  simp only [Wtri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact Erdos634.Draft.SumTwoSquares.dsq _ _ _ _ _ (by positivity) (by ring)

theorem W_d12 {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((Wtri e f he hef).pts 1) ((Wtri e f he hef).pts 2) = e ^ 2 * f := by
  have hf : 0 < f := lt_trans he hef
  simp only [Wtri, mkTri_pts, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine Erdos634.Draft.SumTwoSquares.dsq _ _ _ _ _ (by positivity) ?_
  rw [← side_sq he hef]; ring

theorem W_d20 {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((Wtri e f he hef).pts 2) ((Wtri e f he hef).pts 0) = e * (f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  simp only [Wtri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine Erdos634.Draft.SumTwoSquares.dsq _ _ _ _ _ (by positivity) ?_
  rw [← hyp_sq he hef]; ring

theorem E_d01 {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((Etri e f he hef).pts 0) ((Etri e f he hef).pts 1) = e * f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  simp only [Etri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact Erdos634.Draft.SumTwoSquares.dsq _ _ _ _ _ (by positivity) (by ring)

theorem E_d12 {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((Etri e f he hef).pts 1) ((Etri e f he hef).pts 2) = e ^ 2 * f := by
  have hf : 0 < f := lt_trans he hef
  simp only [Etri, mkTri_pts, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine Erdos634.Draft.SumTwoSquares.dsq _ _ _ _ _ (by positivity) ?_
  rw [← side_sq he hef]; ring

theorem E_d20 {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((Etri e f he hef).pts 2) ((Etri e f he hef).pts 0) = e * (f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  simp only [Etri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine Erdos634.Draft.SumTwoSquares.dsq _ _ _ _ _ (by positivity) ?_
  rw [← hyp_sq he hef]; ring

/-! ## The blocks lie in the target and are separated -/

theorem third_le {e f : ℝ} (he : 0 < e) (hef : e < f) :
    e ^ 2 * baseLen e f / (2 * f ^ 2) ≤ e * f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  rw [div_le_iff₀ (by positivity)]
  unfold baseLen Nq
  have h1 : 0 ≤ (2 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  nlinarith [mul_nonneg he.le h1]

theorem gap_pos {e f : ℝ} (he : 0 < e) (hef : e < f) :
    e * f ^ 2 < baseLen e f - e * f ^ 2 := by
  unfold baseLen Nq
  have h2 : e ^ 2 < f ^ 2 := by nlinarith
  nlinarith [mul_pos he (sub_pos.mpr h2)]

theorem W_left {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (Wtri e f he hef).carrier ⊆ {q : Plane | q 0 ≤ e * f ^ 2} := by
  have hf : 0 < f := lt_trans he hef
  have hconv : Convex ℝ {q : Plane | q 0 ≤ e * f ^ 2} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hx0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    rw [hx0]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  refine convexHull_min ?_ hconv
  rintro _ ⟨k, rfl⟩
  have h3 := third_le he hef
  have hpos : 0 ≤ e * f ^ 2 := by positivity
  fin_cases k <;> simp [Wtri, mkTri_pts, mkPt_zero] <;> first | exact h3 | exact hpos | linarith | skip

theorem E_right {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (Etri e f he hef).carrier ⊆ {q : Plane | baseLen e f - e * f ^ 2 ≤ q 0} := by
  have hf : 0 < f := lt_trans he hef
  have hconv : Convex ℝ {q : Plane | baseLen e f - e * f ^ 2 ≤ q 0} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hx0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    rw [hx0]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  refine convexHull_min ?_ hconv
  rintro _ ⟨k, rfl⟩
  have h3 := third_le he hef
  have hpos : 0 ≤ e * f ^ 2 := by positivity
  fin_cases k <;> simp [Etri, mkTri_pts, mkPt_zero] <;> first | exact h3 | exact hpos | linarith | skip

theorem WE_disjoint {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Disjoint (interior (Wtri e f he hef).carrier) (interior (Etri e f he hef).carrier) := by
  rw [Set.disjoint_left]
  intro x hxW hxE
  have h1 : x 0 ≤ e * f ^ 2 := W_left he hef (interior_subset hxW)
  have h2 : baseLen e f - e * f ^ 2 ≤ x 0 := E_right he hef (interior_subset hxE)
  have := gap_pos he hef
  linarith

theorem pts_mem (T : Tri) (k : Fin 3) : T.pts k ∈ T.carrier :=
  subset_convexHull ℝ _ ⟨k, rfl⟩

theorem seg_sub (T : Tri) (i j : Fin 3) : segment ℝ (T.pts i) (T.pts j) ⊆ T.carrier :=
  (convex_convexHull ℝ _).segment_subset (pts_mem T i) (pts_mem T j)

theorem W_subset {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (Wtri e f he hef).carrier ⊆ (baseBetaTarget e f he hef).carrier := by
  have hf : 0 < f := lt_trans he hef
  have hL := baseLen_pos he hef
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · -- `(e f², 0)` on the base
    have hle : e * f ^ 2 ≤ baseLen e f := by
      have := gap_pos he hef
      have : 0 < e * f ^ 2 := by positivity
      linarith
    exact seg_sub _ 0 1 (base_point_mem he hef (by positivity) hle)
  · -- the corner
    have h0 : (Wtri e f he hef).pts 1 = (baseBetaTarget e f he hef).pts 0 := by
      simp [Wtri, mkTri_pts]
    show (Wtri e f he hef).pts 1 ∈ _
    rw [h0]; exact pts_mem _ 0
  · -- the point of the left side
    apply seg_sub _ 0 2
    refine ⟨1 - e ^ 2 / f ^ 2, e ^ 2 / f ^ 2, ?_, by positivity, by ring, ?_⟩
    · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · apply plane_ext
      · simp [Wtri, mkTri_pts]; field_simp
      · simp [Wtri, mkTri_pts]; field_simp

theorem E_subset {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (Etri e f he hef).carrier ⊆ (baseBetaTarget e f he hef).carrier := by
  have hf : 0 < f := lt_trans he hef
  have hL := baseLen_pos he hef
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · -- `(L − e f², 0)` on the base
    have h1 := gap_pos he hef
    have h2 : 0 < e * f ^ 2 := by positivity
    exact seg_sub _ 0 1 (base_point_mem he hef (by linarith) (by linarith))
  · -- the corner
    have h0 : (Etri e f he hef).pts 1 = (baseBetaTarget e f he hef).pts 1 := by
      simp [Etri, mkTri_pts]
    show (Etri e f he hef).pts 1 ∈ _
    rw [h0]; exact pts_mem _ 1
  · -- the point of the right side
    apply seg_sub _ 1 2
    refine ⟨1 - e ^ 2 / f ^ 2, e ^ 2 / f ^ 2, ?_, by positivity, by ring, ?_⟩
    · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · apply plane_ext
      · simp [Etri, mkTri_pts]; field_simp; ring
      · simp [Etri, mkTri_pts]; field_simp

/-! ## The blocks are tiled by `e²` copies of the tile -/

theorem model_sides (M : Tri) {a b c : ℝ} (h0 : sideOpp M 0 = a) (h1 : sideOpp M 1 = b)
    (h2 : sideOpp M 2 = c) :
    dist (M.pts 0) (M.pts 1) = c ∧ dist (M.pts 1) (M.pts 2) = a ∧ dist (M.pts 2) (M.pts 0) = b :=
  ⟨h2, h0, h1⟩

theorem W_tiling {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (M : Tri)
    (h0 : sideOpp M 0 = (e : ℝ) * f) (h1 : sideOpp M 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp M 2 = (f : ℝ) ^ 2) :
    Nonempty (RTiling (Wtri (e : ℝ) f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast hef)).carrier M (e * e * 1)) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hef' : (e : ℝ) < f := by exact_mod_cast hef
  obtain ⟨m01, m12, m20⟩ := model_sides M h0 h1 h2
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Draft.SumTwoSquares.ladder_piece M M
    (Wtri (e : ℝ) f he' hef') e (by omega) (Tri.Congruent.refl _)
    (by rw [W_d01 he' hef', m01]) (by rw [W_d12 he' hef', m12]; ring)
    (by rw [W_d20 he' hef', m20])
  exact Erdos634.Draft.WtoDeltaF.seed_of_cd E _ M hEt (by rw [hEm]; exact Tri.Congruent.refl _)

theorem E_tiling {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (M : Tri)
    (h0 : sideOpp M 0 = (e : ℝ) * f) (h1 : sideOpp M 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp M 2 = (f : ℝ) ^ 2) :
    Nonempty (RTiling (Etri (e : ℝ) f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast hef)).carrier M (e * e * 1)) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hef' : (e : ℝ) < f := by exact_mod_cast hef
  obtain ⟨m01, m12, m20⟩ := model_sides M h0 h1 h2
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Draft.SumTwoSquares.ladder_piece M M
    (Etri (e : ℝ) f he' hef') e (by omega) (Tri.Congruent.refl _)
    (by rw [E_d01 he' hef', m01]) (by rw [E_d12 he' hef', m12]; ring)
    (by rw [E_d20 he' hef', m20])
  exact Erdos634.Draft.WtoDeltaF.seed_of_cd E _ M hEt (by rw [hEm]; exact Tri.Congruent.refl _)

/-! ## The lemma -/

/-- **`lem:pentagon`.**  For coprime `1 ≤ e < f` and a tile `M` with sides `(e f, f² − e², f²)`,
the middle region of the `m = 1` base-`β` target (the closure of the target minus the two dual
blocks) has no tiling by congruent copies of `M`, with any number `n` of tiles. -/
theorem pentagon_no_tiling {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) (M : Tri)
    (h0 : sideOpp M 0 = (e : ℝ) * f) (h1 : sideOpp M 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp M 2 = (f : ℝ) ^ 2) (n : ℕ) :
    IsEmpty (RTiling (pentagon (e : ℝ) f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast hef)) M n) := by
  refine ⟨fun RP => ?_⟩
  have he' : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hef' : (e : ℝ) < f := by exact_mod_cast hef
  obtain ⟨RW⟩ := W_tiling he hef M h0 h1 h2
  obtain ⟨RE⟩ := E_tiling he hef M h0 h1 h2
  have U1 := union RW RE (WE_disjoint he' hef')
  have U2 := union U1 RP (disjoint_interior_closure_diff _ _)
  have hcov : ((Wtri (e : ℝ) f he' hef').carrier ∪ (Etri (e : ℝ) f he' hef').carrier) ∪
      pentagon (e : ℝ) f he' hef' = (baseBetaTarget (e : ℝ) f he' hef').carrier :=
    union_closure_diff (baseBetaTarget (e : ℝ) f he' hef').isCompact.isClosed
      (Set.union_subset (W_subset he' hef') (E_subset he' hef'))
  let D : CongruentDissection (e * e * 1 + e * e * 1 + n) := toCD (RTiling.cast hcov U2)
  exact Erdos634.Draft.BaseBetaFullUnc.basebeta_full_unc D hco he hef (Tri.Congruent.refl _)
    h0 h1 h2

/-- The side lengths of the middle region: its base is `e·b`, each dual hypotenuse is `e·b`
(`W_d20`, `E_d20`), and each side segment is `f·b`, where `b = f² − e²`. -/
theorem pentagon_lengths {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (baseLen e f - e * f ^ 2) - e * f ^ 2 = e * (f ^ 2 - e ^ 2) ∧
    f ^ 3 - e ^ 2 * f = f * (f ^ 2 - e ^ 2) ∧
    dist ((Wtri e f he hef).pts 2) ((Wtri e f he hef).pts 0) = e * (f ^ 2 - e ^ 2) ∧
    dist ((Etri e f he hef).pts 2) ((Etri e f he hef).pts 0) = e * (f ^ 2 - e ^ 2) := by
  refine ⟨by unfold baseLen Nq; ring, by ring, W_d20 he hef, E_d20 he hef⟩

end Erdos634.Draft.PentagonNoTiling
