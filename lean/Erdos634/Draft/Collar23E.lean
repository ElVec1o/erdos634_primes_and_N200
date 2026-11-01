-- Draft/Collar23E.lean -- (2,3) collar, part E: the collar STEP  T(g) tiled by 5g^2 copies of (4,5,6)  ==>  T(g+1) tiled by 5(g+1)^2, for all g >= 2;
-- induction, exit to `CongruentDissection`, `TileCount`, corollary from a seed.  UNAUDITED.  No sorry, no native_decide.  NOT imported by All.
-- Credit: B. Herdt (the 1125-tiling by (4,5,6): the seed template), Beeson-Rosu, Paliy; the strip/cap/slice structure is the project's AI assistant P1
-- (internal working notes).  T(g) is the isosceles triangle with base 15g, legs 10g, base angles alpha (cos alpha = 3/4).
import Erdos634.Draft.Collar23D
import Erdos634.Draft.TileCountFamilies

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)
open Erdos634.Draft.S2L (hull_le hull_ge mem_hull3')
open Erdos634.Draft.TileCountFamilies (TileCount)

namespace Erdos634.Draft.Collar23

theorem T_union_Z (m : ℝ) : Tset23 m ∪ Zset m = Tset23 (m + 1) := by
  ext z
  simp only [Tset23, Zset, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, by linarith⟩
    · exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases h : 2 * z.1 + 3 * z.2 ≤ 30 * m
    · left; exact ⟨h1, h2, h⟩
    · right; rw [not_le] at h; exact ⟨h1, h2, h.le, by linarith⟩

/-- `T(g)` is tiled by `5 g^2` copies of the model tile (4,5,6). -/
def Tile23 (g : ℕ) : Prop := Nonempty (RTiling (Phi '' Tset23 (g : ℝ)) M23 (5 * (g * g)))

/-- **(iii) The collar step.**  `T(g)` tiled by `5g^2` copies of (4,5,6)  ==>  `T(g+1)` tiled by `5(g+1)^2`, for every `g >= 2`. -/
theorem tile23_succ (g : ℕ) (hg : 2 ≤ g) (h : Tile23 g) : Tile23 (g + 1) := by
  obtain ⟨R⟩ := h
  obtain ⟨a, b, hab⟩ := exists_ab g hg
  have hr : 2 * (a : ℝ) + 3 * (b : ℝ) + 4 = 5 * (g : ℝ) := by exact_mod_cast hab
  have Z := ZRT (g : ℝ) a b hr
  have hd : Disjoint (interior (Phi '' Tset23 (g : ℝ))) (interior (Phi '' Zset (g : ℝ))) := by
    refine disjoint_image (interior_disj_lin (-2) (-3) (-(30 * (g : ℝ))) (by norm_num) ?_ ?_)
    · rintro p ⟨h1, h2, h3⟩; linarith
    · rintro p ⟨h1, h2, h3, h4⟩; linarith
  have U := union R Z hd
  refine ⟨RTiling.castN ?_ (RTiling.cast ?_ U)⟩
  · have h1 : 4 * a + 13 + 6 * b = 2 * (5 * g) + 5 := by omega
    rw [h1]; ring
  · rw [← Set.image_union, T_union_Z]; push_cast; rfl

/-- **(iii) Induction**: from any `T(g1)`, `g1 >= 2`, every `T(g)`, `g >= g1`. -/
theorem tile23_up (g1 : ℕ) (h1 : 2 ≤ g1) (T1 : Tile23 g1) : ∀ g, g1 ≤ g → Tile23 g := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => exact T1
  | succ n hn ih => exact tile23_succ n (le_trans h1 hn) ih

/-! ## Exit to `CongruentDissection` -/

theorem Tset23_convex (m : ℝ) : Convex ℝ (Tset23 m) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  show 0 ≤ (a • x + b • y).1 ∧ 0 ≤ (a • x + b • y).2 ∧ 2 * (a • x + b • y).1 + 3 * (a • x + b • y).2 ≤ 30 * m
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]

theorem Tset23_eq_hull (m : ℝ) (hm : 0 < m) :
    Tset23 m = convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (15 * m, 0), (0, 10 * m)} : Set (ℝ × ℝ)) := by
  apply Set.Subset.antisymm
  · rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    refine mem_hull3' (A := ((0 : ℝ), (0 : ℝ))) (B := (15 * m, 0)) (C := (0, 10 * m)) (30 * m)
      (30 * m - 2 * x - 3 * y) (2 * x) (3 * y) (by linarith) (by linarith) (by linarith) (by linarith)
      (by ring) (x, y) ?_ ?_
    · simp only; ring
    · simp only; ring
  · refine convexHull_min ?_ (Tset23_convex m)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨le_refl _, le_refl _, by simp; linarith⟩
    · exact ⟨by linarith, le_refl _, by simp; linarith⟩
    · exact ⟨le_refl _, by linarith, by simp; linarith⟩

theorem cr_T (g : ℝ) (hg : 0 < g) : cr ((0 : ℝ), (0 : ℝ)) (15 * g, 0) (0, 10 * g) ≠ 0 := by
  simp only [cr]; nlinarith [mul_pos hg hg]

/-- The target triangle `T(g)`: vertices `Phi(0,0)`, `Phi(15 g, 0)`, `Phi(0, 10 g)`. -/
noncomputable def tri23 (g : ℝ) (hg : 0 < g) : Tri := TT (0, 0) (15 * g, 0) (0, 10 * g) (cr_T g hg)

theorem tri23_carrier (g : ℝ) (hg : 0 < g) : (tri23 g hg).carrier = Phi '' Tset23 g := by
  unfold tri23
  rw [TT_carrier, Tset23_eq_hull g hg]

/-- **Exit**: a tiling of `T(g)` in the frame is a genuine `CongruentDissection` of the triangle `tri23 g` with model `M23`. -/
theorem tile23_dissection (g : ℕ) (hg : 0 < g) (h : Tile23 g) :
    ∃ D : CongruentDissection (5 * (g * g)), D.target = tri23 (g : ℝ) (by exact_mod_cast hg) ∧ D.model = M23 := by
  obtain ⟨R⟩ := h
  have hpos : (0 : ℝ) < g := by exact_mod_cast hg
  have R' : RTiling (tri23 (g : ℝ) hpos).carrier M23 (5 * (g * g)) :=
    RTiling.cast (tri23_carrier _ hpos).symm R
  exact ⟨toCD R', rfl, rfl⟩

/-- the other direction: a `CongruentDissection` of `tri23 g` with model `M23` is a frame tiling. -/
theorem tile23_of_dissection (g : ℕ) (hg : 0 < g) (D : CongruentDissection (5 * (g * g)))
    (ht : D.target = tri23 (g : ℝ) (by exact_mod_cast hg)) (hm : D.model = M23) : Tile23 g := by
  have hpos : (0 : ℝ) < g := by exact_mod_cast hg
  have R := ofCD D
  rw [ht, hm] at R
  exact ⟨RTiling.cast (tri23_carrier _ hpos) R⟩

/-- **More generally, any `CongruentDissection` whose target is congruent to `T(g)` and whose model is congruent to the
tile (4,5,6)** (any position, any orientation, reflections allowed) gives a frame tiling. -/
theorem tile23_of_congruent (g : ℕ) (hg : 0 < g) (D : CongruentDissection (5 * (g * g)))
    (ht : D.target.Congruent (tri23 (g : ℝ) (by exact_mod_cast hg))) (hm : D.model.Congruent M23) : Tile23 g := by
  have hpos : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨f, σ, hf⟩ := ht
  have R := Erdos634.Draft.RegionTiling.map (ofCD D) f
  have hc := Erdos634.CongruentArea.image_carrier_of_congruent hf
  have R2 := remodel R hm
  exact ⟨RTiling.cast (hc.trans (tri23_carrier _ hpos)) R2⟩

/-- **The family theorem.**  If `T(g1)` is tiled by `5 g1^2` copies of (4,5,6) (`g1 >= 2`), then for every `g >= g1` the number
`5 g^2` is a tile count.  The target is the isosceles triangle with base `15 g`, legs `10 g`, model the tile (4,5,6). -/
theorem collar23_family (g1 : ℕ) (h1 : 2 ≤ g1) (T1 : Tile23 g1) (g : ℕ) (hg : g1 ≤ g) (hg0 : 0 < g) :
    ∃ D : CongruentDissection (5 * (g * g)),
      D.target = tri23 (g : ℝ) (by exact_mod_cast hg0) ∧ D.model = M23 :=
  tile23_dissection g hg0 (tile23_up g1 h1 T1 g hg)

theorem collar23_tileCount (g1 : ℕ) (h1 : 2 ≤ g1) (T1 : Tile23 g1) (g : ℕ) (hg : g1 ≤ g) :
    TileCount (5 * (g * g)) := by
  obtain ⟨D, -, -⟩ := collar23_family g1 h1 T1 g hg (by omega)
  exact ⟨D⟩

/-- **(iv) The corollary from the Herdt/engine seed `T(12)` (720 tiles).**  The seed itself is NOT in the corpus; this is conditional on it. -/
theorem collar23_from_T12 (T12 : Tile23 12) (g : ℕ) (hg : 12 ≤ g) : TileCount (5 * (g * g)) :=
  collar23_tileCount 12 (by norm_num) T12 g hg

/-! ## Non-vacuity of the step: the strip region dissection alone, for several `g` -/

theorem Z_witness_values :
    Nonempty (RTiling (Phi '' Zset 2) M23 25) ∧ Nonempty (RTiling (Phi '' Zset 3) M23 35) ∧
    Nonempty (RTiling (Phi '' Zset 4) M23 45) ∧ Nonempty (RTiling (Phi '' Zset 5) M23 55) ∧
    Nonempty (RTiling (Phi '' Zset 6) M23 65) ∧ Nonempty (RTiling (Phi '' Zset 11) M23 115) ∧
    Nonempty (RTiling (Phi '' Zset 13) M23 135) ∧ Nonempty (RTiling (Phi '' Zset 40) M23 405) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Z_tiling 2 (by norm_num)).map (fun R => by simpa using R)
  · exact (Z_tiling 3 (by norm_num)).map (fun R => by simpa using R)
  · exact (Z_tiling 4 (by norm_num)).map (fun R => by simpa using R)
  · exact (Z_tiling 5 (by norm_num)).map (fun R => by simpa using R)
  · exact (Z_tiling 6 (by norm_num)).map (fun R => by simpa using R)
  · exact (Z_tiling 11 (by norm_num)).map (fun R => by simpa using R)
  · exact (Z_tiling 13 (by norm_num)).map (fun R => by simpa using R)
  · exact (Z_tiling 40 (by norm_num)).map (fun R => by simpa using R)


/-! ## The model is the tile (4,5,6); negative controls -/

theorem M23_sq : dist (M23.pts 0) (M23.pts 1) ^ 2 = 25 ∧ dist (M23.pts 1) (M23.pts 2) ^ 2 = 36 ∧
    dist (M23.pts 2) (M23.pts 0) ^ 2 = 16 := by
  have e : M23.pts = ![Phi (pt modelZT.a), Phi (pt modelZT.b), Phi (pt modelZT.c)] := rfl
  rw [e]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩ <;> rw [dist_sq_Phi] <;> simp [pt, modelZT] <;> norm_num

/-- **The model tile has side lengths 5, 6, 4** (the tile `(4,5,6)` in the order (01,12,20)): `Phi` has unit basis vectors. -/
theorem M23_dist : dist (M23.pts 0) (M23.pts 1) = 5 ∧ dist (M23.pts 1) (M23.pts 2) = 6 ∧
    dist (M23.pts 2) (M23.pts 0) = 4 := by
  obtain ⟨a, b, c⟩ := M23_sq
  refine ⟨eq_of_sq_eq' dist_nonneg (by norm_num) (by rw [a]; norm_num),
    eq_of_sq_eq' dist_nonneg (by norm_num) (by rw [b]; norm_num),
    eq_of_sq_eq' dist_nonneg (by norm_num) (by rw [c]; norm_num)⟩

/-- **(iii) in `CongruentDissection` form**: a congruent dissection of `T(g)` (target congruent to `tri23 g`, tiles congruent to the
tile (4,5,6) = `M23`, `N = 5 g^2`) gives one of `T(g+1)`, `g >= 2`. -/
theorem collar23_step_CD (g : ℕ) (hg : 2 ≤ g) (D : CongruentDissection (5 * (g * g)))
    (ht : D.target.Congruent (tri23 (g : ℝ) (by exact_mod_cast (by omega : 0 < g))))
    (hm : D.model.Congruent M23) :
    ∃ D' : CongruentDissection (5 * ((g + 1) * (g + 1))),
      D'.target = tri23 ((g + 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 0 < g + 1)) ∧ D'.model = M23 :=
  tile23_dissection (g + 1) (by omega) (tile23_succ g hg (tile23_of_congruent g (by omega) D ht hm))

theorem neg_control_sep : ¬ sep (capTab 0) (capTab 0) := by decide
theorem neg_control_model : ¬ (⟨(0, 0), (0, 5), (6, -3)⟩ : ZT).model := by decide
theorem neg_control_in : ¬ inR capReg (0, 11) := by decide
theorem neg_control_deg : ¬ (⟨(0, 0), (1, 1), (2, 2)⟩ : ZT).nd := by decide

end Erdos634.Draft.Collar23

#print axioms Erdos634.Draft.Collar23.tile23_succ
#print axioms Erdos634.Draft.Collar23.tile23_up
#print axioms Erdos634.Draft.Collar23.collar23_family
#print axioms Erdos634.Draft.Collar23.collar23_tileCount
#print axioms Erdos634.Draft.Collar23.collar23_from_T12
#print axioms Erdos634.Draft.Collar23.tile23_of_congruent
#print axioms Erdos634.Draft.Collar23.Z_witness_values
#print axioms Erdos634.Draft.Collar23.M23_dist
#print axioms Erdos634.Draft.Collar23.collar23_step_CD
#print axioms Erdos634.Draft.Collar23.neg_control_sep
