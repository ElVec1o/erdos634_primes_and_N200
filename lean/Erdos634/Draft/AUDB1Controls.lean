-- Sanity examples for the semantic core of the prime theorem
-- (Plane, Tri, Tri.carrier, Dissection, Tri.Congruent, CongruentDissection, cornerAngle, localAngle,
-- the statements of theoremP_6 / prime_tile_count_iff).
-- Not imported by `All`.  No sorry, no native_decide.
import Erdos634.Draft.PrimeCharacterization
import Erdos634.Draft.S2GControls
import Erdos634.Draft.CutGen
import Erdos634.Draft.RWGlue
import Erdos634.Draft.RWEast
import Erdos634.Ladder
import Erdos634.CongruentArea
import Erdos634.AngleSumDissection
import Erdos634.Tiling44Bridge
import Erdos634.Tiling99Bridge
import Erdos634.R84TilingBridge
import Erdos634.R88TilingBridge
import Erdos634.R126TilingBridge
import Erdos634.S2RTilingBridge

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SumTwoSquares MeasureTheory

namespace Erdos634.AUDB1

/-! ## 0. The ambient metric is the Euclidean (L2) one, not sup -/

/-- `dist (0,0) (3,4) = 5`: `Plane = EuclideanSpace ℝ (Fin 2)` carries the L2 distance (a sup-norm
plane would give 4).  So `Tri.Congruent`'s `Plane ≃ᵢ Plane` is the Euclidean isometry group. -/
theorem plane_dist_is_L2 : dist (mkPt 0 0) (mkPt 3 4) = 5 :=
  dsq 0 0 3 4 5 (by norm_num) (by norm_num)

/-! ## 1. Basic coordinate triangles -/

theorem detT0 : det3 0 0 1 0 0 1 ≠ 0 := by unfold det3; norm_num
noncomputable def T0 : Tri := mkTri 0 0 1 0 0 1 detT0     -- right isosceles, legs 1

/-- generic: ladder of any tile `T` by `k` is a `CongruentDissection (k*k*1)`. -/
theorem ladder_nonempty (T : Tri) (k : ℕ) (hk : 0 < k) : Nonempty (CongruentDissection (k * k * 1)) := by
  obtain ⟨hind, heta⟩ := Erdos634.Draft.RWEast.tri_eta T
  set D0 : CongruentDissection 1 :=
    { toDissection := Erdos634.RouteOneCrossing.selfDissection T, model := T,
      tiles_congruent := fun _ => Tri.Congruent.refl T }
  obtain ⟨E, -, -⟩ := Erdos634.Ladder.ladder (T.pts 0) (T.pts 1) (T.pts 2) hind D0 heta k hk
  exact ⟨E⟩

/-! ## 2. POSITIVE controls: `Nonempty (CongruentDissection N)` at the exact `N` -/

theorem N1 : Nonempty (CongruentDissection 1) := by
  have : Nonempty (CongruentDissection (1 * 1 * 1)) := ladder_nonempty T0 1 (by norm_num)
  exact this
theorem N2 : Nonempty (CongruentDissection 2) :=
  Erdos634.Draft.PrimeWitness2.exists_prime_dissection.1
theorem N3 : Nonempty (CongruentDissection 3) := Erdos634.Draft.Equilateral3.exists_dissection_3
theorem N4 : Nonempty (CongruentDissection 4) := by
  have : Nonempty (CongruentDissection (2 * 2 * 1)) := ladder_nonempty T0 2 (by norm_num)
  exact this
theorem N5 : Nonempty (CongruentDissection 5) := by
  have := sum_two_squares_tiling 1 2 (by norm_num) (by norm_num); exact this
theorem N8 : Nonempty (CongruentDissection 8) := by
  have := sum_two_squares_tiling 2 2 (by norm_num) (by norm_num); exact this
theorem N9 : Nonempty (CongruentDissection 9) := by
  have : Nonempty (CongruentDissection (3 * 3 * 1)) := ladder_nonempty T0 3 (by norm_num)
  exact this
theorem N13 : Nonempty (CongruentDissection 13) := by
  have := sum_two_squares_tiling 2 3 (by norm_num) (by norm_num); exact this
theorem N44 : Nonempty (CongruentDissection 44) := by
  obtain ⟨E, -⟩ := Erdos634.Tiling44Bridge.exists_dissection_44_mul_sq 1 (by norm_num)
  exact ⟨by simpa using E⟩
theorem N77 : Nonempty (CongruentDissection 77) := by
  simpa using Erdos634.Draft.S2G.s2_family_gen 1 2 le_rfl (by norm_num)
theorem N84 : Nonempty (CongruentDissection 84) := Erdos634.R84TilingBridge.r84_nonempty_congruentDissection
theorem N88 : Nonempty (CongruentDissection 88) := Erdos634.R88TilingBridge.r88_nonempty_congruentDissection
theorem N99 : Nonempty (CongruentDissection 99) := by
  obtain ⟨E, -⟩ := Erdos634.Tiling99Bridge.exists_dissection_99_mul_sq 1 (by norm_num)
  exact ⟨by simpa using E⟩
theorem N126 : Nonempty (CongruentDissection 126) := Erdos634.R126TilingBridge.r126_nonempty_congruentDissection
theorem N322 : Nonempty (CongruentDissection 322) := Erdos634.S2RTilingBridge.s2r_nonempty_congruentDissection
/-- `27 = 3 · 3²`, ladder of the 3-tiling: composite, `≡ 3 mod 4`. -/
theorem N27 : Nonempty (CongruentDissection 27) := by
  obtain ⟨D⟩ := N3
  obtain ⟨hind, heta⟩ := Erdos634.Draft.RWEast.tri_eta D.target
  obtain ⟨E, -, -⟩ := Erdos634.Ladder.ladder (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind D heta 3 (by norm_num)
  exact ⟨E⟩

/-- N = 99 is composite, `99 % 4 = 3`: the residue class `3 mod 4` is not empty of tile counts. -/
example : ¬ Nat.Prime 99 ∧ 99 % 4 = 3 := by norm_num
example : ¬ Nat.Prime 27 ∧ 27 % 4 = 3 := by norm_num
/-- N = 3: prime, `≡ 3 mod 4`, a genuine tile count: the hypothesis `3 < N` of `theoremP_6` is
NECESSARY (without it the statement is false). -/
example : Nat.Prime 3 ∧ 3 % 4 = 3 ∧ Nonempty (CongruentDissection 3) := ⟨by norm_num, by norm_num, N3⟩

/-! ## 3. The count is forced (what "tile count" means) -/

/-- If the target has area `n` times the model's area, the tile count IS `n`. -/
theorem count_forced {N n : ℕ} (D : CongruentDissection N)
    (h : volume D.target.carrier = (n : ENNReal) * volume D.model.carrier) : N = n := by
  have h2 := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [h] at h2
  have hv0 : volume D.model.carrier ≠ 0 := D.model.volume_pos.ne'
  have hvt : volume D.model.carrier ≠ ⊤ := D.model.volume_ne_top
  have := (ENNReal.mul_left_inj hv0 hvt).mp h2.symm
  exact_mod_cast this

/-- Wrong count rejected: the ladder 4-tiling of `2·T0` has target area `4·|model|`, so no
`CongruentDissection 3` has the same target and model. -/
theorem wrong_count_rejected :
    ∃ E : CongruentDissection 4, ¬ ∃ D : CongruentDissection 3, D.target = E.target ∧ D.model = E.model := by
  obtain ⟨E⟩ := N4
  refine ⟨E, ?_⟩
  rintro ⟨D, ht, hm⟩
  have h4 := Erdos634.CongruentArea.congruentDissection_volume_target E
  have h3 := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [ht, hm, h4] at h3
  have hv0 : volume E.model.carrier ≠ 0 := E.model.volume_pos.ne'
  have hvt : volume E.model.carrier ≠ ⊤ := E.model.volume_ne_top
  have := (ENNReal.mul_left_inj hv0 hvt).mp h3
  have : (4 : ℕ) = 3 := by exact_mod_cast this
  omega

/-- No dissection with zero tiles. -/
theorem no_zero_tiles : IsEmpty (CongruentDissection 0) := ⟨fun D => by have := D.toDissection.pos; omega⟩

/-! ## 4. NEGATIVE controls: each structure field rejects wrong data -/

/-- (a) overlapping tiles: two equal tiles can never be the tiles of a `Dissection 2`
(`interiors_disjoint` fails because a tile has nonempty interior). -/
theorem overlap_rejected : ¬ ∃ D : Dissection 2, D.tile 0 = D.tile 1 := by
  rintro ⟨D, h⟩
  have hd : Disjoint (interior (D.tile 0).carrier) (interior (D.tile 1).carrier) :=
    D.interiors_disjoint (show (0 : Fin 2) ≠ 1 by decide)
  rw [h] at hd
  obtain ⟨x, hx⟩ := (D.tile 1).interior_nonempty
  exact Set.disjoint_left.mp hd hx hx

theorem halfspace_bound (T : Tri) (c : ℝ) (h : ∀ k, (T.pts k) 0 + (T.pts k) 1 ≤ c) :
    ∀ x ∈ T.carrier, x 0 + x 1 ≤ c := by
  have hconv : Convex ℝ {x : Plane | x 0 + x 1 ≤ c} :=
    convex_halfSpace_le (f := fun x : Plane => x 0 + x 1)
      ⟨fun x y => by simp; ring, fun a x => by simp; ring⟩ c
  have := convexHull_min (s := Set.range T.pts) (t := {x : Plane | x 0 + x 1 ≤ c})
    (by rintro _ ⟨k, rfl⟩; exact h k) hconv
  exact fun x hx => this hx

theorem det_big : det3 0 0 2 0 0 2 ≠ 0 := by unfold det3; norm_num
theorem det_small : det3 0 0 (1/2) 0 0 (1/2) ≠ 0 := by unfold det3; norm_num
noncomputable def Tbig : Tri := mkTri 0 0 2 0 0 2 det_big
noncomputable def Tsmall : Tri := mkTri 0 0 (1/2) 0 0 (1/2) det_small

theorem T0_bound : ∀ x ∈ T0.carrier, x 0 + x 1 ≤ 1 := by
  apply halfspace_bound
  intro k; fin_cases k <;> simp [T0, mkTri_pts]
theorem Tsmall_bound : ∀ x ∈ Tsmall.carrier, x 0 + x 1 ≤ 1/2 := by
  apply halfspace_bound
  intro k; fin_cases k <;> simp [Tsmall, mkTri_pts]

/-- (b) tile sticking out of the target: a single tile `2·T0` cannot cover target `T0`. -/
theorem outside_rejected : ¬ ∃ D : Dissection 1, D.target = T0 ∧ D.tile 0 = Tbig := by
  rintro ⟨D, ht, hl⟩
  have hc := D.covers
  have hmem : (mkPt 2 0 : Plane) ∈ ⋃ i, (D.tile i).carrier := by
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    rw [hl]; exact subset_convexHull ℝ _ ⟨1, by simp [Tbig, mkTri_pts]⟩
  rw [hc, ht] at hmem
  have := T0_bound _ hmem
  norm_num [mkPt_zero, mkPt_one] at this

/-- (b') tile too small to cover (wrong tile count / area): a single tile `T0/2` cannot cover `T0`. -/
theorem undercover_rejected : ¬ ∃ D : Dissection 1, D.target = T0 ∧ D.tile 0 = Tsmall := by
  rintro ⟨D, ht, hl⟩
  have hc := D.covers
  have hmem : (mkPt 1 0 : Plane) ∈ D.target.carrier := by
    rw [ht]; exact subset_convexHull ℝ _ ⟨1, by simp [T0, mkTri_pts]⟩
  rw [← hc] at hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  have : i = 0 := Subsingleton.elim _ _
  subst this
  rw [hl] at hi
  have := Tsmall_bound _ hi
  norm_num [mkPt_zero, mkPt_one] at this

theorem det_M : det3 0 0 2 0 0 1 ≠ 0 := by unfold det3; norm_num
noncomputable def M : Tri := mkTri 0 0 2 0 0 1 det_M    -- scalene right triangle, legs 2,1

/-- (c) tile not congruent to the model: `T0` (sides² 1,1,2) is not congruent to `M` (sides² 4,1,5). -/
theorem not_congruent : ¬ T0.Congruent M := by
  intro h
  have h1 := h.sideMultiset_eq
  have h2 := congrArg (fun m : Multiset ℝ => (m.map (fun x => x ^ 2)).sum) h1
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
    Multiset.sum_singleton] at h2
  have a1 : dist (T0.pts 0) (T0.pts 1) ^ 2 = 1 := by
    show dist (mkPt 0 0) (mkPt 1 0) ^ 2 = 1; rw [dist_sq_mkPt]; norm_num
  have a2 : dist (T0.pts 2) (T0.pts 0) ^ 2 = 1 := by
    show dist (mkPt 0 1) (mkPt 0 0) ^ 2 = 1; rw [dist_sq_mkPt]; norm_num
  have a3 : dist (T0.pts 1) (T0.pts 2) ^ 2 = 2 := by
    show dist (mkPt 1 0) (mkPt 0 1) ^ 2 = 2; rw [dist_sq_mkPt]; norm_num
  have b1 : dist (M.pts 0) (M.pts 1) ^ 2 = 4 := by
    show dist (mkPt 0 0) (mkPt 2 0) ^ 2 = 4; rw [dist_sq_mkPt]; norm_num
  have b2 : dist (M.pts 2) (M.pts 0) ^ 2 = 1 := by
    show dist (mkPt 0 1) (mkPt 0 0) ^ 2 = 1; rw [dist_sq_mkPt]; norm_num
  have b3 : dist (M.pts 1) (M.pts 2) ^ 2 = 5 := by
    show dist (mkPt 2 0) (mkPt 0 1) ^ 2 = 5; rw [dist_sq_mkPt]; norm_num
  rw [a1, a2, a3, b1, b2, b3] at h2
  norm_num at h2

/-! ## 5. Reflection coverage: a mirror pair is accepted -/

/-- The explicit reflection `(x,y) ↦ (-x,y)` as an element of `Plane ≃ᵢ Plane`
(the isometry group the definition `Tri.Congruent` quantifies over). -/
noncomputable def rho : Plane ≃ᵢ Plane where
  toFun x := mkPt (-(x 0)) (x 1)
  invFun x := mkPt (-(x 0)) (x 1)
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  isometry_toFun := Isometry.of_dist_eq (fun x y => by
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
    congr 1; ring)

/-- `rho` fixes `(0,1)` and `(0,0)` and moves `(-2,0)` to `(2,0)`: a nonidentity isometry with two
distinct fixed points, i.e. a reflection (orientation-reversing), not a direct motion. -/
theorem rho_facts : rho (mkPt 0 1) = mkPt 0 1 ∧ rho (mkPt 0 0) = mkPt 0 0 ∧
    rho (mkPt (-2) 0) = mkPt 2 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> (show mkPt _ _ = _; ext i; fin_cases i <;> simp)

theorem detTm : det3 0 1 (-2) 0 2 0 ≠ 0 := by unfold det3; norm_num
theorem detT1m : det3 0 1 (-2) 0 0 0 ≠ 0 := by unfold det3; norm_num
theorem detT2m : det3 0 1 0 0 2 0 ≠ 0 := by unfold det3; norm_num
noncomputable def Tm : Tri := mkTri 0 1 (-2) 0 2 0 detTm      -- isosceles, base 4, height 1
noncomputable def Tm1 : Tri := mkTri 0 1 (-2) 0 0 0 detT1m    -- left half  (legs 2,1)
noncomputable def Tm2 : Tri := mkTri 0 1 0 0 2 0 detT2m       -- right half = mirror image

/-- The explicit reflection carries the vertices of `Tm1` to those of `Tm2`, with the transposition
`(1 2)` as vertex relabelling. -/
theorem rho_maps : ∀ k, rho (Tm1.pts k) = Tm2.pts (Equiv.swap (1 : Fin 3) 2 k) := by
  intro k
  fin_cases k
  · show rho (mkPt 0 1) = mkPt 0 1; exact rho_facts.1
  · show rho (mkPt (-2) 0) = mkPt 2 0; exact rho_facts.2.2
  · show rho (mkPt 0 0) = mkPt 0 0; exact rho_facts.2.1

theorem Tm1_congruent_Tm2_via_rho : Tm1.Congruent Tm2 := ⟨rho, Equiv.swap 1 2, rho_maps⟩

/-- **A `CongruentDissection 2` that uses a reflected tile**: the isosceles triangle `Tm` is cut
along its altitude into `Tm1` and its mirror image `Tm2`; tile 1 is carried onto tile 0 only by an
orientation-reversing isometry (`rho`), and the structure accepts it. -/
theorem mirror_pair_dissection :
    ∃ D : CongruentDissection 2, D.target = Tm ∧ D.tile 0 = Tm1 ∧ D.tile 1 = Tm2 ∧ D.model = Tm1 := by
  have hlm : AffineMap.lineMap (mkPt (-2 : ℝ) 0) (mkPt 2 0) (1 / 2 : ℝ) = mkPt 0 0 := by
    rw [Erdos634.Draft.RAAssemble.lm]; congr 1 <;> norm_num
  obtain ⟨hcov, hdisj⟩ := Erdos634.Draft.CutGen.cut_carrier Tm Tm1 Tm2 (1 / 2) (by norm_num) (by norm_num)
    (by show mkPt (0:ℝ) 1 = mkPt 0 1; rfl) (by show mkPt (-2:ℝ) 0 = mkPt (-2) 0; rfl)
    (by show mkPt (0:ℝ) 0 = AffineMap.lineMap (mkPt (-2:ℝ) 0) (mkPt 2 0) (1/2); rw [hlm])
    (by show mkPt (0:ℝ) 1 = mkPt 0 1; rfl)
    (by show mkPt (0:ℝ) 0 = AffineMap.lineMap (mkPt (-2:ℝ) 0) (mkPt 2 0) (1/2); rw [hlm])
    (by show mkPt (2:ℝ) 0 = mkPt 2 0; rfl)
  refine ⟨⟨⟨Tm, ![Tm1, Tm2], ?_, ?_⟩, Tm1, ?_⟩, rfl, rfl, rfl, rfl⟩
  · rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hdisj | exact hdisj.symm
  · intro i; fin_cases i
    · exact Tri.Congruent.refl Tm1
    · exact Tm1_congruent_Tm2_via_rho.symm


/-- `Tri.det` is twice the signed area in the vertex order of `pts`. -/
theorem det_Tm1 : Tm1.det = 2 := by
  show (mkPt (-2) 0 - mkPt 0 1 : Plane) 0 * (mkPt 0 0 - mkPt 0 1 : Plane) 1
      - (mkPt (-2) 0 - mkPt 0 1 : Plane) 1 * (mkPt 0 0 - mkPt 0 1 : Plane) 0 = 2
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; norm_num
theorem det_Tm2 : Tm2.det = 2 := by
  show (mkPt 0 0 - mkPt 0 1 : Plane) 0 * (mkPt 2 0 - mkPt 0 1 : Plane) 1
      - (mkPt 0 0 - mkPt 0 1 : Plane) 1 * (mkPt 2 0 - mkPt 0 1 : Plane) 0 = 2
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; norm_num

/-- DOUBT (documented, benign): `Tri.Reflected/Unreflected` read the sign of `Tri.det` in the stored
vertex order, so they are gauge-dependent, not geometric chirality.  Here the mirror pair
`Tm1, Tm2` (related only by a reflection) is `Unreflected` w.r.t. each other under the stored order.
`Tri.Congruent` itself is unaffected (it quantifies over all isometries and all relabellings). -/
theorem reflected_is_label_gauge : Tm2.Unreflected Tm1 ∧ ¬ Tm2.Reflected Tm1 := by
  have h1 := det_Tm1; have h2 := det_Tm2
  refine ⟨?_, ?_⟩
  · simp only [Tri.Unreflected, h1, h2]
  · simp only [Tri.Reflected, h1, h2]; norm_num

/-! ## 6. The two statements, instantiated: hypotheses are satisfiable, and the iff has both sides -/

example : Nat.Prime 7 ∧ 7 % 4 = 3 ∧ 3 < 7 := by norm_num
example : Nat.Prime 11 ∧ 11 % 4 = 3 ∧ 3 < 11 := by norm_num
example : Nat.Prime 19 ∧ 19 % 4 = 3 ∧ 3 < 19 := by norm_num
example : Nat.Prime 4003 ∧ 4003 % 4 = 3 ∧ 3 < 4003 := by norm_num

/-- `theoremP_6` at `N = 7`, hypotheses discharged: the printed instance is a genuine implication from
`CongruentDissection 7` to `False`, with no vacuous hypothesis on `N`. -/
theorem no_dissection_7 : IsEmpty (CongruentDissection 7) :=
  ⟨fun D => Erdos634.Draft.TheoremP6.theoremP_6 7 D (by norm_num) (by norm_num) (by norm_num)⟩
theorem no_dissection_11 : IsEmpty (CongruentDissection 11) :=
  ⟨fun D => Erdos634.Draft.TheoremP6.theoremP_6 11 D (by norm_num) (by norm_num) (by norm_num)⟩

/-- `prime_tile_count_iff` at p = 2,3,5,13 (right side true, witnessed) and p = 7,11 (right side
false, so the iff yields emptiness). -/
theorem iff_p2 : Nonempty (CongruentDissection 2) ↔ (2 = 3 ∨ 2 % 4 ≠ 3) :=
  Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff 2 (by norm_num)
theorem iff_p7 : Nonempty (CongruentDissection 7) ↔ (7 = 3 ∨ 7 % 4 ≠ 3) :=
  Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff 7 (by norm_num)
example : ¬ (7 = 3 ∨ 7 % 4 ≠ 3) := by decide
example : (2 = 3 ∨ 2 % 4 ≠ 3) ∧ (3 = 3 ∨ 3 % 4 ≠ 3) ∧ (5 = 3 ∨ 5 % 4 ≠ 3) ∧ (13 = 3 ∨ 13 % 4 ≠ 3) := by decide

/-! ## 7. Angle definitions -/

/-- `cornerAngle` at the right-angle vertex of `T0` is `π/2`. -/
theorem cornerAngle_right : cornerAngle (mkPt 1 0) (mkPt 0 0) (mkPt 0 1) = Real.pi / 2 := by
  unfold cornerAngle EuclideanGeometry.angle
  rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simp [mkPt_zero, mkPt_one, inner, Fin.sum_univ_two]

end Erdos634.AUDB1

#print axioms Erdos634.AUDB1.plane_dist_is_L2
#print axioms Erdos634.AUDB1.ladder_nonempty
#print axioms Erdos634.AUDB1.N1
#print axioms Erdos634.AUDB1.N2
#print axioms Erdos634.AUDB1.N3
#print axioms Erdos634.AUDB1.N4
#print axioms Erdos634.AUDB1.N5
#print axioms Erdos634.AUDB1.N8
#print axioms Erdos634.AUDB1.N9
#print axioms Erdos634.AUDB1.N13
#print axioms Erdos634.AUDB1.N27
#print axioms Erdos634.AUDB1.N44
#print axioms Erdos634.AUDB1.N77
#print axioms Erdos634.AUDB1.N84
#print axioms Erdos634.AUDB1.N88
#print axioms Erdos634.AUDB1.N99
#print axioms Erdos634.AUDB1.N126
#print axioms Erdos634.AUDB1.N322
#print axioms Erdos634.AUDB1.count_forced
#print axioms Erdos634.AUDB1.wrong_count_rejected
#print axioms Erdos634.AUDB1.no_zero_tiles
#print axioms Erdos634.AUDB1.overlap_rejected
#print axioms Erdos634.AUDB1.outside_rejected
#print axioms Erdos634.AUDB1.undercover_rejected
#print axioms Erdos634.AUDB1.not_congruent
#print axioms Erdos634.AUDB1.rho
#print axioms Erdos634.AUDB1.rho_facts
#print axioms Erdos634.AUDB1.mirror_pair_dissection
#print axioms Erdos634.AUDB1.reflected_is_label_gauge
#print axioms Erdos634.AUDB1.no_dissection_7
#print axioms Erdos634.AUDB1.no_dissection_11
#print axioms Erdos634.AUDB1.iff_p2
#print axioms Erdos634.AUDB1.iff_p7
#print axioms Erdos634.AUDB1.cornerAngle_right
