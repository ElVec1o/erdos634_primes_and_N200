/-
Draft/NoThetaRegion.lean  In `AllThreshold`.

**No θ-region inside `T_M(1,f)` for `f ≥ 3`, `1 ≤ M ≤ f`.**  Tile `(f, f² − 1, f²)` (member `(1, f)`), angles `α, β, γ`
opposite `f, f² − 1, f²`.  A θ-shaped triangle has the corners `α + β` at both ends of one side (and `α` at the third
vertex).

THE LEAN STATEMENT (`no_theta_union`).  `D` is a `CongruentDissection` whose target has the sides `M f³, M f³, M (3f² − 1)`
(the target of `UniformThreshold.BetaTilable 1 f M`) and whose model has the sides `f, f² − 1, f²`; `S` is ANY set of
tiles of `D` whose union is a triangle `T` (`⋃ i ∈ S, (D.tile i).carrier = T.carrier`); the vertices of `T` are named by
a permutation `τ`, and `T` has the corner `α + β` at `T.pts (τ 0)` and at `T.pts (τ 1)` (`α = modelAlpha 1 f`,
`β = modelBeta 1 f`).  Conclusion: `False`.  Position and orientation of `T` are arbitrary; reflections are allowed (as
in `CongruentDissection`).  No restriction of the notion of sub-family: it is the one of `SubDissection.restrict`.

THE PROOF.
1. `SubDissection.restrictCongruent` makes `S` a congruent dissection of `T` with the same model.
2. `SideRunGT.thm_side_theta_angles`: the base `[Y, Z]` (`Y = T.pts (τ 0)`, `Z = T.pts (τ 1)`)
   has `|YZ| ≥ f³`; `SideRunGT.corners_sides_theta` (law of sines): the legs are `|XY| = |XZ| = f |YZ| ≥ f⁴`
   (`X = T.pts (τ 2)`).
3. The diameter of `T_M` is `M f³ ≤ f⁴` (its base `M (3f² − 1) ≤ M f³` for `f ≥ 3`); every point of `T ⊆ T_M` is a
   point of `T_M`, so `f⁴ ≤ |XY| ≤ M f³ ≤ f⁴`: equality, `M = f`, `|YZ| = f³`.
4. A segment of a triangle whose length is the largest vertex distance has both ends at vertices (`eq_vertex_of_far`,
   from the identity `|Σ wᵢ Vᵢ − Q|² = Σ wᵢ |Vᵢ − Q|² − Σ_{i<j} wᵢ wⱼ |Vᵢ − Vⱼ|²`); so `Y` and `Z` are vertices of
   `T_M` and `|YZ| = f³ ∈ {0, f⁴, f (3f² − 1)}`, impossible for `f ≥ 3`.

WITNESSES: `hyp_target_satisfiable` (the hypotheses on `D` hold: `BetaTilable 1 f f`, the seed, every
`f ≥ 2`); `hyp_theta_satisfiable` (the hypotheses on `S`, `T`, `τ` and the model hold for `S = univ` in the 48-tile
tiling of `θ_4(1,2)`, at `f = 2`).

Composite-N statement of the threshold program.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGThetaMain
import Erdos634.Draft.ThetaAngles
import Erdos634.Draft.SideRun
import Erdos634.SubDissection

open scoped Classical

namespace Erdos634.Draft.NoThetaRegion

open Erdos634.Geometry Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.Draft.UniformThreshold (hasSides_congr BetaTilable)

/-! ## 1. Distances in a triangle -/

theorem plane_dist_sq (p q : Plane) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- the barycentric identity `|Σ wᵢ Vᵢ − Q|² = Σ wᵢ |Vᵢ − Q|² − Σ_{i<j} wᵢ wⱼ |Vᵢ − Vⱼ|²` in coordinates -/
theorem combo_identity (w0 w1 w2 a0 a1 b0 b1 c0 c1 q0 q1 : ℝ) (hs : w0 + w1 + w2 = 1) :
    (w0 * a0 + w1 * b0 + w2 * c0 - q0) ^ 2 + (w0 * a1 + w1 * b1 + w2 * c1 - q1) ^ 2 =
      w0 * ((a0 - q0) ^ 2 + (a1 - q1) ^ 2) + w1 * ((b0 - q0) ^ 2 + (b1 - q1) ^ 2) +
        w2 * ((c0 - q0) ^ 2 + (c1 - q1) ^ 2) -
      (w0 * w1 * ((a0 - b0) ^ 2 + (a1 - b1) ^ 2) + w0 * w2 * ((a0 - c0) ^ 2 + (a1 - c1) ^ 2) +
        w1 * w2 * ((b0 - c0) ^ 2 + (b1 - c1) ^ 2)) := by
  have h : w2 = 1 - w0 - w1 := by linarith
  subst h; ring

/-- a point of a triangle is within `D` of every vertex, if all vertex distances are at most `D` -/
theorem dist_vertex_le (T : Erdos634.Geometry.Tri) {D : ℝ} (hD : ∀ i j, dist (T.pts i) (T.pts j) ≤ D) {Q : Plane}
    (hQ : Q ∈ T.carrier) (i : Fin 3) : dist (T.pts i) Q ≤ D := by
  obtain ⟨x', hx', hle⟩ := convexHull_exists_dist_ge hQ (T.pts i)
  obtain ⟨j, rfl⟩ := hx'
  rw [dist_comm]; exact hle.trans (hD j i)

/-- **the diameter of a triangle**: two points of it are within the largest vertex distance -/
theorem dist_le_of_mem (T : Erdos634.Geometry.Tri) {D : ℝ} (hD : ∀ i j, dist (T.pts i) (T.pts j) ≤ D) {P Q : Plane}
    (hP : P ∈ T.carrier) (hQ : Q ∈ T.carrier) : dist P Q ≤ D := by
  obtain ⟨x', hx', hle⟩ := convexHull_exists_dist_ge hP Q
  obtain ⟨j, rfl⟩ := hx'
  exact hle.trans (dist_vertex_le T hD hQ j)

/-- **the equality case**: if two points `P, Q` of a triangle are at distance at least the largest vertex distance,
then `P` is a vertex -/
theorem eq_vertex_of_far (T : Erdos634.Geometry.Tri) {D : ℝ} (hD : ∀ i j, dist (T.pts i) (T.pts j) ≤ D) {P Q : Plane}
    (hP : P ∈ T.carrier) (hQ : Q ∈ T.carrier) (h : D ≤ dist P Q) : ∃ i, P = T.pts i := by
  have hD0 : 0 ≤ D := by have := hD 0 0; rw [dist_self] at this; exact this
  have hVQ := dist_vertex_le T hD hQ
  have hw : ∀ i, 0 ≤ T.basis.coord i P := by
    rw [Tri.carrier_eq_nonneg_coord] at hP; exact hP
  have hsum : ∑ i, T.basis.coord i P = 1 := T.basis.sum_coord_apply_eq_one P
  have hcomb : ∑ i, T.basis.coord i P • T.pts i = P := T.basis.linear_combination_coord_eq_self P
  rw [Fin.sum_univ_three] at hsum hcomb
  set w0 := T.basis.coord 0 P
  set w1 := T.basis.coord 1 P
  set w2 := T.basis.coord 2 P
  have hc0 : P 0 = w0 * T.pts 0 0 + w1 * T.pts 1 0 + w2 * T.pts 2 0 := by
    rw [← hcomb]; simp
  have hc1 : P 1 = w0 * T.pts 0 1 + w1 * T.pts 1 1 + w2 * T.pts 2 1 := by
    rw [← hcomb]; simp
  have hid := combo_identity w0 w1 w2 (T.pts 0 0) (T.pts 0 1) (T.pts 1 0) (T.pts 1 1) (T.pts 2 0) (T.pts 2 1)
    (Q 0) (Q 1) hsum
  rw [← hc0, ← hc1, ← plane_dist_sq, ← plane_dist_sq, ← plane_dist_sq, ← plane_dist_sq, ← plane_dist_sq,
    ← plane_dist_sq, ← plane_dist_sq] at hid
  have hne : ∀ i j : Fin 3, i ≠ j → 0 < dist (T.pts i) (T.pts j) ^ 2 := fun i j hij =>
    pow_pos (dist_pos.mpr (fun he => hij (T.indep.injective he))) 2
  have e01 := hne 0 1 (by decide)
  have e02 := hne 0 2 (by decide)
  have e12 := hne 1 2 (by decide)
  have hsq : D ^ 2 ≤ dist P Q ^ 2 := pow_le_pow_left₀ hD0 h 2
  have q0 : dist (T.pts 0) Q ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ dist_nonneg (hVQ 0) 2
  have q1 : dist (T.pts 1) Q ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ dist_nonneg (hVQ 1) 2
  have q2 : dist (T.pts 2) Q ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ dist_nonneg (hVQ 2) 2
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  have hconv : w0 * dist (T.pts 0) Q ^ 2 + w1 * dist (T.pts 1) Q ^ 2 + w2 * dist (T.pts 2) Q ^ 2 ≤ D ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left q0 h0, mul_le_mul_of_nonneg_left q1 h1, mul_le_mul_of_nonneg_left q2 h2]
  have t01 : 0 ≤ w0 * w1 * dist (T.pts 0) (T.pts 1) ^ 2 := by positivity
  have t02 : 0 ≤ w0 * w2 * dist (T.pts 0) (T.pts 2) ^ 2 := by positivity
  have t12 : 0 ≤ w1 * w2 * dist (T.pts 1) (T.pts 2) ^ 2 := by positivity
  have z01 : w0 * w1 * dist (T.pts 0) (T.pts 1) ^ 2 = 0 := by linarith
  have z02 : w0 * w2 * dist (T.pts 0) (T.pts 2) ^ 2 = 0 := by linarith
  have z12 : w1 * w2 * dist (T.pts 1) (T.pts 2) ^ 2 = 0 := by linarith
  have p01 : w0 * w1 = 0 := (mul_eq_zero.mp z01).resolve_right e01.ne'
  have p02 : w0 * w2 = 0 := (mul_eq_zero.mp z02).resolve_right e02.ne'
  have p12 : w1 * w2 = 0 := (mul_eq_zero.mp z12).resolve_right e12.ne'
  by_cases a0 : w0 = 0
  · by_cases a1 : w1 = 0
    · refine ⟨2, ?_⟩
      have : w2 = 1 := by linarith
      rw [← hcomb, a0, a1, this]; simp
    · have b2 : w2 = 0 := (mul_eq_zero.mp p12).resolve_left a1
      refine ⟨1, ?_⟩
      have : w1 = 1 := by linarith
      rw [← hcomb, a0, b2, this]; simp
  · have b1 : w1 = 0 := (mul_eq_zero.mp p01).resolve_left a0
    have b2 : w2 = 0 := (mul_eq_zero.mp p02).resolve_left a0
    refine ⟨0, ?_⟩
    have : w0 = 1 := by linarith
    rw [← hcomb, b1, b2, this]; simp

/-- the vertex distances of a triangle with `HasSides T a b c` are `0, a, b, c` -/
theorem dist_cases {T : Erdos634.Geometry.Tri} {a b c : ℝ} (h : HasSides T a b c) (i j : Fin 3) :
    dist (T.pts i) (T.pts j) = 0 ∨ dist (T.pts i) (T.pts j) = a ∨ dist (T.pts i) (T.pts j) = b ∨
      dist (T.pts i) (T.pts j) = c := by
  obtain ⟨τ, ha, hb, hc⟩ := h
  have ha' : dist (T.pts (τ 2)) (T.pts (τ 1)) = a := by rw [dist_comm]; exact ha
  have hb' : dist (T.pts (τ 0)) (T.pts (τ 2)) = b := by rw [dist_comm]; exact hb
  have hc' : dist (T.pts (τ 1)) (T.pts (τ 0)) = c := by rw [dist_comm]; exact hc
  obtain ⟨i', rfl⟩ := τ.surjective i
  obtain ⟨j', rfl⟩ := τ.surjective j
  fin_cases i' <;> fin_cases j' <;> simp [ha, hb, hc, ha', hb', hc']

/-! ## 2. The theorem -/

/-- **NO θ-REGION IN `T_M(1, f)`.**  Let `f ≥ 3`, `1 ≤ M ≤ f`, and let `D` be a congruent dissection of the triangle
`T_M(1, f)` (sides `M f³, M f³, M (3f² − 1)`) by the tile with sides `f, f² − 1, f²` (any number of tiles, reflections
allowed).  No set `S` of tiles of `D` has for union a triangle `T` with the corner `α + β` at two of its vertices
(`α, β` the angles of the tile opposite `f`, `f² − 1`), in any position or orientation. -/
theorem no_theta_union (f M : ℕ) (hf : 3 ≤ f) (hM : 1 ≤ M) (hMf : M ≤ f) {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target ((M : ℝ) * (f : ℝ) ^ 3) ((M : ℝ) * (f : ℝ) ^ 3) ((M : ℝ) * (3 * (f : ℝ) ^ 2 - 1)))
    (hMod : HasSides D.model (f : ℝ) ((f : ℝ) ^ 2 - 1) ((f : ℝ) ^ 2))
    (S : Finset (Fin N)) (T : Erdos634.Geometry.Tri) (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier)
    (τ : Equiv.Perm (Fin 3))
    (hQ : cornerAngle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) = modelAlpha 1 (f : ℝ) + modelBeta 1 (f : ℝ))
    (hB : cornerAngle (T.pts (τ 0)) (T.pts (τ 1)) (T.pts (τ 2)) = modelAlpha 1 (f : ℝ) + modelBeta 1 (f : ℝ)) :
    False := by
  have hfR : (3 : ℝ) ≤ f := by exact_mod_cast hf
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMfR : (M : ℝ) ≤ f := by exact_mod_cast hMf
  have hf0 : (0 : ℝ) < f := by linarith
  -- 1. the sub-family as a congruent dissection of `T`
  set D' := Erdos634.SubDissection.restrictCongruent D S T hcov with hD'
  have hMod' : HasSides D'.model (((1 : ℕ) : ℝ) * (f : ℝ)) ((f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) ((f : ℝ) ^ 2) :=
    hasSides_congr hMod (by push_cast; ring) (by push_cast; ring) rfl
  have hQ' : cornerAngle (D'.target.pts (τ 2)) (D'.target.pts (τ 0)) (D'.target.pts (τ 1)) =
      modelAlpha ((1 : ℕ) : ℝ) (f : ℝ) + modelBeta ((1 : ℕ) : ℝ) (f : ℝ) := by
    rw [Nat.cast_one]; exact hQ
  have hB' : cornerAngle (D'.target.pts (τ 0)) (D'.target.pts (τ 1)) (D'.target.pts (τ 2)) =
      modelAlpha ((1 : ℕ) : ℝ) (f : ℝ) + modelBeta ((1 : ℕ) : ℝ) (f : ℝ) := by
    rw [Nat.cast_one]; exact hB
  have h1f : 1 < f := by omega
  have hco : Nat.Coprime 1 f := Nat.coprime_one_left f
  -- 2. the base carries `f` c-edges (S7), and the legs are `f` times the base
  obtain ⟨_, _, _, _, _, hbase⟩ :=
    Erdos634.Draft.SideRunGT.thm_side_theta_angles 1 f le_rfl h1f hco D' hMod' τ hQ' hB'
  obtain ⟨σm, m0, m1, m2⟩ := Erdos634.Draft.SideRunG.sideOpp_relabel_of_hasSides hMod'
  obtain ⟨s, hs, l1, l2, l3⟩ :=
    Erdos634.Draft.SideRunGT.corners_sides_theta T (D'.model.relabel σm) τ le_rfl h1f m0 m1 m2 hQ' hB'
  change (f : ℝ) ^ 3 ≤ dist (T.pts (τ 0)) (T.pts (τ 1)) at hbase
  set X := T.pts (τ 2)
  set Y := T.pts (τ 0)
  set Z := T.pts (τ 1)
  have hleg1 : dist X Y = (f : ℝ) * dist Y Z := by rw [l2, l3]; push_cast; ring
  have hleg2 : dist Z X = (f : ℝ) * dist Y Z := by rw [l1, l3]; push_cast; ring
  -- 3. `T` lies in `T_M`, whose diameter is `M f³`
  have hsub : T.carrier ⊆ D.target.carrier := by
    intro x hx
    rw [← hcov] at hx
    obtain ⟨i, -, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact tile_subset_target D.toDissection i hxi
  have hmem : ∀ k, T.pts k ∈ D.target.carrier := fun k =>
    hsub (subset_convexHull ℝ _ (Set.mem_range_self k))
  have hbase_le : (M : ℝ) * (3 * (f : ℝ) ^ 2 - 1) ≤ (M : ℝ) * (f : ℝ) ^ 3 := by
    have h3 : 3 * (f : ℝ) ^ 2 - 1 ≤ (f : ℝ) ^ 3 := by nlinarith [sq_nonneg (f : ℝ)]
    exact mul_le_mul_of_nonneg_left h3 (by linarith)
  have hdiam : ∀ i j, dist (D.target.pts i) (D.target.pts j) ≤ (M : ℝ) * (f : ℝ) ^ 3 := by
    intro i j
    have hpos : 0 ≤ (M : ℝ) * (f : ℝ) ^ 3 := by positivity
    rcases dist_cases hT i j with h | h | h | h <;> rw [h] <;> linarith
  have hXY_le : dist X Y ≤ (M : ℝ) * (f : ℝ) ^ 3 := dist_le_of_mem _ hdiam (hmem _) (hmem _)
  have hMf4 : (M : ℝ) * (f : ℝ) ^ 3 ≤ (f : ℝ) ^ 4 := by
    have : (M : ℝ) * (f : ℝ) ^ 3 ≤ (f : ℝ) * (f : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hMfR (by positivity)
    linear_combination this
  have hf4 : (f : ℝ) ^ 4 ≤ dist X Y := by
    rw [hleg1]
    have := mul_le_mul_of_nonneg_left hbase hf0.le
    linear_combination this
  have hXY : dist X Y = (M : ℝ) * (f : ℝ) ^ 3 := le_antisymm hXY_le (hMf4.trans hf4)
  have hMf4' : (M : ℝ) * (f : ℝ) ^ 3 = (f : ℝ) ^ 4 := le_antisymm hMf4 (hXY ▸ hf4)
  have hYZ : dist Y Z = (f : ℝ) ^ 3 := by
    have h1 : (f : ℝ) * dist Y Z = (f : ℝ) * (f : ℝ) ^ 3 := by
      rw [← hleg1, hXY]; linear_combination hMf4'
    exact mul_left_cancel₀ hf0.ne' h1
  have hMeq : (M : ℝ) = f := by
    have h1 : ((M : ℝ) - f) * (f : ℝ) ^ 3 = 0 := by linear_combination hMf4'
    have := (mul_eq_zero.mp h1).resolve_right (by positivity)
    linarith
  -- 4. `Y` and `Z` are vertices of `T_M`
  obtain ⟨i, hi⟩ := eq_vertex_of_far D.target hdiam (hmem (τ 0)) (hmem (τ 2))
    (by rw [dist_comm]; exact hXY.symm.le)
  obtain ⟨j, hj⟩ := eq_vertex_of_far D.target hdiam (hmem (τ 1)) (hmem (τ 2))
    (by rw [hleg2, ← hleg1, hXY])
  have hd : dist (D.target.pts i) (D.target.pts j) = (f : ℝ) ^ 3 := by
    rw [← hi, ← hj]; exact hYZ
  rw [hMeq] at hT
  rcases dist_cases hT i j with h | h | h | h <;> rw [hd] at h
  · have : (0 : ℝ) < (f : ℝ) ^ 3 := by positivity
    linarith
  · linarith [pow_pos hf0 3, mul_le_mul_of_nonneg_right hfR (pow_pos hf0 3).le]
  · linarith [pow_pos hf0 3, mul_le_mul_of_nonneg_right hfR (pow_pos hf0 3).le]
  · have h2 : (f : ℝ) * (2 * (f : ℝ) ^ 2 - 1) = 0 := by linear_combination (-1 : ℝ) * h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · nlinarith

/-! ## 3. The hypotheses are satisfiable (separately) -/

/-- the hypotheses on `D` hold: `T_f(1, f)` has a tiling (the seed), every `f ≥ 2` -/
theorem hyp_target_satisfiable (f : ℕ) (hf : 2 ≤ f) : ∃ (N : ℕ) (D : CongruentDissection N),
    HasSides D.target ((f : ℝ) * (f : ℝ) ^ 3) ((f : ℝ) * (f : ℝ) ^ 3) ((f : ℝ) * (3 * (f : ℝ) ^ 2 - 1)) ∧
    HasSides D.model (f : ℝ) ((f : ℝ) ^ 2 - 1) ((f : ℝ) ^ 2) := by
  obtain ⟨N, D, hT, hM⟩ := Erdos634.Draft.SideRun.betaTilable_e1_self f hf
  exact ⟨N, D, hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
    hasSides_congr hM (by norm_num) (by norm_num) rfl⟩

/-- the hypotheses on `S`, `T`, `τ` and the model hold together (`S = univ`, `T` the target) in the 48-tile tiling of
`θ_4(1,2)` (member `(1, 2)`; the theorem needs `f ≥ 3`, where the library has no θ-tiling) -/
theorem hyp_theta_satisfiable : ∃ (N : ℕ) (D : CongruentDissection N) (S : Finset (Fin N)) (T : Erdos634.Geometry.Tri)
    (τ : Equiv.Perm (Fin 3)), (⋃ i ∈ S, (D.tile i).carrier) = T.carrier ∧
    HasSides D.model ((2 : ℕ) : ℝ) (((2 : ℕ) : ℝ) ^ 2 - 1) (((2 : ℕ) : ℝ) ^ 2) ∧
    cornerAngle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) = modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) ∧
    cornerAngle (T.pts (τ 0)) (T.pts (τ 1)) (T.pts (τ 2)) = modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) := by
  obtain ⟨N, D, τ, hM, hQ, hB, -⟩ := Erdos634.Draft.ThetaAngles.angles_witness_4_1_2
  refine ⟨N, D, Finset.univ, D.target, τ, ?_, hasSides_congr hM (by push_cast; ring) (by push_cast; ring) rfl,
    by rw [← Nat.cast_one]; exact hQ, by rw [← Nat.cast_one]; exact hB⟩
  simp only [Finset.mem_univ, Set.iUnion_true]
  exact D.covers

end Erdos634.Draft.NoThetaRegion

#print axioms Erdos634.Draft.NoThetaRegion.eq_vertex_of_far
#print axioms Erdos634.Draft.NoThetaRegion.no_theta_union
#print axioms Erdos634.Draft.NoThetaRegion.hyp_target_satisfiable
#print axioms Erdos634.Draft.NoThetaRegion.hyp_theta_satisfiable
