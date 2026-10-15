/-
The forward tile at the ends of the corner chord, part 1 of 2.  Adapts `GLCForward` (γ = 2α) and `T30LC2Forward` (π/3)
to the base-β tile.  The architecture and proof skeleton are redone for the base-β tile; the files below are not imported,
to keep the import cone small.  Copied lemmas each carry a header line naming file:line:
  Draft/T30LC2Forward.lean:29     C2Forward.inner_coord             -> inner_coord
  Draft/GLCForward.lean:36        GLC.cross_ne_of_angle'            -> cross_ne_of_angle'
  Draft/T30LC2Forward.lean:54     C2Forward.cross_zero_of_ker       -> cross_zero_of_ker
  Draft/T30LPi3Cone.lean:67       Pi3Cone.hull_cone                 -> hull_cone
  Draft/T30LSectorFill.lean:113   SectorFill.vertex_dir_nonpos      -> vertex_dir_nonpos
  Draft/GLCG1.lean:24             GLC.coord_lin (generalized from `U.basis.coord m` to any affine functional) -> aff_lin
  Draft/GLCForward.lean:60-111    forward_tile_2a, covering half (the tiles missing `X` are at positive distance; a tile
                                  `K0` covering `X + eps u` contains `X`)                          -> forward_cover
  Draft/GLCForward.lean:129-197   forward_tile_2a, cone half (`X + eps u` in the cone of `K0` at its vertex; `g <= 0` on
                                  its edges; two edges on the line `g = 0` would be parallel)    -> edge_on_ray
  Draft/GLCForward.lean:112-128   forward_tile_2a, fan half (`boundary_fan_2alpha` + `cntA` bookkeeping)
                                  -> third_presents_beta, replaced by
                                  `VertexFigureReal.gamma_boundary_figure_real` (a `gamma` at a non-vertex frontier point
                                  forces the figure `{alpha, beta, gamma}`, one tile each, none straight)
  Draft/GLCG1.lean:33             GLC.fwd_not_mem (a point beyond a vertex of a triangle is outside it)
                                  -> `fwd_not_mem_hull` (the same barycentric-functional argument, for the parallelogram
                                  `T_A u T_3` at once: one functional for both tiles)
Imported and applied:
  Draft/CornerParaHalfTurn.lean   (and `Draft/T30LPi3F6Geom.lean` for `lin_coord`)
  VertexFigureReal.lean:347       gamma_boundary_figure_real
  TileAt.lean:665                 congruentDissection_localAngle_mem_boundary
  CornerAnglePerm.lean:369        vertex_of_localAngle_corner
-/
import Erdos634.Draft.CornerParaHalfTurn

/-!
# The generic pieces of the forward-tile argument, part 1 of 2

Part 2 is `Draft/CornerParaForward.lean` (the symmetric core `forward_tile_core` and its two instances at the corner
chord's ends `P`, `Q`).  Adapts `GLCForward.forward_tile_2a` (γ = 2α) and `T30LC2Forward.forward_tile` (π/3) to the base-β tile.

The argument of `forward_tile_2a` is split into four independent lemmas:
* `forward_cover` (covering half; any `Dissection`): if `X + ε u ∈ target` for `0 < ε ≤ ε0`, some tile `K0` contains `X`
  and one forward point `X + ε u` (the tiles missing `X` are at positive distance from it);
* `edge_on_ray` (cone half; any `Dissection`): a tile `K` with vertex `l` at `X`, a forward point `X + ε u` in `K`, a
  supporting functional `g` of the target with `g X = cg`, `g u = 0`, and corner angle `θ ∈ (0, π)` at `l`, has an edge at
  `X` on the ray `ℝ≥0 u` (two edges on the line `g = 0` would be parallel; they make the angle `θ`);
* `third_presents_beta`: at a non-vertex frontier point `X` where two tiles present `α` and `γ`, every other tile
  containing `X` presents `β` (the figure is `{α, β, γ}`, one tile each, none straight), and the `β`-presenter is unique;
* `fwd_not_mem_hull`: the points `X + δ (X - A)` (`δ > 0`) lie outside the parallelogram `hull {A, X, X + Y - A, Y}` (one
  affine functional `ψ` with `ψ A = ψ Y = 0`, `ψ X = 1`, so `ψ ≤ 1` on the parallelogram and `ψ = 1 + δ` there).

`fwd_not_mem_hull` has an in-file witness `fwd_not_mem_hull_witness` (concrete points `A = 0`, `X = e₀`, `Y = e₁`, `ψ` the first
coordinate) and an in-file counterexample `fwd_not_mem_hull_control` (at `δ = 0` the point is the vertex `X`, so the strict
inequality `δ > 0` is needed).  `forward_cover`, `edge_on_ray`, `third_presents_beta`, `unique_beta_presenter` concern arbitrary
`Dissection`s / `CongruentDissection`s; they are exercised, through their consumer `forward_tile_core`
(`Draft/CornerParaForward.lean`), at the N = 44 tiling `D44` by `Draft/CornerParaWitnessAux` / `Draft/CornerParaWitness`.
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

/-! ## 1. Copied pieces: cross products, the cone of a triangle at a vertex, the supporting functional -/

/-- COPY of `Draft/T30LC2Forward.lean:29 C2Forward.inner_coord`. -/
theorem inner_coord (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  try ring

/-- COPY of `Draft/GLCForward.lean:36 GLC.cross_ne_of_angle'`: two vectors at angle `θ ∈ (0, π)` are not parallel. -/
theorem cross_ne_of_angle' {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi) {x y : Plane} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : InnerProductGeometry.angle x y = θ) : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
  intro hc
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm x y
  rw [h] at hcos
  have hxx : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [← real_inner_self_eq_norm_sq, inner_coord]; ring
  have hyy : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by rw [← real_inner_self_eq_norm_sq, inner_coord]; ring
  rw [inner_coord] at hcos
  have hpx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpy : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hlag : (x 0 * y 0 + x 1 * y 1) ^ 2 = (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
    have : (x 0 * y 0 + x 1 * y 1) ^ 2 + (x 0 * y 1 - x 1 * y 0) ^ 2
        = (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by ring
    rw [hc] at this; linarith
  rw [← hcos, ← hxx, ← hyy] at hlag
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 h1
  have hsc := Real.sin_sq_add_cos_sq θ
  have hpos : 0 < (‖x‖ * ‖y‖) ^ 2 := by positivity
  have : (Real.sin θ) ^ 2 * (‖x‖ * ‖y‖) ^ 2 = 0 := by nlinarith
  have := mul_eq_zero.mp this
  rcases this with h' | h'
  · nlinarith
  · linarith

/-- COPY of `Draft/T30LC2Forward.lean:54 C2Forward.cross_zero_of_ker`: two vectors in the kernel of a nonzero functional on
the plane are parallel. -/
theorem cross_zero_of_ker (g : Plane →ₗ[ℝ] ℝ) (hg : g ≠ 0) {x y : Plane} (hx : g x = 0) (hy : g y = 0) :
    x 0 * y 1 - x 1 * y 0 = 0 := by
  rw [Erdos634.Pi3F6.lin_coord g x] at hx
  rw [Erdos634.Pi3F6.lin_coord g y] at hy
  have hg' : g (EuclideanSpace.single 0 1) ≠ 0 ∨ g (EuclideanSpace.single 1 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg
    refine LinearMap.ext fun z => ?_
    rw [Erdos634.Pi3F6.lin_coord g z, hcon.1, hcon.2]; simp
  rcases hg' with h | h
  · apply mul_left_cancel₀ h
    linear_combination (y 1) * hx - (x 1) * hy
  · apply mul_left_cancel₀ h
    linear_combination (x 0) * hy - (y 0) * hx

/-- COPY of `Draft/T30LPi3Cone.lean:67 Pi3Cone.hull_cone`: a point of a triangle's carrier lies in the cone
`v + ℝ≥0 (B − v) + ℝ≥0 (C − v)` at the vertex `v = T.pts k`. -/
theorem hull_cone (T : Tri) (k : Fin 3) :
    ∀ x ∈ T.carrier, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      x - T.pts k = s • (T.pts (k + 1) - T.pts k) + t • (T.pts (k + 2) - T.pts k) := by
  have hconv : Convex ℝ {x : Plane | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      x - T.pts k = s • (T.pts (k + 1) - T.pts k) + t • (T.pts (k + 2) - T.pts k)} := by
    intro x hx y hy a b ha hb hab
    obtain ⟨s, t, hs, ht, hx⟩ := hx
    obtain ⟨s', t', hs', ht', hy⟩ := hy
    refine ⟨a * s + b * s', a * t + b * t', by positivity, by positivity, ?_⟩
    have e : a • x + b • y - T.pts k = a • (x - T.pts k) + b • (y - T.pts k) := by
      have : T.pts k = (a + b) • T.pts k := by rw [hab, one_smul]
      conv_lhs => rw [this]
      simp only [smul_sub, add_smul]; abel
    rw [e, hx, hy]
    simp only [smul_add, smul_smul, add_smul]; abel
  have hsub : T.carrier ⊆ {x : Plane | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      x - T.pts k = s • (T.pts (k + 1) - T.pts k) + t • (T.pts (k + 2) - T.pts k)} := by
    refine convexHull_min ?_ hconv
    rintro z ⟨i, rfl⟩
    have h3 : ∀ k i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide
    rcases h3 k i with rfl | rfl | rfl
    · exact ⟨0, 0, le_refl _, le_refl _, by simp⟩
    · exact ⟨1, 0, zero_le_one, le_refl _, by simp⟩
    · exact ⟨0, 1, le_refl _, zero_le_one, by simp⟩
  exact fun x hx => hsub hx

/-- COPY of `Draft/T30LSectorFill.lean:113 SectorFill.vertex_dir_nonpos`: every tile edge at a target-boundary vertex points
into the target's half-plane: if `g ≤ cg` on the target and `g = cg` at the vertex `(tile i).pts j`, then every other
vertex `(tile i).pts k` satisfies `g (P − v) ≤ 0`. -/
theorem vertex_dir_nonpos {N : ℕ} (D : Dissection N) (i : Fin N) (j k : Fin 3)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hv : g ((D.tile i).pts j) = cg) : g ((D.tile i).pts k - (D.tile i).pts j) ≤ 0 := by
  have hk : (D.tile i).pts k ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨i, subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  have := hg _ hk
  rw [map_sub, hv]; linarith

/-! ## 2. D1, covering half: some tile contains `X` and a forward point -/

/-- **Covering half of `GLCForward.forward_tile_2a` (`:76-109`).**  If `X + ε u` is in the target for `0 < ε ≤ ε0` (`u ≠ 0`),
then some tile `K0` contains `X` AND a forward point `X + ε u` with `0 < ε ≤ ε0`: the tiles missing `X` form a closed set not
containing `X`, hence at positive distance from it; a forward point close enough to `X` lies in some tile, which therefore
contains `X`.  Stated for any `Dissection`. -/
theorem forward_cover {N : ℕ} (D : Dissection N) {X u : Plane} (hu : u ≠ 0) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hin : ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → X + ε • u ∈ D.target.carrier) :
    ∃ (K0 : Fin N) (ε : ℝ), 0 < ε ∧ ε ≤ ε0 ∧ X ∈ (D.tile K0).carrier ∧
      X + ε • u ∈ (D.tile K0).carrier := by
  classical
  have hBadClosed : IsClosed (⋃ i ∈ ({i | X ∉ (D.tile i).carrier} : Finset (Fin N)), (D.tile i).carrier) := by
    refine isClosed_biUnion_finset ?_
    intro i _
    exact (Tri.isCompact _).isClosed
  have hXnot : X ∉ (⋃ i ∈ ({i | X ∉ (D.tile i).carrier} : Finset (Fin N)), (D.tile i).carrier) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop, not_exists, not_and]
    intro i hi hmem
    exact hi hmem
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hBadClosed.isOpen_compl X hXnot
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set ε : ℝ := min ε0 (δ / (2 * ‖u‖)) with hε
  have hεpos : 0 < ε := lt_min hε0 (by positivity)
  have hεle : ε ≤ ε0 := min_le_left _ _
  have hεδ : ε * ‖u‖ < δ := by
    have h1 : ε ≤ δ / (2 * ‖u‖) := min_le_right _ _
    have h2 : ε * ‖u‖ ≤ δ / (2 * ‖u‖) * ‖u‖ := by gcongr
    have h3 : δ / (2 * ‖u‖) * ‖u‖ = δ / 2 := by field_simp
    linarith
  have hy := hin ε hεpos hεle
  rw [← D.covers] at hy
  obtain ⟨K0, hyK0⟩ := Set.mem_iUnion.mp hy
  have hXK0 : X ∈ (D.tile K0).carrier := by
    by_contra hnot
    have hyb : X + ε • u ∈ (⋃ i ∈ ({i | X ∉ (D.tile i).carrier} : Finset (Fin N)), (D.tile i).carrier) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
      exact ⟨K0, hnot, hyK0⟩
    have hd : X + ε • u ∈ Metric.ball X δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
      exact hεδ
    exact hball hd hyb
  exact ⟨K0, ε, hεpos, hεle, hXK0, hyK0⟩

/-! ## 3. D1, cone half: a tile with a vertex at `X` and a forward point has an edge on the ray -/

/-- **Cone half of `GLCForward.forward_tile_2a` (`:136-197`).**  Let `g ≠ 0` be a supporting functional of the target
(`g ≤ cg` on it) with `g X = cg` and `g u = 0` (`u` runs along the line `g = cg`).  Let the tile `K` have its vertex `l` at `X`
with corner angle `θ ∈ (0, π)` there, and contain a forward point `X + ε u` (`ε > 0`).  Then one of the two edges of `K` at
`X` is a positive multiple of `u` (`pts (l+1) - X = t u` or `pts (l+2) - X = t u`, `t > 0`): it lies on the ray `ℝ≥0 u`.
(`GLCForward` states this as `SameRay`; the `∃ t > 0` form is `SameRay` plus nonvanishing of the edge.)  Proof: `X + ε u` is in the
cone of `K` at `l`; both edges point into the half-plane `g ≤ cg` (`vertex_dir_nonpos`); if both cone coefficients were
positive both edges would lie on the line `g = cg`, hence be parallel, but they make the angle `θ ∈ (0, π)`. -/
theorem edge_on_ray {N : ℕ} (D : Dissection N) {X u : Plane} (hu : u ≠ 0)
    (g : Plane →ₗ[ℝ] ℝ) (hg0 : g ≠ 0) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgX : g X = cg) (hgu : g u = 0) {K : Fin N} {l : Fin 3} (hl : (D.tile K).pts l = X)
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hang : cornerAngle ((D.tile K).pts (l + 1)) ((D.tile K).pts l) ((D.tile K).pts (l + 2)) = θ)
    {ε : ℝ} (hεpos : 0 < ε) (hmem : X + ε • u ∈ (D.tile K).carrier) :
    (∃ t : ℝ, 0 < t ∧ (D.tile K).pts (l + 1) - X = t • u) ∨
      (∃ t : ℝ, 0 < t ∧ (D.tile K).pts (l + 2) - X = t • u) := by
  obtain ⟨s, t, hs, ht, hst⟩ := hull_cone (D.tile K) l _ hmem
  rw [hl] at hst
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile K).pts m ≠ (D.tile K).pts n :=
    fun m n h hh => h ((D.tile K).indep.injective hh)
  have he1 : (D.tile K).pts (l + 1) - X ≠ 0 := by
    rw [sub_ne_zero, ← hl]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) l)).symm
  have he2 : (D.tile K).pts (l + 2) - X ≠ 0 := by
    rw [sub_ne_zero, ← hl]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) l)).symm
  have hg1 : g ((D.tile K).pts (l + 1) - X) ≤ 0 := by
    have := vertex_dir_nonpos D K l (l + 1) g cg hg (by rw [hl]; exact hgX)
    rwa [hl] at this
  have hg2 : g ((D.tile K).pts (l + 2) - X) ≤ 0 := by
    have := vertex_dir_nonpos D K l (l + 2) g cg hg (by rw [hl]; exact hgX)
    rwa [hl] at this
  have hang' : InnerProductGeometry.angle ((D.tile K).pts (l + 1) - X) ((D.tile K).pts (l + 2) - X) = θ := by
    have := hang
    unfold cornerAngle EuclideanGeometry.angle at this
    simp only [vsub_eq_sub] at this
    rw [hl] at this
    exact this
  set e1 := (D.tile K).pts (l + 1) - X with he1def
  set e2 := (D.tile K).pts (l + 2) - X with he2def
  have hεu : ε • u = s • e1 + t • e2 := by
    have : X + ε • u - X = ε • u := by abel
    rw [← this]; exact hst
  have hgε : s * g e1 + t * g e2 = 0 := by
    have := congrArg g hεu
    rw [map_smul, hgu, map_add, map_smul, map_smul] at this
    simp only [smul_eq_mul, mul_zero] at this
    linarith
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · -- `s = 0`
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le ht with h | h
      · exfalso
        rw [← hs0, ← h] at hεu
        simp only [zero_smul, add_zero] at hεu
        exact hu ((smul_eq_zero.mp hεu).resolve_left hεpos.ne')
      · exact h
    right
    have : e2 = (ε / t) • u := by
      calc e2 = t⁻¹ • (t • e2) := by rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
        _ = t⁻¹ • (ε • u) := by rw [← hs0] at hεu; simp only [zero_smul, zero_add] at hεu; rw [hεu]
        _ = (ε / t) • u := by rw [smul_smul]; congr 1; field_simp
    exact ⟨ε / t, by positivity, this⟩
  · rcases eq_or_lt_of_le ht with ht0 | ht0
    · -- `t = 0`
      left
      have : e1 = (ε / s) • u := by
        calc e1 = s⁻¹ • (s • e1) := by rw [smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
          _ = s⁻¹ • (ε • u) := by rw [← ht0] at hεu; simp only [zero_smul, add_zero] at hεu; rw [hεu]
          _ = (ε / s) • u := by rw [smul_smul]; congr 1; field_simp
      exact ⟨ε / s, by positivity, this⟩
    · -- `s, t > 0`: both edges on the line `g = 0`, impossible at an angle in `(0, π)`
      exfalso
      have h1 : g e1 = 0 := by
        nlinarith [mul_nonneg hs0.le (neg_nonneg.mpr hg1), mul_nonneg ht0.le (neg_nonneg.mpr hg2)]
      have h2 : g e2 = 0 := by
        nlinarith [mul_nonneg hs0.le (neg_nonneg.mpr hg1), mul_nonneg ht0.le (neg_nonneg.mpr hg2)]
      exact cross_ne_of_angle' hθ0 hθπ he1 he2 hang' (cross_zero_of_ker g hg0 h1 h2)

/-! ## 4. D0: at a non-vertex frontier point with an `α`-tile and a `γ`-tile, the third presenter is `β` -/

/-- Uniqueness from a cardinality-one count: if exactly one tile presents `θ` at a point (the `Finset` of presenters has
card `1`), any two presenters coincide. -/
theorem unique_of_card_one {N : ℕ} {F : Fin N → ℝ} {θ : ℝ}
    (h : ({i | F i = θ} : Finset (Fin N)).card = 1) {i j : Fin N} (hi : F i = θ) (hj : F j = θ) : i = j := by
  classical
  exact Finset.card_le_one.mp h.le i (by simp [hi]) j (by simp [hj])

/-- **The figure at a `γ`-point** (`GLCForward.forward_tile_2a:112-118`, the `boundary_fan_2alpha` + `cntA` bookkeeping, replaced
by `VertexFigureReal.gamma_boundary_figure_real`): at a non-vertex frontier point `X` of the target where some tile presents
`γ`, exactly one tile presents each of `α`, `β`, `γ` and none is straight. -/
theorem figure_at_gamma_point {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) {X : Plane}
    (hXfr : X ∈ frontier D.target.carrier) (hXnv : X ∉ Set.range D.target.pts)
    {iγ : Fin N} (hiγ : (D.tile iγ).localAngle X = γ) :
    ({i | (D.tile i).localAngle X = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle X = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle X = γ} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle X = Real.pi} : Finset (Fin N)).card = 0 := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := angleFacts hA
  have hvals := Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem_boundary D α β γ
    hM.hα' hM.hβ' hM.hγ' hXfr hXnv
  exact Erdos634.VertexFigureReal.gamma_boundary_figure_real D.toDissection hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hXfr hXnv hvals iγ hiγ

/-- The figure at `X` from a pair of presenters: if two tiles present `α` and `γ` (in either order) at a non-vertex frontier
point `X` of the target, then exactly one tile presents each of `α`, `β`, `γ` and none is straight. -/
theorem figure_of_pair {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) {X : Plane}
    (hXfr : X ∈ frontier D.target.carrier) (hXnv : X ∉ Set.range D.target.pts) {i1 i2 : Fin N}
    (h12 : ((D.tile i1).localAngle X = α ∧ (D.tile i2).localAngle X = γ) ∨
      ((D.tile i1).localAngle X = γ ∧ (D.tile i2).localAngle X = α)) :
    ({i | (D.tile i).localAngle X = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle X = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle X = γ} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle X = Real.pi} : Finset (Fin N)).card = 0 := by
  rcases h12 with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact figure_at_gamma_point hM hA hXfr hXnv h2
  · exact figure_at_gamma_point hM hA hXfr hXnv h1

/-- **D0.**  Let `X` be a frontier point of the target that is not a target vertex, and let two tiles `i1`, `i2` present `α` and
`γ` at `X` (in either order).  Then every tile `K ≠ i1, i2` whose carrier contains `X` presents `β` at `X` (the figure at `X`
is `{α, β, γ}`, one tile each, none straight: `figure_at_gamma_point`). -/
theorem third_presents_beta {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) {X : Plane}
    (hXfr : X ∈ frontier D.target.carrier) (hXnv : X ∉ Set.range D.target.pts) {i1 i2 : Fin N}
    (h12 : ((D.tile i1).localAngle X = α ∧ (D.tile i2).localAngle X = γ) ∨
      ((D.tile i1).localAngle X = γ ∧ (D.tile i2).localAngle X = α))
    {K : Fin N} (hK : X ∈ (D.tile K).carrier) (hK1 : K ≠ i1) (hK2 : K ≠ i2) :
    (D.tile K).localAngle X = β := by
  classical
  obtain ⟨hcα, -, hcγ, hcπ⟩ := figure_of_pair hM hA hXfr hXnv h12
  have hvals := Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem_boundary D α β γ
    hM.hα' hM.hβ' hM.hγ' hXfr hXnv K
  have hne0 := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile K) hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvals
  rcases hvals with h | h | h | h | h
  · exfalso
    rcases h12 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hK1 (unique_of_card_one hcα h h1)
    · exact hK2 (unique_of_card_one hcα h h2)
  · exact h
  · exfalso
    rcases h12 with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hK2 (unique_of_card_one hcγ h h2)
    · exact hK1 (unique_of_card_one hcγ h h1)
  · exfalso
    have hmem : K ∈ ({i | (D.tile i).localAngle X = Real.pi} : Finset (Fin N)) := by simp [h]
    simp [Finset.card_eq_zero.mp hcπ] at hmem
  · exact absurd h hne0

/-- **The `β`-presenter at `X` is unique** (same hypotheses as `third_presents_beta`): any two tiles presenting `β` at `X`
coincide. -/
theorem unique_beta_presenter {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) {X : Plane}
    (hXfr : X ∈ frontier D.target.carrier) (hXnv : X ∉ Set.range D.target.pts) {i1 i2 : Fin N}
    (h12 : ((D.tile i1).localAngle X = α ∧ (D.tile i2).localAngle X = γ) ∨
      ((D.tile i1).localAngle X = γ ∧ (D.tile i2).localAngle X = α))
    {K K' : Fin N} (hK : (D.tile K).localAngle X = β) (hK' : (D.tile K').localAngle X = β) : K = K' :=
  unique_of_card_one (figure_of_pair hM hA hXfr hXnv h12).2.1 hK hK'

/-! ## 5. The forward points are outside the parallelogram -/

/-- GENERALIZATION of `Draft/GLCG1.lean:24 GLC.coord_lin` (from `U.basis.coord m` to any affine functional). -/
theorem aff_lin (ψ : Plane →ᵃ[ℝ] ℝ) (x y z : Plane) (t : ℝ) :
    ψ (x + t • (y - z)) = ψ x + t * (ψ y - ψ z) := by
  have h1 : x + t • (y - z) = (t • (y - z)) +ᵥ x := by rw [vadd_eq_add]; abel
  have h2 : ψ.linear (y - z) = ψ y - ψ z := by
    rw [← vsub_eq_sub, AffineMap.linearMap_vsub]; rfl
  rw [h1, AffineMap.map_vadd, map_smul, h2]
  simp [vadd_eq_add, smul_eq_mul, add_comm]

/-- **The forward points at a vertex of a parallelogram are outside it** (the parallelogram form of
`Draft/GLCG1.lean:33 GLC.fwd_not_mem`, in which the point `U.pts n + ε (U.pts r - U.pts m)` is outside the triangle `U` because
the barycentric coordinate at `m` is `-ε`).  Let `ψ` be an affine functional with `ψ A = 0`, `ψ X = 1`, `ψ Y = 0`.  Then
`ψ ≤ 1` on `A`, `X`, `Y` and on `X + Y - A` (`ψ (X + Y - A) = ψ X + ψ Y - ψ A = 1`), hence on the parallelogram
`hull {A, X, X + Y - A, Y}`, while `ψ (X + δ (X - A)) = 1 + δ > 1`.  So no point `X + δ (X - A)`, `δ > 0`, lies in the
parallelogram.  Used for the corner tile `T_A = hull {A, P, Q}` together with its point reflection `T_3 = hull {P, Q, P + Q - A}`
(`T_A ∪ T_3` is the parallelogram, CP-3's `parallelogram_hull_union`): ONE functional serves both tiles. -/
theorem fwd_not_mem_hull (ψ : Plane →ᵃ[ℝ] ℝ) {A X Y : Plane} (hA : ψ A = 0) (hX : ψ X = 1) (hY : ψ Y = 0)
    {δ : ℝ} (hδ : 0 < δ) : X + δ • (X - A) ∉ convexHull ℝ {A, X, X + Y - A, Y} := by
  intro h
  have hconv : Convex ℝ (ψ ⁻¹' Set.Iic (1 : ℝ)) := (convex_Iic (1 : ℝ)).affine_preimage ψ
  have hR : ψ (X + Y - A) = 1 := by
    have e : X + Y - A = X + (1 : ℝ) • (Y - A) := by rw [one_smul]; abel
    rw [e, aff_lin, hX, hY, hA]; norm_num
  have hsub : ({A, X, X + Y - A, Y} : Set Plane) ⊆ ψ ⁻¹' Set.Iic (1 : ℝ) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_preimage, Set.mem_Iic]
    rcases hx with h | h | h | h
    · rw [h, hA]; norm_num
    · rw [h, hX]
    · rw [h, hR]
    · rw [h, hY]; norm_num
  have h1 := convexHull_min hsub hconv h
  simp only [Set.mem_preimage, Set.mem_Iic] at h1
  rw [aff_lin, hX, hA] at h1
  linarith

/-- CONTROL for `fwd_not_mem_hull`: the strict inequality `δ > 0` is load-bearing: at `δ = 0` the point is the vertex `X`
of the parallelogram. -/
theorem fwd_not_mem_hull_control (A X Y : Plane) :
    X + (0 : ℝ) • (X - A) ∈ convexHull ℝ {A, X, X + Y - A, Y} := by
  rw [zero_smul, add_zero]
  exact subset_convexHull ℝ _ (by simp)

/-- WITNESS for `fwd_not_mem_hull`: its hypotheses are satisfiable (`A = 0`, `X = e₀`, `Y = e₁`, `ψ` the first coordinate),
and the conclusion holds at the concrete point `e₀ + 1 • (e₀ - 0) = 2 e₀`. -/
theorem fwd_not_mem_hull_witness :
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (1 : ℝ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) - 0) : Plane) ∉
      convexHull ℝ {(0 : Plane), EuclideanSpace.single (0 : Fin 2) (1 : ℝ),
        EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + EuclideanSpace.single (1 : Fin 2) (1 : ℝ) - 0,
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} :=
  fwd_not_mem_hull (ψ := ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) : Plane →ₗ[ℝ] ℝ).toAffineMap)
    (by simp) (by simp) (by simp) one_pos

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.inner_coord
#print axioms Erdos634.CornerPara.cross_ne_of_angle'
#print axioms Erdos634.CornerPara.cross_zero_of_ker
#print axioms Erdos634.CornerPara.hull_cone
#print axioms Erdos634.CornerPara.vertex_dir_nonpos
#print axioms Erdos634.CornerPara.forward_cover
#print axioms Erdos634.CornerPara.edge_on_ray
#print axioms Erdos634.CornerPara.unique_of_card_one
#print axioms Erdos634.CornerPara.figure_at_gamma_point
#print axioms Erdos634.CornerPara.figure_of_pair
#print axioms Erdos634.CornerPara.third_presents_beta
#print axioms Erdos634.CornerPara.unique_beta_presenter
#print axioms Erdos634.CornerPara.aff_lin
#print axioms Erdos634.CornerPara.fwd_not_mem_hull
#print axioms Erdos634.CornerPara.fwd_not_mem_hull_control
#print axioms Erdos634.CornerPara.fwd_not_mem_hull_witness
