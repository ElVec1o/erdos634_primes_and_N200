/-
Clamping of the corner chord by the two target sides.  Adapts the pipeline of the γ = 2α and π/3 cases to the
base-β tile.

Lemmas copied (not imported; each copy carries a header line naming file:line):
  Draft/T30LPi3Clamp.lean:20-43       aff_comb, lin_comb, supp_pair, cover3, clamps (Pi3F6.clamps, r<1 weakened to r<=1)
  Draft/T30LPi3F6.lean:29,32,52       fin3_cover, seg_endpoints, third_strict
  Draft/HalfAngle.lean:33             volume_level_line (needed by third_strict; copied so as not to import HalfAngle)
  Draft/T30LPi3F6Corner.lean:95       rayparam
  Draft/T30LPi3Corner.lean:45,59      sum_mem_card, far_chain_single_gen
  (frontier clause: SideWall.edge_subset_frontier replaces Draft/FluxHBreakpointsFrontier.Tri.mem_frontier_of_supporting)
-/
import Erdos634.Draft.CornerParaBase
import Erdos634.Draft.ChordFar
import Erdos634.TP_erdos
import Erdos634.SideWall

/-!
# The corner chord is clamped by the two target sides; the far chain of a `b`-chord is one edge

Adapts the pipeline of the γ = 2α and π/3 cases to the base-β tile.  Everything below is a copy (with the minimal change
named) of a lemma of the `T30L`/`Pi3` pipeline, so that this module does not import `T30LPi3Clamp` / `T30LPi3Corner` /
`T30LPi3F6` / `T30LPi3F6Corner` (to keep the import cone small).  Sources:
* `aff_comb`, `lin_comb`, `supp_pair`, `cover3`     <- `Draft/T30LPi3Clamp.lean:20-41` (verbatim)
* `clamps'`                                           <- `Draft/T30LPi3Clamp.lean:43` `Pi3F6.clamps`, hypothesis
  `r < 1` weakened to `r ≤ 1` (the chord's second end `Q` may a priori be the apex), and the
  frontier clause (originally `FluxHBreakpointsFrontier.Tri.mem_frontier_of_supporting`) discharged
  by `SideWall.edge_subset_frontier` via `side_pt_mem_frontier`
* `seg_endpoints`                                      <- `Draft/T30LPi3F6.lean:32` (verbatim)
* `fin3_cover`, `third_strict`                         <- `Draft/T30LPi3F6.lean:29, 52` (verbatim)
* `volume_level_line`                                  <- `Draft/HalfAngle.lean:33` (verbatim; `third_strict` needs it)
* `rayparam`                                           <- `Draft/T30LPi3F6Corner.lean:95` (verbatim)
* `sum_mem_card`, `far_chain_single_gen`               <- `Draft/T30LPi3Corner.lean:45, 59` (verbatim; the version
  that keeps the cardinality of the chain, unlike `EdgeWordConversion.word_of_chain_sum`)

New here (instances of copied lemmas via `hword_b` and `BaseBetaModel.sideLen_mem`):
* `far_chain_single_b`   -- `far_chain_single_gen` with `hsides := BaseBetaModel.sideLen_mem`,
  `hword := hword_b`, chord length `b`: the far chain of the corner `b`-chord is one edge;
* `far_edge_eq_segment`  -- the single far-chain edge, of the chord's length, is the chord
  (`TPErdos.chain_edge_subset_chord` + `seg_endpoints`), and `far_edge_b` = both together;
* `wall_far_edge_eq_segment` (instance of `far_edge_eq_segment` on the 2-tile wall dissection), next to the copied
  instance section of `Draft/T30LPi3Corner.lean` (`hword_sqrt2`, `wall_sideLen_cases`, `wall_dist_uv`, `wall_far_single`:
  instance of the copied `far_chain_single_gen`; `hword_fails_two`: counterexample when `hword` fails);
* `side_pt_mem_frontier`, `clamps'_instance_r_eq_one` (the weakening is non-vacuous: at `r = 1`, `Q` is a vertex)
  and `clamps'_r_le_one_needed` (at `r = 2`, `Q` is outside `T`).

`clamps'` is instantiated on the triangle `TPErdos.wallTarget`, including the case `r = 1` (`clamps'_instance_r_eq_one`);
`far_chain_single_gen` and `far_edge_eq_segment` are instantiated on the 2-tile dissection
`EdgeWordConversion.wallCongruentDissection` (`wall_far_single`, `wall_far_edge_eq_segment`).  `far_chain_single_b` and
`far_edge_b`, with a clamped corner `b`-chord, are exercised on the N = 44 tiling through the consumers of this module
in `Draft/CornerParaWitnessAux` / `Draft/CornerParaWitness` (`D44_corner_parallelogram`, `D44_corner0_pinned`,
`D44_corner1_pinned`).
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.EdgeWordConversion Erdos634.ChordFar
  Erdos634.TPErdos

/-! ## Barycentric helpers (verbatim copies of `T30LPi3Clamp.lean:20-41`) -/

/-- COPY of `Draft/T30LPi3Clamp.lean:20 aff_comb`. -/
theorem aff_comb (f : Plane →ᵃ[ℝ] ℝ) (P Q : Plane) (a b : ℝ) (hab : a + b = 1) :
    f (a • P + b • Q) = a * f P + b * f Q := by
  have hd : ∀ x, f x = f.linear x + f 0 := fun x => by simpa using congrFun (AffineMap.decomp f) x
  rw [hd (a • P + b • Q), hd P, hd Q]
  simp only [map_add, map_smul, smul_eq_mul]
  linear_combination (-(f 0)) * hab

/-- COPY of `Draft/T30LPi3Clamp.lean:27 lin_comb`. -/
theorem lin_comb (f : Plane →ₗ[ℝ] ℝ) (P Q : Plane) (a b : ℝ) :
    f (a • P + b • Q) = a * f P + b * f Q := by
  simp [map_add, map_smul]

/-- COPY of `Draft/T30LPi3Clamp.lean:31 supp_pair`. -/
theorem supp_pair (T : Tri) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ x ∈ T.carrier, f x ≤ c) ∧
      f (T.pts v) = c ∧ f (T.pts w) = c ∧ f (T.pts z) < c := by
  have h : ∀ v w z : Fin 3, v ≠ w → v ≠ z → w ≠ z →
      ((w = v + 1 ∧ z = v + 2) ∨ (v = w + 1 ∧ z = w + 2)) := by
    decide
  rcases h v w z hvw hvz hwz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact exists_supporting T v
  · obtain ⟨f, c, hf, hle, h1, h2, h3⟩ := exists_supporting T w
    exact ⟨f, c, hf, hle, h2, h1, h3⟩

/-- COPY of `Draft/T30LPi3Clamp.lean:41 cover3`. -/
theorem cover3 : ∀ v w z i : Fin 3, v ≠ w → v ≠ z → w ≠ z → (i = v ∨ i = w ∨ i = z) := by decide

/-! ## M7: `clamps'` — the chord `PQ` between the two sides at `T_v`, with `Q` allowed to be the far vertex -/

/-- **A point of a side lies in the frontier.**  Replaces the flux-import frontier lemma of the original
`Pi3F6.clamps` by `SideWall.edge_subset_frontier`. -/
theorem side_pt_mem_frontier (T : Tri) {v w : Fin 3} (hvw : v ≠ w) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : ((1 - p) • T.pts v + p • T.pts w) ∈ frontier T.carrier := by
  have hmem : (1 - p) • T.pts v + p • T.pts w ∈ segment ℝ (T.pts v) (T.pts w) :=
    ⟨1 - p, p, by linarith, hp0, by ring, rfl⟩
  have h : ∀ v w : Fin 3, v ≠ w → (w = v + 1 ∨ v = w + 1) := by decide
  rcases h v w hvw with rfl | rfl
  · exact Erdos634.SideWall.edge_subset_frontier T v hmem
  · rw [segment_symm] at hmem
    exact Erdos634.SideWall.edge_subset_frontier T w hmem

/-- **M7.**  `Pi3F6.clamps` (`Draft/T30LPi3Clamp.lean:43`) with `r < 1` weakened to `r ≤ 1`.  `T` a triangle,
`v, w, z` distinct vertex indices, `P = (1-p) T_v + p T_w`, `Q = (1-r) T_v + r T_z` with `p ∈ (0,1)`, `r ∈ (0,1]`
(`P` strictly inside the side `vw`; `Q` on the side `vz`, the far vertex `T_z` allowed).  Then the chord `PQ` is
clamped as in `ChordFar.chord_far_sum`: a supporting functional `g` of `T` (side `vw`: `g P = c_g`, `g Q < c_g`) and
`h` (side `vz`: `h Q = c_h`, `h P < c_h`), the open chord lies in the interior of `T`, and `P` is a non-vertex
frontier point.  Only `p < 1` is used for the interior (the coordinate at `v` is `a(1-p) + b(1-r) ≥ a(1-p) > 0`),
`hgQ`, `hhP` use `r > 0`, `p > 0`, and `Q ∈ T.carrier` uses `r ≤ 1`. -/
theorem clamps' (T : Tri) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) {p r : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    let P : Plane := (1 - p) • T.pts v + p • T.pts w
    let Q : Plane := (1 - r) • T.pts v + r • T.pts z
    (∃ (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ), (∀ y ∈ T.carrier, g y ≤ cg) ∧ g P = cg ∧ g Q < cg ∧ g ≠ 0) ∧
    (∃ (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ), (∀ y ∈ T.carrier, h y ≤ ch) ∧ h Q = ch ∧ h P < ch ∧ h ≠ 0) ∧
    openSegment ℝ P Q ⊆ interior T.carrier ∧ P ∈ frontier T.carrier ∧ P ∉ Set.range T.pts ∧
    P ∈ T.carrier ∧ Q ∈ T.carrier := by
  intro P Q
  have hcd : ∀ (i j : Fin 3), T.basis.coord i (T.pts j) = if i = j then 1 else 0 :=
    fun i j => AffineBasis.coord_apply T.basis i j
  have hcP : ∀ i, T.basis.coord i P =
      (1 - p) * (if i = v then 1 else 0) + p * (if i = w then 1 else 0) := by
    intro i
    show T.basis.coord i ((1 - p) • T.pts v + p • T.pts w) = _
    rw [aff_comb _ _ _ _ _ (by ring), hcd, hcd]
  have hcQ : ∀ i, T.basis.coord i Q =
      (1 - r) * (if i = v then 1 else 0) + r * (if i = z then 1 else 0) := by
    intro i
    show T.basis.coord i ((1 - r) • T.pts v + r • T.pts z) = _
    rw [aff_comb _ _ _ _ _ (by ring), hcd, hcd]
  have hPmem : P ∈ T.carrier := by
    rw [T.carrier_eq_nonneg_coord]
    intro i
    rw [hcP]
    split_ifs <;> nlinarith
  have hQmem : Q ∈ T.carrier := by
    rw [T.carrier_eq_nonneg_coord]
    intro i
    rw [hcQ]
    split_ifs <;> nlinarith
  obtain ⟨g, cg, hg0, hgle, hgv, hgw, hgz⟩ := supp_pair T v w z hvw hvz hwz
  obtain ⟨h, ch, hh0, hhle, hhv, hhz, hhw⟩ := supp_pair T v z w hvz hvw hwz.symm
  have hgP : g P = cg := by
    show g ((1 - p) • T.pts v + p • T.pts w) = cg
    rw [lin_comb, hgv, hgw]; ring
  have hgQ : g Q < cg := by
    show g ((1 - r) • T.pts v + r • T.pts z) < cg
    rw [lin_comb, hgv]; nlinarith
  have hhQ : h Q = ch := by
    show h ((1 - r) • T.pts v + r • T.pts z) = ch
    rw [lin_comb, hhv, hhz]; ring
  have hhP : h P < ch := by
    show h ((1 - p) • T.pts v + p • T.pts w) < ch
    rw [lin_comb, hhv]; nlinarith
  refine ⟨⟨g, cg, hgle, hgP, hgQ, hg0⟩, ⟨h, ch, hhle, hhQ, hhP, hh0⟩, ?_, ?_, ?_, hPmem, hQmem⟩
  · -- the open chord is interior: every barycentric coordinate is positive
    have hint : interior T.carrier = {x | ∀ i, 0 < T.basis.coord i x} := by
      have : T.carrier = convexHull ℝ (Set.range (T.basis : Fin 3 → Plane)) := rfl
      rw [this]
      exact AffineBasis.interior_convexHull T.basis
    rw [hint]
    rintro y ⟨a, b, ha, hb, hab, rfl⟩ i
    rw [aff_comb _ _ _ _ _ hab, hcP, hcQ]
    rcases cover3 v w z i hvw hvz hwz with rfl | rfl | rfl
    · simp [hvw, hvz]
      nlinarith [mul_pos ha (sub_pos.mpr hp1), mul_nonneg hb.le (sub_nonneg.mpr hr1)]
    · simp [hvw.symm, hwz]
      nlinarith [mul_pos ha hp0]
    · simp [hvz.symm, hwz.symm]
      nlinarith [mul_pos hb hr0]
  · exact side_pt_mem_frontier T hvw hp0.le hp1.le
  · rintro ⟨m, hm⟩
    have h1 := hcP v
    rw [← hm, hcd] at h1
    have hv1 : (if v = v then (1 : ℝ) else 0) = 1 := by simp
    rw [hv1] at h1
    simp only [hvw, if_false] at h1
    by_cases hmv : v = m
    · rw [if_pos hmv] at h1; nlinarith
    · rw [if_neg hmv] at h1; nlinarith

/-! ## Pure convexity / ray lemmas (verbatim copies) -/

/-- COPY of `Draft/T30LPi3F6.lean:32 seg_endpoints`.  A sub-segment of `[P,Q]` of full length has the endpoints
of `[P,Q]`. -/
theorem seg_endpoints {X Y P Q : Plane} (hPQ : P ≠ Q) (hX : X ∈ segment ℝ P Q)
    (hY : Y ∈ segment ℝ P Q) (hd : dist X Y = dist P Q) : (X = P ∧ Y = Q) ∨ (X = Q ∧ Y = P) := by
  rw [segment_eq_image_lineMap] at hX hY
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hX
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hY
  rw [dist_lineMap_lineMap] at hd
  have hpos : 0 < dist P Q := dist_pos.mpr hPQ
  have h1 : dist s t = 1 := by
    have : dist s t * dist P Q = 1 * dist P Q := by rw [hd, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  rw [Real.dist_eq] at h1
  rcases abs_cases (s - t) with ⟨h, _⟩ | ⟨h, _⟩
  · have hs : s = 1 := by linarith
    have ht : t = 0 := by linarith
    right; subst hs; subst ht; simp
  · have hs : s = 0 := by linarith
    have ht : t = 1 := by linarith
    left; subst hs; subst ht; simp

/-- COPY of `Draft/T30LPi3F6.lean:29 fin3_cover`. -/
theorem fin3_cover : ∀ k i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide

/-- COPY of `Draft/HalfAngle.lean:33 volume_level_line`.  The level line of a nonzero functional is Lebesgue-null. -/
theorem volume_level_line (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) {p : Plane} (c : ℝ) (hp : f p = c) :
    MeasureTheory.volume {y : Plane | f y = c} = 0 := by
  have hker : LinearMap.ker f ≠ ⊤ := fun h => hf (LinearMap.ker_eq_top.mp h)
  have hpre : (fun v : Plane => p + v) ⁻¹' {y : Plane | f y = c} = (LinearMap.ker f : Set Plane) := by
    ext v; simp [hp]
  have := MeasureTheory.Measure.addHaar_submodule (MeasureTheory.volume : MeasureTheory.Measure Plane) _ hker
  rw [← MeasureTheory.measure_preimage_add (MeasureTheory.volume : MeasureTheory.Measure Plane) p
    {y : Plane | f y = c}, hpre]
  exact this

/-- COPY of `Draft/T30LPi3F6.lean:52 third_strict`.  The third vertex is strictly off the line: if two vertices
`U_k, U_{k+1}` of a tile lie on `{f = c₀}` and the tile is in `{f ≤ c₀}`, then `f (U_{k+2}) < c₀`. -/
theorem third_strict (U : Tri) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c0 : ℝ)
    (hle : ∀ i, f (U.pts i) ≤ c0) (k : Fin 3) (h1 : f (U.pts k) = c0)
    (h2 : f (U.pts (k + 1)) = c0) : f (U.pts (k + 2)) < c0 := by
  by_contra hnot
  have h3 : f (U.pts (k + 2)) = c0 := le_antisymm (hle _) (not_lt.mp hnot)
  have hall : ∀ i, f (U.pts i) = c0 := by
    intro i
    have : i = k ∨ i = k + 1 ∨ i = k + 2 := fin3_cover k i
    rcases this with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hconv : Convex ℝ {y : Plane | f y = c0} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx, hy, ← add_mul, hab, one_mul]
  have hsub : U.carrier ⊆ {y : Plane | f y = c0} := by
    refine convexHull_min ?_ hconv
    rintro z ⟨i, rfl⟩
    exact hall i
  have hv := U.volume_pos
  have h0 := volume_level_line f hf c0 (hall 0)
  exact absurd (MeasureTheory.measure_mono_null hsub h0) hv.ne'

/-- COPY of `Draft/T30LPi3F6Corner.lean:95 rayparam`.  Two vectors on the same ray are a positive multiple
of one another. -/
theorem rayparam {u e : Plane} (hu : u ≠ 0) (he : e ≠ 0) (h : SameRay ℝ u e) :
    ∃ p : ℝ, 0 < p ∧ e = p • u := by
  obtain ⟨r1, r2, h1, h2, h12⟩ := h.exists_pos hu he
  refine ⟨r1 / r2, div_pos h1 h2, ?_⟩
  have : e = (1 / r2) • (r1 • u) := by
    rw [h12, smul_smul, one_div, inv_mul_cancel₀ h2.ne', one_smul]
  rw [this, smul_smul]; congr 1; ring

/-! ## M8: the far chain of a clamped chord is a single edge, given the word lemma -/

/-- COPY of `Draft/T30LPi3Corner.lean:45 sum_mem_card`.  A sum of terms in `{a,b,c}`: `x a + y b + z c` with
`x + y + z` the number of terms. -/
theorem sum_mem_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) (a b c : ℝ)
    (h : ∀ i ∈ s, g i = a ∨ g i = b ∨ g i = c) :
    ∃ x y z : ℕ, (x : ℝ) * a + y * b + z * c = ∑ i ∈ s, g i ∧ x + y + z = s.card := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp, by simp⟩
  | insert i s hi ih =>
    obtain ⟨x, y, z, hxyz, hc⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    rcases h i (Finset.mem_insert_self i s) with hg | hg | hg
    · exact ⟨x + 1, y, z, by rw [hg]; push_cast; linarith, by omega⟩
    · exact ⟨x, y + 1, z, by rw [hg]; push_cast; linarith, by omega⟩
    · exact ⟨x, y, z + 1, by rw [hg]; push_cast; linarith, by omega⟩

/-- COPY of `Draft/T30LPi3Corner.lean:59 far_chain_single_gen` (hypotheses exactly as there).  **The far chain of a
chord is a single edge, given the word lemma**: for a `CongruentDissection` whose model sides are among
`s0, s1, s2`, a chord of length `L` clamped on the target as in `ChordFar.chord_far_sum_cong`, and `hword`
(`x s0 + y s1 + z s2 = L → x + y + z = 1`), the far chain `lineChain (-f) (-c)` consists of exactly ONE edge, of
length `L`. -/
theorem far_chain_single_gen {N : ℕ} (D : CongruentDissection N) {s0 s1 s2 L : ℝ}
    (hsides : ∀ i : Fin 3, sideLen D i = s0 ∨ sideLen D i = s1 ∨ sideLen D i = s2)
    (hword : ∀ x y z : ℕ, (x : ℝ) * s0 + y * s1 + z * s2 = L → x + y + z = 1)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = L) :
    ∃ e₀ ∈ D.lineChain (-f) (-c), D.lineChain (-f) (-c) = {e₀} ∧
      dist ((D.tile e₀.1).pts e₀.2) ((D.tile e₀.1).pts (e₀.2 + 1)) = L := by
  have hsum := chord_far_sum_cong D f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall
  rw [hdist] at hsum
  have hmem : ∀ e ∈ D.lineChain (-f) (-c),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = s0 ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = s1 ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = s2 := by
    intro e _
    rcases edge_length_trichotomy D e.1 e.2 with h' | h' | h'
    · rw [h']; exact hsides 0
    · rw [h']; exact hsides 1
    · rw [h']; exact hsides 2
  obtain ⟨x, y, z, hxyz, hcard⟩ := sum_mem_card (D.lineChain (-f) (-c))
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) s0 s1 s2 hmem
  have h1 := hword x y z (by rw [hxyz]; exact hsum)
  obtain ⟨e₀, he⟩ := Finset.card_eq_one.mp (by omega : (D.lineChain (-f) (-c)).card = 1)
  refine ⟨e₀, by rw [he]; simp, he, ?_⟩
  rw [he, Finset.sum_singleton] at hsum
  exact hsum

/-! ## M8 instantiated at the base-β model: the far chain of a `b`-chord is one edge, and it is the chord -/

/-- **The far chain of a clamped `b`-chord is a single edge** (`far_chain_single_gen` with `hsides` from
`BaseBetaModel.sideLen_mem` (M4), `hword` from `hword_b` (M3), `L = b = sideOpp D.model 1`). -/
theorem far_chain_single_b {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (φ : Plane →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hφP : φ P = c) (hφQ : φ Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = sideOpp D.model 1) :
    ∃ e₀ ∈ D.lineChain (-φ) (-c), D.lineChain (-φ) (-c) = {e₀} ∧
      dist ((D.tile e₀.1).pts e₀.2) ((D.tile e₀.1).pts (e₀.2 + 1)) = sideOpp D.model 1 := by
  have hL : sideOpp D.model 1 = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := hM.hs1
  obtain ⟨e₀, he₀, hchain, hlen⟩ := far_chain_single_gen D (s0 := s * ((e : ℝ) * f))
    (s1 := s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (s2 := s * (f : ℝ) ^ 2)
    (L := s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) hM.sideLen_mem (hword_b hco he hef hM.hs)
    φ hφ c hPQ hφP hφQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall (hdist.trans hL)
  exact ⟨e₀, he₀, hchain, hlen.trans hL.symm⟩

/-- **A far-chain edge of the chord's full length IS the chord** (plan B4).  By `chain_edge_subset_chord` the edge
lies in `segment P Q`, and by `seg_endpoints` an edge of full length in `[P,Q]` has the endpoints of `[P,Q]`. -/
theorem far_edge_eq_segment {N : ℕ} (D : Dissection N) (φ : Plane →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (c : ℝ)
    {P Q : Plane} (hPQ : P ≠ Q) (hφP : φ P = c) (hφQ : φ Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    {e₀ : Fin N × Fin 3} (he₀ : e₀ ∈ D.lineChain (-φ) (-c))
    (hlen : dist ((D.tile e₀.1).pts e₀.2) ((D.tile e₀.1).pts (e₀.2 + 1)) = dist P Q) :
    (D.tile e₀.1).edge e₀.2 = segment ℝ P Q := by
  have hsub := chain_edge_subset_chord D (-φ) (neg_ne_zero.mpr hφ) (-c) hPQ (by simp [hφP])
    (by simp [hφQ]) g cg hg hgP hgQ h ch hh hhQ hhP he₀
  have hX : (D.tile e₀.1).pts e₀.2 ∈ segment ℝ P Q := hsub (left_mem_segment ℝ _ _)
  have hY : (D.tile e₀.1).pts (e₀.2 + 1) ∈ segment ℝ P Q := hsub (right_mem_segment ℝ _ _)
  rcases seg_endpoints hPQ hX hY hlen with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · show segment ℝ _ _ = _
    rw [h1, h2]
  · show segment ℝ _ _ = _
    rw [h1, h2, segment_symm]

/-- **B3 + B4 for the base-β `b`-chord**: the far chain of a clamped `b`-chord `[P,Q]` is ONE edge `e₀`, and that
edge is exactly the segment `[P,Q]`. -/
theorem far_edge_b {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (φ : Plane →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hφP : φ P = c) (hφQ : φ Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = sideOpp D.model 1) :
    ∃ e₀ ∈ D.lineChain (-φ) (-c), D.lineChain (-φ) (-c) = {e₀} ∧
      (D.tile e₀.1).edge e₀.2 = segment ℝ P Q := by
  obtain ⟨e₀, he₀, hchain, hlen⟩ := far_chain_single_b hM hco he hef φ hφ c hPQ hφP hφQ g cg hg hgP
    hgQ h ch hh hhQ hhP hint hwall hdist
  exact ⟨e₀, he₀, hchain, far_edge_eq_segment D.toDissection φ hφ c hPQ hφP hφQ g cg hg hgP hgQ h ch hh
    hhQ hhP he₀ (hlen.trans hdist.symm)⟩

/-! ## Witness: `far_chain_single_gen` and `far_edge_eq_segment` on a real dissection

The same real witness as the original (`Draft/T30LPi3Corner.lean`, section `witness`): the 2-tile dissection
`EdgeWordConversion.wallCongruentDissection` (sides `√2, √2, 2`), median chord `[wallU, wallV]` of length `√2`,
clamped by the base and the hypotenuse, with `hword` from the irrationality of `√2`.  This shows the hypotheses of the
COPIES are jointly satisfiable (not just those of the originals), and that the conclusion is a real single edge. -/

section witness

open Erdos634.CertCoord

/-- COPY of `Draft/T30LPi3Corner.lean:121 hword_sqrt2`. -/
theorem hword_sqrt2 (x y z : ℕ)
    (h : (x : ℝ) * Real.sqrt 2 + y * Real.sqrt 2 + z * 2 = Real.sqrt 2) : x + y + z = 1 := by
  have hs := irrational_sqrt_two
  have h1 : (((x : ℤ) + y - 1 : ℤ) : ℝ) * Real.sqrt 2 = -(2 * z) := by push_cast; linarith
  have hxy : (x : ℤ) + y - 1 = 0 := by
    by_contra hne
    apply hs
    refine ⟨(-(2 * (z : ℚ))) / (((x : ℤ) + y - 1 : ℤ) : ℚ), ?_⟩
    have hm : (((x : ℤ) + y - 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
    push_cast at hm h1 ⊢
    field_simp
    linarith
  have hz : (z : ℝ) = 0 := by
    have : (((x : ℤ) + y - 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hxy
    rw [this] at h1; linarith
  have hz' : z = 0 := by exact_mod_cast hz
  omega

/-- Copy of `Draft/T30LPi3Corner.lean:139 hword_fails_two`: for the chord `2√2` the arithmetic
hypothesis `hword` fails, so the single-edge conclusion of `far_chain_single_gen` needs it. -/
theorem hword_fails_two : ∃ x y z : ℕ,
    (x : ℝ) * Real.sqrt 2 + y * Real.sqrt 2 + z * 2 = 2 * Real.sqrt 2 ∧ x + y + z ≠ 1 :=
  ⟨2, 0, 0, by push_cast; ring, by norm_num⟩

/-- COPY of `Draft/T30LPi3Corner.lean wall_sideLen_cases`. -/
theorem wall_sideLen_cases (i : Fin 3) :
    sideLen wallCongruentDissection i = Real.sqrt 2 ∨ sideLen wallCongruentDissection i = Real.sqrt 2
      ∨ sideLen wallCongruentDissection i = 2 := by
  have hsq : ∀ d : ℝ, 0 ≤ d → d ^ 2 = 2 → d = Real.sqrt 2 := fun d hd h => by
    rw [← h, Real.sqrt_sq hd]
  fin_cases i
  · left
    have h : dist (mkPt 0 0) (mkPt 1 1) ^ 2 = 2 := by rw [dist_sq_mkPt]; norm_num
    exact hsq _ dist_nonneg h
  · left
    have h : dist (mkPt 1 1) (mkPt 2 0) ^ 2 = 2 := by rw [dist_sq_mkPt]; norm_num
    exact hsq _ dist_nonneg h
  · right; right
    have h : dist (mkPt 2 0) (mkPt 0 0) ^ 2 = 2 ^ 2 := by rw [dist_sq_mkPt]; norm_num
    exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h

/-- COPY of `Draft/T30LPi3Corner.lean wall_dist_uv`. -/
theorem wall_dist_uv : dist wallU wallV = Real.sqrt 2 := by
  have h : dist wallU wallV ^ 2 = 2 := by
    rw [wallU, wallV, dist_sq_mkPt]; norm_num
  rw [← h, Real.sqrt_sq dist_nonneg]

/-- COPY of `Draft/T30LPi3Corner.lean wall_far_single`.  **Witness for `far_chain_single_gen` (the copy).**  The far
side of the median chord of the 2-tile wall dissection is a single edge of length `√2`. -/
theorem wall_far_single :
    ∃ e₀ ∈ wallCongruentDissection.lineChain (-wallF) (-0),
      wallCongruentDissection.lineChain (-wallF) (-0) = {e₀} ∧
      dist ((wallCongruentDissection.tile e₀.1).pts e₀.2)
        ((wallCongruentDissection.tile e₀.1).pts (e₀.2 + 1)) = Real.sqrt 2 :=
  far_chain_single_gen wallCongruentDissection wall_sideLen_cases hword_sqrt2
    wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num) wall_hint wall_hwall wall_dist_uv

/-- **Witness for `far_edge_eq_segment`.**  On the same dissection the single far-chain edge IS the chord
`[wallU, wallV]` (so the hypotheses of `far_edge_eq_segment` are satisfiable and its conclusion is an actual
set equality of a tile edge with the chord). -/
theorem wall_far_edge_eq_segment :
    ∃ e₀ ∈ wallCongruentDissection.lineChain (-wallF) (-0),
      (wallCongruentDissection.tile e₀.1).edge e₀.2 = segment ℝ wallU wallV := by
  obtain ⟨e₀, he₀, -, hlen⟩ := wall_far_single
  exact ⟨e₀, he₀, far_edge_eq_segment wallCongruentDissection.toDissection wallF wallF_ne 0
    wallU_ne_wallV wallF_u wallF_v gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num) hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num) he₀ (hlen.trans wall_dist_uv.symm)⟩

end witness

/-! ## Non-vacuity and controls for the weakening `r < 1 → r ≤ 1`

On the concrete triangle `TPErdos.wallTarget` (vertices `(0,0), (2,0), (0,2)`), with `v, w, z = 0, 1, 2`,
`p = 1/2`: at `r = 1`, `Q` is the vertex `(0,2)` — exactly the case `Pi3F6.clamps` (`r < 1`) excluded — and the
conclusions of `clamps'` still hold; at `r = 2`, `Q` leaves the triangle, so `r ≤ 1` is load-bearing. -/

/-- The weakened hypothesis is satisfiable with `Q` a target vertex (the new case), on a concrete triangle. -/
theorem clamps'_instance_r_eq_one :
    (let P : Plane := (1 - (1 / 2 : ℝ)) • wallTarget.pts 0 + (1 / 2 : ℝ) • wallTarget.pts 1
     let Q : Plane := (1 - (1 : ℝ)) • wallTarget.pts 0 + (1 : ℝ) • wallTarget.pts 2
     openSegment ℝ P Q ⊆ interior wallTarget.carrier ∧ P ∈ frontier wallTarget.carrier ∧
       P ∉ Set.range wallTarget.pts ∧ Q ∈ Set.range wallTarget.pts) := by
  intro P Q
  obtain ⟨-, -, hint, hfr, hnv, -, -⟩ := clamps' wallTarget 0 1 2 (by decide) (by decide) (by decide)
    (p := 1 / 2) (r := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl
  refine ⟨hint, hfr, hnv, ⟨2, ?_⟩⟩
  show wallTarget.pts 2 = (1 - (1 : ℝ)) • wallTarget.pts 0 + (1 : ℝ) • wallTarget.pts 2
  simp

/-- **Sharpness of `r ≤ 1`.**  At `r = 2` the point `Q = (1-2) T_v + 2 T_z` is not in the triangle (its
barycentric coordinate at `v` is `-1`), so the conclusion `Q ∈ T.carrier` of `clamps'` fails: the weakening
cannot be pushed past `r ≤ 1`. -/
theorem clamps'_r_le_one_needed (T : Tri) (v z : Fin 3) (hvz : v ≠ z) :
    ((1 - (2 : ℝ)) • T.pts v + (2 : ℝ) • T.pts z) ∉ T.carrier := by
  intro hQ
  have hcd : ∀ (i j : Fin 3), T.basis.coord i (T.pts j) = if i = j then 1 else 0 :=
    fun i j => AffineBasis.coord_apply T.basis i j
  rw [T.carrier_eq_nonneg_coord] at hQ
  have h := hQ v
  rw [aff_comb _ _ _ _ _ (by ring), hcd, hcd] at h
  simp [hvz] at h

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.aff_comb
#print axioms Erdos634.CornerPara.lin_comb
#print axioms Erdos634.CornerPara.supp_pair
#print axioms Erdos634.CornerPara.cover3
#print axioms Erdos634.CornerPara.side_pt_mem_frontier
#print axioms Erdos634.CornerPara.clamps'
#print axioms Erdos634.CornerPara.seg_endpoints
#print axioms Erdos634.CornerPara.fin3_cover
#print axioms Erdos634.CornerPara.volume_level_line
#print axioms Erdos634.CornerPara.third_strict
#print axioms Erdos634.CornerPara.rayparam
#print axioms Erdos634.CornerPara.sum_mem_card
#print axioms Erdos634.CornerPara.far_chain_single_gen
#print axioms Erdos634.CornerPara.far_chain_single_b
#print axioms Erdos634.CornerPara.far_edge_eq_segment
#print axioms Erdos634.CornerPara.far_edge_b
#print axioms Erdos634.CornerPara.hword_sqrt2
#print axioms Erdos634.CornerPara.hword_fails_two
#print axioms Erdos634.CornerPara.wall_sideLen_cases
#print axioms Erdos634.CornerPara.wall_dist_uv
#print axioms Erdos634.CornerPara.wall_far_single
#print axioms Erdos634.CornerPara.wall_far_edge_eq_segment
#print axioms Erdos634.CornerPara.clamps'_instance_r_eq_one
#print axioms Erdos634.CornerPara.clamps'_r_le_one_needed
