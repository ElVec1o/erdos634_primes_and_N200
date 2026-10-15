import Mathlib.Tactic
import Erdos634.Draft.T30LL3SideTile
import Erdos634.Draft.T30LL3Far

/-!
# (L3) at a doubled corner

`l3_corner`: on a `CongruentDissection` with `SixtyData` model, `α ∉ ℚπ`, `a, b, c` pairwise distinct, and the word lemma for `2c`
(`x a + y b + z c = 2 c → (x,y,z) = (0,0,2)`), let `T = {O, P, Q}` be a tile with a `π/3` vertex at a target corner `O` and `P, Q` on the two target sides, `|OP| = a`,
`|OQ| = b`, neither `2a` nor `2b` a side length.  If the second tile on the `P`-side has a `π/3` vertex at `P` with a side edge of length `a`, and the second tile on the `Q`-side has a `π/3`
vertex at `Q` with a side edge of length `b` (the doubled corner), then there is a tile with a `π/3` vertex at `P₂ = 2P - O` and an edge along the `P`-side, forward; its side
edge is `a` or `b` (never `c`): the third edge on that side is not a `c`-edge.
Chain (all derived here): `side_tile_full` (`T₃ = T + (P-O)` with vertices `P, P₂, Z`, `Z = P + Q - O`; `T₄ = T + (Q-O)` with vertices `Q, Q₁, Z`);
`clamps` for `P₂, Q₁`; the doubled chord `P₂Q₁` is the union of the tile edges `P₂Z`, `ZQ₁` (wall); `far_edge_at_end` (a far-chain tile `Kc` with the edge `[P₂, Z]`); `angles_differ`
(`Kc` presents `α` at `P₂`, since `T₃` presents `β`); `l3_fill` (the fan forces a `π/3` tile along the side).
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.ChordFar Erdos634.SectorFill

set_option maxHeartbeats 3200000 in
theorem l3_corner {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b)
    (hword2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = 2 * c → x = 0 ∧ y = 0 ∧ z = 2)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = Real.pi / 3)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hOP : dist (D.target.pts v) ((D.tile i).pts (j + 1)) = a)
    (hOQ : dist (D.target.pts v) ((D.tile i).pts (j + 2)) = b)
    (h2a : dist (D.target.pts v) (D.target.pts w) ≠ 2 * a)
    (h2b : dist (D.target.pts v) (D.target.pts z) ≠ 2 * b)
    (hK3 : SideTileLen D ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 1) - D.target.pts v) a)
    (hK4 : SideTileLen D ((D.tile i).pts (j + 2)) ((D.tile i).pts (j + 2) - D.target.pts v) b) :
    SideTile D ((D.tile i).pts (j + 1) + ((D.tile i).pts (j + 1) - D.target.pts v))
      ((D.tile i).pts (j + 1) - D.target.pts v) a b := by
  classical
  have hpi := Real.pi_pos
  set T := D.target with hT
  set P := (D.tile i).pts (j + 1) with hPdef
  set Q := (D.tile i).pts (j + 2) with hQdef
  set O := T.pts v with hO
  have hPform : P = (1 - p) • T.pts v + p • T.pts w := by
    have : P = T.pts v + p • (T.pts w - T.pts v) := by rw [← hP]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hQform : Q = (1 - r) • T.pts v + r • T.pts z := by
    have : Q = T.pts v + r • (T.pts z - T.pts v) := by rw [← hQ]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hu : P - O ≠ 0 := by
    rw [sub_ne_zero, ← hjv]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hq : Q - O ≠ 0 := by
    rw [sub_ne_zero, ← hjv]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hang' : InnerProductGeometry.angle (P - O) (Q - O) = Real.pi / 3 := by
    have := hang
    unfold Tri.angleAt cornerAngle EuclideanGeometry.angle at this
    simp only [vsub_eq_sub] at this
    rw [hjv] at this
    exact this
  have hnu : ‖P - O‖ = a := by rw [← dist_eq_norm, dist_comm]; exact hOP
  have hnq : ‖Q - O‖ = b := by rw [← dist_eq_norm, dist_comm]; exact hOQ
  have hPQc : dist P Q = c := by
    have := opp_c_of_pi3 hirr (tile_sixty D hS i) j hang
    unfold Tri.oppLen at this
    exact this
  -- supporting functionals of the two sides
  obtain ⟨g, cg, hg0, hgle, hgv, hgw, hgz⟩ := supp_pair T v w z hvw hvz hwz
  obtain ⟨h, ch, hh0, hhle, hhv, hhz, hhw⟩ := supp_pair T v z w hvz hvw hwz.symm
  have hgP : g P = cg := by rw [hPform, lin_comb, hgv, hgw]; ring
  have hgQ : g Q < cg := by
    rw [hQform, lin_comb, hgv]; nlinarith [mul_pos hr0 (sub_pos.mpr hgz)]
  have hhQ : h Q = ch := by rw [hQform, lin_comb, hhv, hhz]; ring
  have hhP : h P < ch := by
    rw [hPform, lin_comb, hhv]; nlinarith [mul_pos hp0 (sub_pos.mpr hhw)]
  have hgu : g (P - O) = 0 := by rw [map_sub, hgP, hgv]; ring
  have hgq : g (Q - O) < 0 := by rw [map_sub, hgv]; linarith
  have hhq : h (Q - O) = 0 := by rw [map_sub, hhQ, hhv]; ring
  have hhp : h (P - O) < 0 := by rw [map_sub, hhv]; linarith
  -- the two second tiles
  obtain ⟨K3, m3, hK3m, hK3v, hK3ang⟩ := side_tile_full D hirr hS hac hbc hab hu (Or.inl ⟨hnu, hnq⟩) hang' g hgu hgq
    (fun y hy => by rw [hgP]; exact hgle y hy) (by rw [hnu]; exact hK3)
  obtain ⟨K4, m4, hK4m, hK4v, -⟩ := side_tile_full D hirr hS hac hbc hab hq (Or.inr ⟨hnq, hnu⟩)
    (by rw [InnerProductGeometry.angle_comm]; exact hang') h hhq hhp
    (fun y hy => by rw [hhQ]; exact hhle y hy) (by rw [hnq]; exact hK4)
  have hK3β := hK3ang hnq
  have hZ : Q + (P - O) = P + (Q - O) := by abel
  rw [hZ] at hK4v
  -- `2p < 1`, `2r < 1`
  have hP2form : P + (P - O) = (1 - 2 * p) • T.pts v + (2 * p) • T.pts w := by
    rw [hPform, hO]; module
  have hQ1form : Q + (Q - O) = (1 - 2 * r) • T.pts v + (2 * r) • T.pts z := by
    rw [hQform, hO]; module
  have hP2mem : P + (P - O) ∈ T.carrier := by
    have h1 : P + (P - O) ∈ (D.tile K3).carrier := by
      rw [← hK3m]; exact subset_convexHull ℝ _ ⟨m3, rfl⟩
    exact Erdos634.BaseSelection.tile_subset_target D.toDissection K3 h1
  have hQ1mem : Q + (Q - O) ∈ T.carrier := by
    have h1 : Q + (Q - O) ∈ (D.tile K4).carrier := by
      rw [← hK4m]; exact subset_convexHull ℝ _ ⟨m4, rfl⟩
    exact Erdos634.BaseSelection.tile_subset_target D.toDissection K4 h1
  have hdw : a = p * dist (T.pts v) (T.pts w) := by
    rw [← hnu, hP, norm_smul, Real.norm_eq_abs, abs_of_pos hp0, ← dist_eq_norm, dist_comm]
  have hdz : b = r * dist (T.pts v) (T.pts z) := by
    rw [← hnq, hQ, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, ← dist_eq_norm, dist_comm]
  have hp2 : 2 * p < 1 := by
    have hmem' := hP2mem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v (P + (P - O)) := hmem' v
    rw [hP2form, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvw] at hnn
    rcases lt_or_eq_of_le (by linarith : 2 * p ≤ 1) with h' | h'
    · exact h'
    · exfalso
      apply h2a
      have hp' : p = 1 / 2 := by linarith
      rw [hp'] at hdw; linarith
  have hr2 : 2 * r < 1 := by
    have hmem' := hQ1mem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v (Q + (Q - O)) := hmem' v
    rw [hQ1form, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvz] at hnn
    rcases lt_or_eq_of_le (by linarith : 2 * r ≤ 1) with h' | h'
    · exact h'
    · exfalso
      apply h2b
      have hr' : r = 1 / 2 := by linarith
      rw [hr'] at hdz; linarith
  -- clamps of the doubled chord
  obtain ⟨⟨g1, cg1, hg1, hg1P, hg1Q, -⟩, ⟨h1, ch1, hh1, hh1Q, hh1P, -⟩, hint0, hfr0, hnv0, -, -⟩ :=
    clamps T v w z hvw hvz hwz (p := 2 * p) (r := 2 * r) (by positivity) hp2 (by positivity) hr2
  have hg1P' : g1 (P + (P - O)) = cg1 := by rw [hP2form]; exact hg1P
  have hg1Q' : g1 (Q + (Q - O)) < cg1 := by rw [hQ1form]; exact hg1Q
  have hh1Q' : h1 (Q + (Q - O)) = ch1 := by rw [hQ1form]; exact hh1Q
  have hh1P' : h1 (P + (P - O)) < ch1 := by rw [hP2form]; exact hh1P
  have hint : openSegment ℝ (P + (P - O)) (Q + (Q - O)) ⊆ interior T.carrier := by
    rw [hP2form, hQ1form]; exact hint0
  have hVfr : P + (P - O) ∈ frontier T.carrier := by rw [hP2form]; exact hfr0
  have hVnv : P + (P - O) ∉ Set.range T.pts := by rw [hP2form]; exact hnv0
  have hPQ : P + (P - O) ≠ Q + (Q - O) := by
    intro he; rw [he] at hg1P'; linarith
  -- the chord functional from the c-edge `[P₂, Z]` of `T₃`
  obtain ⟨f, c0, hf0, hfle, hfP2, hfZ, hfPl⟩ : ∃ (f : Plane →ₗ[ℝ] ℝ) (c0 : ℝ), f ≠ 0 ∧
      (∀ y ∈ (D.tile K3).carrier, f y ≤ c0) ∧ f (P + (P - O)) = c0 ∧ f (P + (Q - O)) = c0 ∧ f P < c0 := by
    rcases hK3v with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · obtain ⟨f, c0, hf, hle, h1', h2', h3'⟩ := exists_supporting (D.tile K3) (m3 + 2)
      have a1 : m3 + 2 + 1 = m3 := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) m3
      have a2 : m3 + 2 + 2 = m3 + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) m3
      rw [a1, hK3m] at h2'
      rw [a2, e1] at h3'
      rw [e2] at h1'
      exact ⟨f, c0, hf, hle, h2', h1', h3'⟩
    · obtain ⟨f, c0, hf, hle, h1', h2', h3'⟩ := exists_supporting (D.tile K3) m3
      rw [hK3m] at h1'
      rw [e1] at h2'
      rw [e2] at h3'
      exact ⟨f, c0, hf, hle, h1', h2', h3'⟩
  have hfQ1 : f (Q + (Q - O)) = c0 := by
    have : Q + (Q - O) = (2 : ℝ) • (P + (Q - O)) - (P + (P - O)) := by module
    rw [this, map_sub, map_smul, hfZ, hfP2]; simp only [smul_eq_mul]; ring
  have hdist : dist (P + (P - O)) (Q + (Q - O)) = 2 * c := by
    rw [dist_eq_norm]
    have : P + (P - O) - (Q + (Q - O)) = (2 : ℝ) • (P - Q) := by module
    have h2n : ‖(2 : ℝ)‖ = 2 := by simp
    rw [this, norm_smul, ← dist_eq_norm, hPQc, h2n]
  have hmZ : midpoint ℝ (P + (P - O)) (Q + (Q - O)) = P + (Q - O) := by
    rw [midpoint_eq_smul_add]; simp only [invOf_eq_inv]; module
  -- the doubled chord is a wall: union of the tile edges `P₂Z` (of `T₃`) and `ZQ₁` (of `T₄`)
  obtain ⟨k3, hk3⟩ : ∃ k, (D.tile K3).edge k = segment ℝ (P + (P - O)) (P + (Q - O)) := by
    rcases hK3v with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · obtain ⟨k, hk⟩ := pair_edge (D.tile K3) m3 (m3 + 2) ((by decide : ∀ x : Fin 3, x ≠ x + 2) m3)
      exact ⟨k, by rw [hk, hK3m, e2]⟩
    · obtain ⟨k, hk⟩ := pair_edge (D.tile K3) m3 (m3 + 1) ((by decide : ∀ x : Fin 3, x ≠ x + 1) m3)
      exact ⟨k, by rw [hk, hK3m, e1]⟩
  obtain ⟨k4, hk4⟩ : ∃ k, (D.tile K4).edge k = segment ℝ (Q + (Q - O)) (P + (Q - O)) := by
    rcases hK4v with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · obtain ⟨k, hk⟩ := pair_edge (D.tile K4) m4 (m4 + 2) ((by decide : ∀ x : Fin 3, x ≠ x + 2) m4)
      exact ⟨k, by rw [hk, hK4m, e2]⟩
    · obtain ⟨k, hk⟩ := pair_edge (D.tile K4) m4 (m4 + 1) ((by decide : ∀ x : Fin 3, x ≠ x + 1) m4)
      exact ⟨k, by rw [hk, hK4m, e1]⟩
  have hwall : ∀ y ∈ openSegment ℝ (P + (P - O)) (Q + (Q - O)), ∀ i', y ∉ interior (D.tile i').carrier := by
    intro y hy
    rcases openSegment_halves _ _ hy with h' | h'
    · rw [hmZ] at h'
      exact Dissection.edge_point_not_interior D.toDissection (j := K3) (k := k3) (by rw [hk3]; exact h')
    · rw [hmZ] at h'
      refine Dissection.edge_point_not_interior D.toDissection (j := K4) (k := k4) (by rw [hk4]; rw [segment_symm]; exact h')
  -- the far-chain tile `Kc` with the edge `[P₂, Z]`
  obtain ⟨Kc, k, hKc, hKc3, -⟩ := far_edge_at_end D hS hword2 f hf0 c0 hPQ hfP2 hfQ1 g1 cg1 hg1 hg1P' hg1Q'
    h1 ch1 hh1 hh1Q' hh1P' hint hwall hdist
  rw [hmZ] at hKc
  have hdPZ : dist (P + (P - O)) (P + (Q - O)) = c := by
    rw [← hmZ, dist_left_midpoint (𝕜 := ℝ), hdist]
    have h2n : ‖(2 : ℝ)‖ = 2 := by simp
    rw [h2n]; ring
  have hKcne : K3 ≠ Kc := by
    intro he
    subst he
    have := hfle _ (subset_convexHull ℝ _ ⟨k + 2, rfl⟩)
    simp only [LinearMap.neg_apply] at hKc3
    linarith
  have hKcc : dist ((D.tile Kc).pts k) ((D.tile Kc).pts (k + 1)) = c := by
    rcases hKc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hdPZ
    · rw [e1, e2, dist_comm]; exact hdPZ
  have hKcαβ := third_vertex (tile_sixty D hS Kc) hac hbc k hKcc
  have hKcloc : (D.tile Kc).localAngle (P + (P - O)) = α := by
    have hne := angles_differ D hirr hS hVfr hVnv hKcne (Or.inr hK3β)
    have hαβ : (D.tile Kc).localAngle (P + (P - O)) = α ∨
        (D.tile Kc).localAngle (P + (P - O)) = 2 * Real.pi / 3 - α := by
      rcases hKc with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, Tri.localAngle_vertex]
        rcases hKcαβ with ⟨-, t1, -, -⟩ | ⟨-, t1, -, -⟩
        · exact Or.inl t1
        · exact Or.inr t1
      · rw [← e2, Tri.localAngle_vertex]
        rcases hKcαβ with ⟨-, -, -, t1⟩ | ⟨-, -, -, t1⟩
        · exact Or.inr t1
        · exact Or.inl t1
    rcases hαβ with h' | h'
    · exact h'
    · exact absurd (hK3β.trans h'.symm) hne
  -- the fan at `P₂` forces a `π/3` tile along the side
  obtain ⟨ε0, hε, hεin⟩ : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      (P + (P - O)) + ε • (P - O) ∈ T.carrier := by
    refine ⟨(1 - 2 * p) / p, div_pos (by linarith) hp0, fun ε hε hεle => ?_⟩
    have hεp : ε * p ≤ 1 - 2 * p := (le_div_iff₀ hp0).mp hεle
    have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
    have hOmem : O ∈ T.carrier := subset_convexHull ℝ _ ⟨v, rfl⟩
    have hwmem : T.pts w ∈ T.carrier := subset_convexHull ℝ _ ⟨w, rfl⟩
    have e : (P + (P - O)) + ε • (P - O) = O + ((2 + ε) * p) • (T.pts w - O) := by
      have h1' : (P + (P - O)) + ε • (P - O) = O + (2 + ε) • (P - O) := by module
      rw [h1', hP, smul_smul]
    rw [e]
    exact hconv.add_smul_sub_mem hOmem hwmem ⟨by positivity, by nlinarith⟩
  have hgV : g (P + (P - O)) = cg := by
    rw [hP2form, lin_comb, hgv, hgw]; ring
  have hVd : (P + (P - O)) + ((P + (Q - O)) - (P + (P - O))) = P + (Q - O) := by abel
  obtain ⟨n, hn0, hn⟩ : ∃ n : Fin 3, (D.tile Kc).pts n = P + (P - O) ∧
      (((D.tile Kc).pts (n + 1) = P + (Q - O) ∧ (D.tile Kc).pts (n + 2) = (D.tile Kc).pts (k + 2)) ∨
       ((D.tile Kc).pts (n + 1) = (D.tile Kc).pts (k + 2) ∧ (D.tile Kc).pts (n + 2) = P + (Q - O))) := by
    rcases hKc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨k, e1, Or.inl ⟨e2, rfl⟩⟩
    · have e5 : k + 1 + 1 = k + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) k
      have e6 : k + 1 + 2 = k := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) k
      exact ⟨k + 1, e2, Or.inr ⟨by rw [e5], by rw [e6]; exact e1⟩⟩
  have hmain := l3_fill D hirr hS (V := P + (P - O)) (u := P - O) (d := (P + (Q - O)) - (P + (P - O)))
    (X := (D.tile Kc).pts (k + 2)) hu hVfr hVnv g hg0 cg hgle hgV hgu hε hεin K3 m3 hK3m
    (by
      have e1 : (P + (P - O)) - (P - O) = P := by abel
      rw [e1, hVd]
      rcases hK3v with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · exact Or.inl ⟨x1, x2⟩
      · exact Or.inr ⟨x1, x2⟩)
    Kc n hn0 (by rw [hVd]; exact hn) hKcloc hK3β
  exact sideTile_of D hirr hS hac hbc hmain

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.l3_corner
