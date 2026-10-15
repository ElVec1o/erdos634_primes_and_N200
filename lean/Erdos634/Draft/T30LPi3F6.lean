import Mathlib.Tactic
import Erdos634.Draft.T30LPi3F6Geom
import Erdos634.Draft.T30LPi3F6Tile
import Erdos634.Draft.T30LPi3Corner
import Erdos634.Draft.HalfAngle

/-!
# `Pi3F6`: the far tile across a corner chord is the point reflection of the corner tile

`corner_chord_reflection` (any `CongruentDissection` whose model is a `SixtyData` tile with `α ∉ ℚπ`, sides `a, b, c` pairwise distinct,
word lemma for `c`): let `T = tile j₀` have the `c`-edge `[P,Q] = [pts k₀, pts (k₀+1)]`, lying in the half-plane `f ≤ c₀` with the chord clamped
on the target as in `ChordFar`, and `P` a non-vertex frontier point of the target.  Then there are `j ≠ j₀` and a third vertex `X` of `T` with
`T.carrier = hull{P,Q,X}` and `(tile j).carrier = hull{P,Q,P+Q−X}`, `(tile j) ⊆ {f ≥ c₀}`: the far tile is the point reflection of `T` through the
midpoint of `PQ`.  Ingredients:
 near/far chain are single `c`-edges (`ChordFar`, word lemma); the far edge is exactly `[P,Q]` (`seg_endpoints`, from `chain_edge_subset_chord`);
 the two tiles have angles `α, β` at `P` in one order only (fan count `boundary_fan_real`: at most one tile per angle `α`, `β`);
 hence the legs are swapped (`tri_two_orient`), and `reflect_of_swapped` places the third vertex.

Hypotheses not derived here: the clamps `g, h, hint` (they come from the corner tile's placement at the target corner: see
`T30LPi3Cone`) and `P` non-vertex.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.ChordFar Erdos634.Pi3Corner Erdos634.TPErdos

theorem fin3_cover : ∀ k i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide

/-- A sub-segment of `[P,Q]` of full length has the endpoints of `[P,Q]`. -/
theorem seg_endpoints {X Y P Q : Plane} (hPQ : P ≠ Q) (hX : X ∈ segment ℝ P Q) (hY : Y ∈ segment ℝ P Q)
    (hd : dist X Y = dist P Q) : (X = P ∧ Y = Q) ∨ (X = Q ∧ Y = P) := by
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

/-- **The third vertex is strictly off the line.** -/
theorem third_strict (U : Tri) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c0 : ℝ) (hle : ∀ i, f (U.pts i) ≤ c0)
    (k : Fin 3) (h1 : f (U.pts k) = c0) (h2 : f (U.pts (k + 1)) = c0) : f (U.pts (k + 2)) < c0 := by
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
  have h0 := Erdos634.HalfAngle.volume_level_line f hf c0 (hall 0)
  exact absurd (MeasureTheory.measure_mono_null hsub h0) hv.ne'

theorem range_pts_eq (U : Tri) (k : Fin 3) :
    Set.range U.pts = {U.pts k, U.pts (k + 1), U.pts (k + 2)} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    have : i = k ∨ i = k + 1 ∨ i = k + 2 := fin3_cover k i
    rcases this with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- **Third vertex, tile form.** -/
theorem third_vertex {U : Tri} {α a b c : ℝ} (hU : U.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (k : Fin 3) (hk : dist (U.pts k) (U.pts (k + 1)) = c) :
    (dist (U.pts (k + 1)) (U.pts (k + 2)) = a ∧ U.angleAt k = α ∧ dist (U.pts k) (U.pts (k + 2)) = b ∧
        U.angleAt (k + 1) = 2 * Real.pi / 3 - α) ∨
    (dist (U.pts (k + 1)) (U.pts (k + 2)) = b ∧ U.angleAt k = 2 * Real.pi / 3 - α ∧
        dist (U.pts k) (U.pts (k + 2)) = a ∧ U.angleAt (k + 1) = α) := by
  have e3 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have e4 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
  have e5 : ∀ k : Fin 3, k + 2 + 1 + 1 = k + 1 := by decide
  have e6 : ∀ k : Fin 3, k + 2 + 1 + 2 = k + 2 := by decide
  have e7 : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  have e8 : ∀ k : Fin 3, k + 1 + 2 = k := by decide
  have hl : U.oppLen (k + 2) = c := by
    unfold Tri.oppLen; rw [e3, e4]; exact hk
  have := tri_two_orient hU hac hbc (k + 2) hl
  simp only [Tri.oppLen, e3, e4, e7, e8, Tri.angleAt] at this ⊢
  rcases this with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    refine ⟨h1, h2, ?_, h4⟩
    rw [dist_comm]; exact h3
  · right
    refine ⟨h1, h2, ?_, h4⟩
    rw [dist_comm]; exact h3

/-- Fan count: at a non-vertex frontier point at most one tile presents `α` and at most one presents `β`. -/
theorem cnt_le_one {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) :
    cnt D.toDissection v α ≤ 1 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) ≤ 1 := by
  have hb : (cnt D.toDissection v α = 0 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 0 ∧
        cnt D.toDissection v (Real.pi / 3) = 0 ∧ cnt D.toDissection v Real.pi = 1)
      ∨ (cnt D.toDissection v α = 0 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 0 ∧
        cnt D.toDissection v (Real.pi / 3) = 3 ∧ cnt D.toDissection v Real.pi = 0)
      ∨ (cnt D.toDissection v α = 1 ∧ cnt D.toDissection v (2 * Real.pi / 3 - α) = 1 ∧
        cnt D.toDissection v (Real.pi / 3) = 1 ∧ cnt D.toDissection v Real.pi = 0) :=
    boundary_fan_real D hirr hS hv hnv
  rcases hb with h | h | h <;> omega

/-- Two distinct tiles cannot both present `α` (resp. `β`) at such a point. -/
theorem angles_differ {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle v = α ∨ (D.tile i).localAngle v = 2 * Real.pi / 3 - α) :
    (D.tile i).localAngle v ≠ (D.tile j).localAngle v := by
  intro heq
  obtain ⟨h1, h2⟩ := cnt_le_one D hirr hS hv hnv
  have key : ∀ θ : ℝ, (D.tile i).localAngle v = θ → (D.tile j).localAngle v = θ → 2 ≤ cnt D.toDissection v θ := by
    intro θ hθi hθj
    unfold cnt
    have : 1 < ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card :=
      Finset.one_lt_card.mpr ⟨i, by simp [hθi], j, by simp [hθj], hij⟩
    omega
  rcases hi with hi | hi
  · have := key α hi (heq ▸ hi); omega
  · have := key _ hi (heq ▸ hi); omega

open Erdos634.EdgeWordConversion in
theorem sideLen_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.SixtyData α a b c)
    (i : Fin 3) : sideLen D i = a ∨ sideLen D i = b ∨ sideLen D i = c := by
  obtain ⟨σ, -, h0', -, h1', -, h2'⟩ := hS
  have e3 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have e4 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
  have : sideLen D i = D.model.oppLen (i + 2) := by
    unfold sideLen Tri.oppLen; rw [e3, e4]
  rw [this]
  obtain ⟨m, hm⟩ := σ.surjective (i + 2)
  rw [← hm]
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 m with rfl | rfl | rfl
  · exact Or.inl h0'
  · exact Or.inr (Or.inl h1')
  · exact Or.inr (Or.inr h2')

open Erdos634.EdgeWordConversion in
/-- **F6: the far tile across the corner chord is the point reflection of the corner tile.** -/
theorem corner_chord_reflection {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (j0 : Fin N) (k0 : Fin 3) {P Q : Plane} (hP : (D.tile j0).pts k0 = P) (hQ : (D.tile j0).pts (k0 + 1) = Q)
    (hlen : dist P Q = c)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c0 : ℝ) (hfle : ∀ i, f ((D.tile j0).pts i) ≤ c0)
    (hfP : f P = c0) (hfQ : f Q = c0)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hPfr : P ∈ frontier D.target.carrier) (hPnv : P ∉ Set.range D.target.pts) :
    ∃ j : Fin N, j ≠ j0 ∧ ∃ X : Plane, f X < c0 ∧
      (D.tile j0).carrier = convexHull ℝ {P, Q, X} ∧
      (D.tile j).carrier = convexHull ℝ {P, Q, P + Q - X} ∧
      ∀ y ∈ (D.tile j).carrier, c0 ≤ f y := by
  have hPQ : P ≠ Q := by
    rw [← hP, ← hQ]
    intro hh'
    have := (D.tile j0).indep.injective hh'
    exact absurd this ((by decide : ∀ k : Fin 3, k ≠ k + 1) k0)
  have hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier := by
    rw [← hP, ← hQ]; exact hwall_of_tile_edge D.toDissection j0 k0
  -- the far chain is a single `c`-edge
  obtain ⟨e2, he2, hch2, hlen2⟩ := far_chain_single_gen D (sideLen_mem D hS)
    hword f hf c0 hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall hlen
  obtain ⟨j, k2⟩ := e2
  obtain ⟨hf2P, hf2Q, hle2⟩ := Dissection.mem_lineChain.mp he2
  have hsub := chain_edge_subset_chord D.toDissection (-f) (neg_ne_zero.mpr hf) (-c0) hPQ (by simp [hfP])
    (by simp [hfQ]) g cg hg hgP hgQ h ch hh hhQ hhP he2
  have hend := seg_endpoints hPQ (hsub (left_mem_segment ℝ _ _ : (D.tile j).pts k2 ∈ (D.tile j).edge k2))
    (hsub (right_mem_segment ℝ _ _ : (D.tile j).pts (k2 + 1) ∈ (D.tile j).edge k2))
    (by simpa [hlen] using hlen2)
  -- strictness and distinctness
  have hX : f ((D.tile j0).pts (k0 + 2)) < c0 :=
    third_strict (D.tile j0) f hf c0 hfle k0 (by rw [hP]; exact hfP) (by rw [hQ]; exact hfQ)
  have hX' : (-f) ((D.tile j).pts (k2 + 2)) < -c0 :=
    third_strict (D.tile j) (-f) (neg_ne_zero.mpr hf) (-c0) hle2 k2 hf2P hf2Q
  have hjne : j ≠ j0 := by
    rintro rfl
    have := hle2 (k0 + 2)
    simp only [LinearMap.neg_apply] at this
    linarith
  -- angles at `P`
  have hTc : dist ((D.tile j0).pts k0) ((D.tile j0).pts (k0 + 1)) = c := by rw [hP, hQ]; exact hlen
  have hTd := third_vertex (tile_sixty D hS j0) hac hbc k0 hTc
  have hT2c : dist ((D.tile j).pts k2) ((D.tile j).pts (k2 + 1)) = c := hlen2
  have hT2d := third_vertex (tile_sixty D hS j) hac hbc k2 hT2c
  have hlocT : (D.tile j0).localAngle P = (D.tile j0).angleAt k0 := by
    rw [← hP]; exact Tri.localAngle_vertex _ _
  have hαT : (D.tile j0).localAngle P = α ∨ (D.tile j0).localAngle P = 2 * Real.pi / 3 - α := by
    rw [hlocT]
    rcases hTd with ⟨-, h2, -, -⟩ | ⟨-, h2, -, -⟩
    · exact Or.inl h2
    · exact Or.inr h2
  have hdiff := angles_differ D hirr hS hPfr hPnv hjne.symm hαT
  -- legs swapped
  have hswap : dist P ((D.tile j).pts (k2 + 2)) = dist Q ((D.tile j0).pts (k0 + 2)) ∧
      dist Q ((D.tile j).pts (k2 + 2)) = dist P ((D.tile j0).pts (k0 + 2)) := by
    rw [hP, hQ] at hTd
    rcases hend with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hloc : (D.tile j).localAngle P = (D.tile j).angleAt k2 := by
        rw [← e1]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hloc] at hdiff
      rw [e1, e2] at hT2d
      rcases hTd with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩ <;>
        rcases hT2d with ⟨u1, u2, u3, u4⟩ | ⟨u1, u2, u3, u4⟩ <;>
        first
        | exact absurd (t2.trans u2.symm) hdiff
        | exact ⟨by rw [← e1] at *; linarith, by linarith⟩
    · have hloc : (D.tile j).localAngle P = (D.tile j).angleAt (k2 + 1) := by
        rw [← e2]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hloc] at hdiff
      rw [e1, e2] at hT2d
      rcases hTd with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩ <;>
        rcases hT2d with ⟨u1, u2, u3, u4⟩ | ⟨u1, u2, u3, u4⟩ <;>
        first
        | exact absurd (t2.trans u4.symm) hdiff
        | exact ⟨by linarith, by linarith⟩
  have hX'' : c0 < f ((D.tile j).pts (k2 + 2)) := by
    simp only [LinearMap.neg_apply] at hX'; linarith
  have hrefl := reflect_of_swapped f c0 hPQ hfP hfQ (by rw [← hP, ← hQ] at *; exact hX) hX'' hswap.1 hswap.2
  refine ⟨j, hjne, (D.tile j0).pts (k0 + 2), hX, ?_, ?_, ?_⟩
  · unfold Tri.carrier; rw [range_pts_eq _ k0, hP, hQ]
  · unfold Tri.carrier; rw [range_pts_eq _ k2, hrefl]
    rcases hend with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, Set.insert_comm]
  · intro y hy
    have := Tri.carrier_subset_halfplane (D.tile j) (-f) (-c0) hle2 y hy
    simp only [LinearMap.neg_apply] at this; linarith

end Erdos634.Pi3F6
