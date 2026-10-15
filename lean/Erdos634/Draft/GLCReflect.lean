import Mathlib.Tactic
import Erdos634.Draft.T30LPi3F6
import Erdos634.Draft.GLCFan
import Erdos634.Draft.GLCArith

/-!
# G1: the far tile across the corner chord (an `a`-edge) is the point reflection of the corner tile

Port of `Pi3F6.corner_chord_reflection` (the `π/3` tile, chord a `c`-edge) to the `γ = 2α` tile, chord = the `a`-edge `[P,Q]`
(`a` opposite `α`; its ends carry `(β,γ)`).  `corner_chord_reflection_2a`: on a `CongruentDissection` whose model has `TwoAlphaData α a b c`,
`α ∉ ℚπ`, with the word lemma for `a` (`x a + y b + z c = a ⇒ x+y+z = 1`; for the tile `(k²,2k+1,k(k+1))`, `k ≥ 2` this is
`GLCArith.hword_a_real`), let `T = tile j₀` have the `a`-edge `[P,Q]`, in the half-plane `f ≤ c₀`, chord clamped on the target as in `ChordFar`,
`P` a non-vertex frontier point.  Then there are `j ≠ j₀` and a third vertex `X` of `T` with `T = hull{P,Q,X}`, `tile j = hull{P,Q,P+Q−X}`,
`tile j ⊆ {f ≥ c₀}`: the tile across the chord is the point reflection of `T` through the midpoint of `PQ`.
Ingredients: far chain is a single `a`-edge (`far_chain_single_gen` + word lemma); the far edge is exactly `[P,Q]` (`seg_endpoints`);
the two tiles cannot present the same angle (`β` or `γ`) at `P` (`GLCFan.angles_differ_2alpha`), so the legs are swapped, and
`reflect_of_swapped` places the third vertex.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.ChordFar Erdos634.Pi3Corner Erdos634.TPErdos Erdos634.Pi3F6
open Erdos634.EdgeWordConversion

variable {N : ℕ}

theorem tile_twoalpha (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.TwoAlphaData α a b c)
    (i : Fin N) : (D.tile i).TwoAlphaData α a b c := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨τ, h0, h0', h1, h1', h2, h2'⟩ := hS
  refine ⟨τ.trans σ.symm, ?_⟩
  have key : ∀ m : Fin 3, (D.tile i).angleAt ((τ.trans σ.symm) m) = D.model.angleAt (τ m) ∧
      (D.tile i).oppLen ((τ.trans σ.symm) m) = D.model.oppLen (τ m) := by
    intro m
    have := hσ ((τ.trans σ.symm) m)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(key 0).1, h0]
  · rw [(key 0).2, h0']
  · rw [(key 1).1, h1]
  · rw [(key 1).2, h1']
  · rw [(key 2).1, h2]
  · rw [(key 2).2, h2']

theorem sideLen_mem_2a (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.TwoAlphaData α a b c)
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

theorem tri_orient_a {U : Tri} {α a b c : ℝ} (hU : U.TwoAlphaData α a b c) (hab : a ≠ b) (hac : a ≠ c)
    (l : Fin 3) (hl : U.oppLen l = a) :
    (U.oppLen (l + 1) = b ∧ U.angleAt (l + 1) = Real.pi - 3 * α ∧ U.oppLen (l + 2) = c ∧
        U.angleAt (l + 2) = 2 * α) ∨
    (U.oppLen (l + 1) = c ∧ U.angleAt (l + 1) = 2 * α ∧ U.oppLen (l + 2) = b ∧
        U.angleAt (l + 2) = Real.pi - 3 * α) := by
  obtain ⟨σ, h0, h0', h1, h1', h2, h2'⟩ := hU
  obtain ⟨m, hm⟩ := σ.surjective l
  obtain ⟨m1, hm1⟩ := σ.surjective (l + 1)
  obtain ⟨m2, hm2⟩ := σ.surjective (l + 2)
  have e1 : ∀ x : Fin 3, x ≠ x + 1 := by decide
  have e2 : ∀ x : Fin 3, x ≠ x + 2 := by decide
  have e12 : ∀ x : Fin 3, x + 1 ≠ x + 2 := by decide
  have n01 : m ≠ m1 := fun h => e1 l (by have := congrArg σ h; rwa [hm, hm1] at this)
  have n02 : m ≠ m2 := fun h => e2 l (by have := congrArg σ h; rwa [hm, hm2] at this)
  have n12 : m1 ≠ m2 := fun h => e12 l (by have := congrArg σ h; rwa [hm1, hm2] at this)
  rw [← hm1, ← hm2]
  rw [← hm] at hl
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 m with rfl | rfl | rfl <;> rcases h3 m1 with rfl | rfl | rfl <;>
    rcases h3 m2 with rfl | rfl | rfl <;> simp only [ne_eq, not_true_eq_false] at n01 n02 n12 <;>
    first
    | exact absurd hl (by rw [h1']; exact hab.symm)
    | exact absurd hl (by rw [h2']; exact hac.symm)
    | exact Or.inl ⟨h1', h1, h2', h2⟩
    | exact Or.inr ⟨h2', h2, h1', h1⟩

/-- **Third vertex over an `a`-edge.**  The `a`-edge `[P,Q] = [U.pts k, U.pts (k+1)]` has ends `(β,γ)` in one of the two orders;
with `X = U.pts (k+2)`: `β` at `P` gives `|QX| = b, |PX| = c`; `γ` at `P` gives `|QX| = c, |PX| = b`. -/
theorem third_vertex_a {U : Tri} {α a b c : ℝ} (hU : U.TwoAlphaData α a b c) (hab : a ≠ b) (hac : a ≠ c)
    (k : Fin 3) (hk : dist (U.pts k) (U.pts (k + 1)) = a) :
    (U.angleAt k = Real.pi - 3 * α ∧ U.angleAt (k + 1) = 2 * α ∧
        dist (U.pts (k + 1)) (U.pts (k + 2)) = b ∧ dist (U.pts k) (U.pts (k + 2)) = c) ∨
    (U.angleAt k = 2 * α ∧ U.angleAt (k + 1) = Real.pi - 3 * α ∧
        dist (U.pts (k + 1)) (U.pts (k + 2)) = c ∧ dist (U.pts k) (U.pts (k + 2)) = b) := by
  have e3 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have e4 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
  have e7 : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  have e8 : ∀ k : Fin 3, k + 1 + 2 = k := by decide
  have hl : U.oppLen (k + 2) = a := by
    unfold Tri.oppLen; rw [e3, e4]; exact hk
  have := tri_orient_a hU hab hac (k + 2) hl
  simp only [Tri.oppLen, e3, e4, e7, e8, Tri.angleAt] at this ⊢
  rcases this with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    refine ⟨h2, h4, ?_, ?_⟩
    · exact h1
    · rw [dist_comm]; exact h3
  · right
    refine ⟨h2, h4, ?_, ?_⟩
    · exact h1
    · rw [dist_comm]; exact h3

/-- **G1, geometric core: the far tile across the corner chord is the point reflection of the corner tile.** -/
theorem corner_chord_reflection_2a (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (j0 : Fin N) (k0 : Fin 3) {P Q : Plane} (hP : (D.tile j0).pts k0 = P) (hQ : (D.tile j0).pts (k0 + 1) = Q)
    (hlen : dist P Q = a)
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
      (∀ y ∈ (D.tile j).carrier, c0 ≤ f y) ∧
      X = (D.tile j0).pts (k0 + 2) ∧
      (∃ k2 : Fin 3, (((D.tile j).pts k2 = P ∧ (D.tile j).pts (k2 + 1) = Q) ∨
          ((D.tile j).pts k2 = Q ∧ (D.tile j).pts (k2 + 1) = P)) ∧ (D.tile j).pts (k2 + 2) = P + Q - X) ∧
      (((D.tile j0).localAngle P = Real.pi - 3 * α ∧ (D.tile j).localAngle P = 2 * α ∧
          (D.tile j0).localAngle Q = 2 * α ∧ (D.tile j).localAngle Q = Real.pi - 3 * α) ∨
        ((D.tile j0).localAngle P = 2 * α ∧ (D.tile j).localAngle P = Real.pi - 3 * α ∧
          (D.tile j0).localAngle Q = Real.pi - 3 * α ∧ (D.tile j).localAngle Q = 2 * α)) := by
  have hPQ : P ≠ Q := by
    rw [← hP, ← hQ]
    intro hh'
    have := (D.tile j0).indep.injective hh'
    exact absurd this ((by decide : ∀ k : Fin 3, k ≠ k + 1) k0)
  have hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier := by
    rw [← hP, ← hQ]; exact hwall_of_tile_edge D.toDissection j0 k0
  obtain ⟨e2, he2, hch2, hlen2⟩ := far_chain_single_gen D (sideLen_mem_2a D hS)
    hword f hf c0 hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall hlen
  obtain ⟨j, k2⟩ := e2
  obtain ⟨hf2P, hf2Q, hle2⟩ := Dissection.mem_lineChain.mp he2
  have hsub := chain_edge_subset_chord D.toDissection (-f) (neg_ne_zero.mpr hf) (-c0) hPQ (by simp [hfP])
    (by simp [hfQ]) g cg hg hgP hgQ h ch hh hhQ hhP he2
  have hend := seg_endpoints hPQ (hsub (left_mem_segment ℝ _ _ : (D.tile j).pts k2 ∈ (D.tile j).edge k2))
    (hsub (right_mem_segment ℝ _ _ : (D.tile j).pts (k2 + 1) ∈ (D.tile j).edge k2))
    (by simpa [hlen] using hlen2)
  have hX : f ((D.tile j0).pts (k0 + 2)) < c0 :=
    third_strict (D.tile j0) f hf c0 hfle k0 (by rw [hP]; exact hfP) (by rw [hQ]; exact hfQ)
  have hX' : (-f) ((D.tile j).pts (k2 + 2)) < -c0 :=
    third_strict (D.tile j) (-f) (neg_ne_zero.mpr hf) (-c0) hle2 k2 hf2P hf2Q
  have hjne : j ≠ j0 := by
    rintro rfl
    have := hle2 (k0 + 2)
    simp only [LinearMap.neg_apply] at this
    linarith
  have hTc : dist ((D.tile j0).pts k0) ((D.tile j0).pts (k0 + 1)) = a := by rw [hP, hQ]; exact hlen
  have hTd := third_vertex_a (tile_twoalpha D hS j0) hab hac k0 hTc
  have hT2d := third_vertex_a (tile_twoalpha D hS j) hab hac k2 hlen2
  have hlocT : (D.tile j0).localAngle P = (D.tile j0).angleAt k0 := by
    rw [← hP]; exact Tri.localAngle_vertex _ _
  have hαT : (D.tile j0).localAngle P = Real.pi - 3 * α ∨ (D.tile j0).localAngle P = 2 * α := by
    rw [hlocT]
    rcases hTd with ⟨h2, -, -, -⟩ | ⟨h2, -, -, -⟩
    · exact Or.inl h2
    · exact Or.inr h2
  have hdiff := angles_differ_2alpha D hα hS hPfr hPnv hjne.symm hαT
  have hlocTQ : (D.tile j0).localAngle Q = (D.tile j0).angleAt (k0 + 1) := by
    rw [← hQ]; exact Tri.localAngle_vertex _ _
  have hsw : (dist P ((D.tile j).pts (k2 + 2)) = dist Q ((D.tile j0).pts (k0 + 2)) ∧
      dist Q ((D.tile j).pts (k2 + 2)) = dist P ((D.tile j0).pts (k0 + 2))) ∧
      (((D.tile j0).localAngle P = Real.pi - 3 * α ∧ (D.tile j).localAngle P = 2 * α ∧
          (D.tile j0).localAngle Q = 2 * α ∧ (D.tile j).localAngle Q = Real.pi - 3 * α) ∨
        ((D.tile j0).localAngle P = 2 * α ∧ (D.tile j).localAngle P = Real.pi - 3 * α ∧
          (D.tile j0).localAngle Q = Real.pi - 3 * α ∧ (D.tile j).localAngle Q = 2 * α)) := by
    rw [hP, hQ] at hTd
    rcases hend with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hloc : (D.tile j).localAngle P = (D.tile j).angleAt k2 := by
        rw [← e1]; exact Tri.localAngle_vertex _ _
      have hlocQ : (D.tile j).localAngle Q = (D.tile j).angleAt (k2 + 1) := by
        rw [← e2]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hloc] at hdiff
      rw [e1, e2] at hT2d
      rcases hTd with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩ <;>
        rcases hT2d with ⟨u1, u2, u3, u4⟩ | ⟨u1, u2, u3, u4⟩ <;>
        first
        | exact absurd (t1.trans u1.symm) hdiff
        | exact ⟨⟨by linarith, by linarith⟩, Or.inl ⟨hlocT.trans t1, hloc.trans u1, hlocTQ.trans t2, hlocQ.trans u2⟩⟩
        | exact ⟨⟨by linarith, by linarith⟩, Or.inr ⟨hlocT.trans t1, hloc.trans u1, hlocTQ.trans t2, hlocQ.trans u2⟩⟩
    · have hloc : (D.tile j).localAngle P = (D.tile j).angleAt (k2 + 1) := by
        rw [← e2]; exact Tri.localAngle_vertex _ _
      have hlocQ : (D.tile j).localAngle Q = (D.tile j).angleAt k2 := by
        rw [← e1]; exact Tri.localAngle_vertex _ _
      rw [hlocT, hloc] at hdiff
      rw [e1, e2] at hT2d
      rcases hTd with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩ <;>
        rcases hT2d with ⟨u1, u2, u3, u4⟩ | ⟨u1, u2, u3, u4⟩ <;>
        first
        | exact absurd (t1.trans u2.symm) hdiff
        | exact ⟨⟨by linarith, by linarith⟩, Or.inl ⟨hlocT.trans t1, hloc.trans u2, hlocTQ.trans t2, hlocQ.trans u1⟩⟩
        | exact ⟨⟨by linarith, by linarith⟩, Or.inr ⟨hlocT.trans t1, hloc.trans u2, hlocTQ.trans t2, hlocQ.trans u1⟩⟩
  obtain ⟨hswap, hangs⟩ := hsw
  have hX'' : c0 < f ((D.tile j).pts (k2 + 2)) := by
    simp only [LinearMap.neg_apply] at hX'; linarith
  have hrefl := reflect_of_swapped f c0 hPQ hfP hfQ (by rw [← hP, ← hQ] at *; exact hX) hX'' hswap.1 hswap.2
  refine ⟨j, hjne, (D.tile j0).pts (k0 + 2), hX, ?_, ?_, ?_, rfl, ⟨k2, ?_, hrefl⟩, hangs⟩
  · unfold Tri.carrier; rw [range_pts_eq _ k0, hP, hQ]
  · unfold Tri.carrier; rw [range_pts_eq _ k2, hrefl]
    rcases hend with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, Set.insert_comm]
  · intro y hy
    have := Tri.carrier_subset_halfplane (D.tile j) (-f) (-c0) hle2 y hy
    simp only [LinearMap.neg_apply] at this; linarith
  · exact hend

end Erdos634.GLC

#print axioms Erdos634.GLC.corner_chord_reflection_2a
