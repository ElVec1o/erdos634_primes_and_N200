import Mathlib.Tactic
import Erdos634.Draft.GLCReflect
import Erdos634.Draft.T30LPi3Cone
import Erdos634.Draft.T30LPi3Clamp
import Erdos634.Draft.T30LPi3F6Corner

/-!
# G1 at an `α`-corner of the target, `γ = 2α` tile

* `corner_has_alpha_tile`: at a target corner of angle `α` exactly one tile presents `α` and none presents `β`, `γ`, `π`, `2π`
  (`Row4.count_eq` + `Row4.fig_arith`).
* `corner_tile_on_sides_gen`: (generic corner angle `θ ∈ (0,π)`) a tile presenting `θ` at the corner has its two edges there on the two target
  sides (`SameRay`, in one order or the other) — port of `Pi3Cone.corner_tile_on_sides` without `SixtyData`.
* `opp_a_of_alpha`: a vertex with angle `α` of a `TwoAlphaData` tile is opposite the `a`-edge.
* `corner_far_reflection_2a` (**G1, the corner chord**): at a target corner of angle `α` whose two adjacent sides have lengths not in `{b, c}`,
  the corner tile `T` has its two edges at the corner on the two sides (`b` and `c`, in one order), ending at `P, Q` on the sides; `PQ` is the
  `a`-edge; the chord is clamped by the two sides; and the tile across `PQ` is the point reflection of `T` through the midpoint of `PQ`.
  With the word lemma for `a` (`GLCArith.hword_a_real`) no clamp or placement hypothesis remains.
* WITNESS `witness_corner_G1`: the real certified 1125-tiling (`G3GControl.D`, tile `(4,5,6)·16`, `k = 2`) at its target corner `0` (angle `α`),
  all hypotheses discharged.  `ctl_sides`: a side of length `c` through the corner is excluded by hypothesis (the edge
  would reach the target vertex).
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Cone Erdos634.Pi3F6 Erdos634.Pi3Tile Erdos634.ChordFar

variable {N : ℕ}

theorem corner_has_alpha_tile (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {k : Fin 3} (hk : D.target.angleAt k = α) :
    cntA D (D.target.pts k) α = 1 ∧ cntA D (D.target.pts k) (Real.pi - 3 * α) = 0 ∧
    cntA D (D.target.pts k) (2 * α) = 0 ∧ cntA D (D.target.pts k) Real.pi = 0 ∧
    cntA D (D.target.pts k) (2 * Real.pi) = 0 := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hc := Row4.count_eq D hα h hα0 hα3 (D.target.pts k)
  rw [D.target.localAngle_vertex k] at hc
  change D.target.angleAt k = _ at hc
  rw [hk] at hc
  unfold cntA
  set P₁ := ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
  set Q₁ := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi - 3 * α} : Finset (Fin N)).card
  set R₁ := ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α} : Finset (Fin N)).card
  set S₁ := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card
  set T₁ := ({i | (D.tile i).localAngle (D.target.pts k) = 2 * Real.pi} : Finset (Fin N)).card
  obtain ⟨h1, h2⟩ := Row4.fig_arith hα (P := P₁) (Q := Q₁) (R := R₁) (S := S₁) (T := T₁)
    (j := 0) (k := 1) (by push_cast; linear_combination -hc)
  omega

theorem exists_pos_orientation' {u1 u2 : Plane} (hu1 : u1 ≠ 0) (hu2 : u2 ≠ 0) {θ : ℝ}
    (h0 : 0 < θ) (h1 : θ < Real.pi) (h : InnerProductGeometry.angle u1 u2 = θ) :
    ∃ o : Orientation ℝ Plane (Fin 2), (o.oangle u1 u2).sign = 1 := by
  let o0 : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hne : (o0.oangle u1 u2).sign ≠ 0 := by
    intro hz
    rcases o0.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hz with e | e | e | e
    · exact hu1 e
    · exact hu2 e
    · rw [h] at e; linarith
    · rw [h] at e; linarith
  have hcases : ∀ s : SignType, s ≠ 0 → s = -1 ∨ s = 1 := by decide
  rcases hcases _ hne with hm | hp
  · refine ⟨-o0, ?_⟩
    rw [Orientation.oangle_neg_orientation_eq_neg, Real.Angle.sign_neg, hm]; decide
  · exact ⟨o0, hp⟩

/-- **The corner tile's edges are on the target sides** (generic corner angle `θ ∈ (0,π)`; port of `Pi3Cone.corner_tile_on_sides`). -/
theorem corner_tile_on_sides_gen (D : CongruentDissection N) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (k : Fin 3) (hk : D.target.angleAt k = θ) (i : Fin N)
    (hi : (D.tile i).localAngle (D.target.pts k) = θ) :
    ∃ j : Fin 3, (D.tile i).pts j = D.target.pts k ∧ (D.tile i).angleAt j = θ ∧
      ((SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k)) ∨
       (SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k))) := by
  classical
  have hpi := Real.pi_pos
  set O := D.target.pts k with hO
  obtain ⟨j, hj, hjang⟩ : ∃ j : Fin 3, O = (D.tile i).pts j ∧
      (D.tile i).localAngle O = cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) := by
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) O with h | h | h | h
    · exact h
    · rw [hi] at h; linarith
    · rw [hi] at h; linarith
    · rw [hi] at h; linarith
  refine ⟨j, hj.symm, by rw [← hi, hjang]; rfl, ?_⟩
  set A := D.target.pts (k + 1)
  set B := D.target.pts (k + 2)
  set P := (D.tile i).pts (j + 1)
  set Q := (D.tile i).pts (j + 2)
  have hcorner : cornerAngle P O Q = θ := by rw [← hi, hjang, ← hj]
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1 : (D.tile i).pts j ≠ (D.tile i).pts (j + 1) := hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)
  have hj2 : (D.tile i).pts j ≠ (D.tile i).pts (j + 2) := hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)
  have hP : P - O ≠ 0 := by rw [sub_ne_zero, hj]; exact hj1.symm
  have hQ : Q - O ≠ 0 := by rw [sub_ne_zero, hj]; exact hj2.symm
  have hAO : A ≠ O := fun h => by
    have := D.target.indep.injective h
    exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k this
  have hBO : B ≠ O := fun h => by
    have := D.target.indep.injective h
    exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k this
  have hu1 : A - O ≠ 0 := sub_ne_zero.mpr hAO
  have hu2 : B - O ≠ 0 := sub_ne_zero.mpr hBO
  have hang : InnerProductGeometry.angle (A - O) (B - O) = θ := by
    rw [← hk]; unfold Tri.angleAt cornerAngle EuclideanGeometry.angle; simp only [vsub_eq_sub]; rfl
  obtain ⟨o, ho⟩ := exists_pos_orientation' hu1 hu2 hθ0 hθπ hang
  have hθ : (o.oangle (A - O) (B - O)).toReal = θ := by
    rw [o.oangle_eq_angle_of_sign_eq_one ho, hang, Real.Angle.toReal_coe_eq_self_iff]
    constructor <;> linarith
  have hconeP : ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ P - O = s • (A - O) + t • (B - O) :=
    hull_cone D.target k P (Erdos634.BaseSelection.tile_subset_target D.toDissection i
      (subset_convexHull ℝ _ ⟨j + 1, rfl⟩))
  have hconeQ : ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ Q - O = s • (A - O) + t • (B - O) :=
    hull_cone D.target k Q (Erdos634.BaseSelection.tile_subset_target D.toDissection i
      (subset_convexHull ℝ _ ⟨j + 2, rfl⟩))
  obtain ⟨sP, tP, hsP, htP, ePQ⟩ := hconeP
  obtain ⟨sQ, tQ, hsQ, htQ, eQ⟩ := hconeQ
  have dP := cone_oangle o ho hsP htP (by rw [← ePQ]; exact hP)
  have dQ := cone_oangle o ho hsQ htQ (by rw [← eQ]; exact hQ)
  rw [← ePQ, hθ] at dP
  rw [← eQ, hθ] at dQ
  have key := Erdos634.WedgeExtremal.Dissection.corner_on_wedge_sides o (A := O) (P := P) (Q := Q) (u := A - O)
    hu1 hP hQ hθπ rfl rfl ⟨dP.1, dP.2⟩ ⟨dQ.1, dQ.2⟩ hcorner
  have h0 : ∀ y : Plane, y ≠ 0 → (o.oangle (A - O) y).toReal = 0 → SameRay ℝ (A - O) y := fun y _ h =>
    sameRay_of_angle_zero o (Real.Angle.toReal_eq_zero_iff.mp h)
  have h3 : ∀ y : Plane, y ≠ 0 → (o.oangle (A - O) y).toReal = θ → SameRay ℝ (B - O) y := by
    intro y hy h
    have e1 : o.oangle (A - O) y = o.oangle (A - O) (B - O) := by
      rw [← Real.Angle.coe_toReal (o.oangle (A - O) y), ← Real.Angle.coe_toReal (o.oangle (A - O) (B - O)), h, hθ]
    have := o.oangle_add hu1 hu2 hy
    have e2 : o.oangle (B - O) y = 0 := by
      have h' : o.oangle (A - O) (B - O) + o.oangle (B - O) y = o.oangle (A - O) (B - O) := by
        rw [this, e1]
      simpa using h'
    exact sameRay_of_angle_zero o e2
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h0 _ hP h1, h3 _ hQ h2⟩
  · right; exact ⟨h3 _ hP h1, h0 _ hQ h2⟩

theorem opp_a_of_alpha {U : Tri} {α a b c : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hU : U.TwoAlphaData α a b c) (j : Fin 3) (hj : U.angleAt j = α) : U.oppLen j = a := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hU
  obtain ⟨m, hm⟩ := σ.surjective j
  rw [← hm] at hj ⊢
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 m with rfl | rfl | rfl
  · exact o0
  · rw [h1] at hj; exact absurd ⟨1 / 4, by push_cast; linarith⟩ hirr
  · rw [h2] at hj; exact absurd ⟨0, by push_cast; linarith⟩ hirr

theorem aux_reflection_2a (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v)
    (hlen : dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hPA : (D.tile i).pts (j + 1) ≠ D.target.pts w) (hQB : (D.tile i).pts (j + 2) ≠ D.target.pts z) :
    ∃ j' : Fin N, j' ≠ i ∧ ∃ X : Plane,
      (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
      (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
        (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} := by
  set T := D.target with hT
  set P := (D.tile i).pts (j + 1) with hPdef
  set Q := (D.tile i).pts (j + 2) with hQdef
  have hPform : P = (1 - p) • T.pts v + p • T.pts w := by
    have : P = T.pts v + p • (T.pts w - T.pts v) := by rw [← hP]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hQform : Q = (1 - r) • T.pts v + r • T.pts z := by
    have : Q = T.pts v + r • (T.pts z - T.pts v) := by rw [← hQ]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  have hPmem : P ∈ T.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection i
    (subset_convexHull ℝ _ ⟨j + 1, rfl⟩)
  have hQmem : Q ∈ T.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection i
    (subset_convexHull ℝ _ ⟨j + 2, rfl⟩)
  have hp1 : p < 1 := by
    have hmem' := hPmem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v P := hmem' v
    rw [hPform, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvw] at hnn
    rcases lt_or_eq_of_le (by linarith : p ≤ 1) with h | h
    · exact h
    · exfalso; apply hPA; rw [hPform, h]; simp
  have hr1 : r < 1 := by
    have hmem' := hQmem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v Q := hmem' v
    rw [hQform, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvz] at hnn
    rcases lt_or_eq_of_le (by linarith : r ≤ 1) with h | h
    · exact h
    · exfalso; apply hQB; rw [hQform, h]; simp
  obtain ⟨⟨g, cg, hg, hgP, hgQ, hg0⟩, ⟨h, ch, hh, hhQ, hhP, hh0⟩, hint, hfr, hnv, -, -⟩ :=
    clamps T v w z hvw hvz hwz hp0 hp1 hr0 hr1
  obtain ⟨f, c0, hf, hfle, hf1, hf2, hf3⟩ := exists_supporting (D.tile i) (j + 1)
  have hfle' : ∀ m, f ((D.tile i).pts m) ≤ c0 := fun m => hfle _ (subset_convexHull ℝ _ ⟨m, rfl⟩)
  have e11 : j + 1 + 1 = j + 2 := (by decide : ∀ j : Fin 3, j + 1 + 1 = j + 2) j
  rw [e11] at hf2
  obtain ⟨j', hj', X, -, hcar1, hcar2, -⟩ := corner_chord_reflection_2a D hα hS hab hac hword i (j + 1)
    (P := P) (Q := Q) rfl (by rw [e11]) hlen f hf c0 hfle' hf1 hf2 g cg hg (by rw [hPform]; exact hgP)
    (by rw [hQform]; exact hgQ)
    h ch hh (by rw [hQform]; exact hhQ) (by rw [hPform]; exact hhP)
    (by rw [hPform, hQform]; exact hint) (by rw [hPform]; exact hfr) (by rw [hPform]; exact hnv)
  exact ⟨j', hj', X, hcar1, hcar2⟩

/-- **G1 at an `α`-corner: the corner tile and its point reflection share the corner chord (the `a`-edge).** -/
theorem corner_far_reflection_2a (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (k : Fin 3) (hk : D.target.angleAt k = α)
    (hA1 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ b)
    (hA2 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ c)
    (hB1 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ b)
    (hB2 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ c) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k ∧ (D.tile i).angleAt j = α ∧
      ((SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k)) ∨
       (SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k))) ∧
      dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a ∧
      ∃ j' : Fin N, j' ≠ i ∧ ∃ X : Plane,
        (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
        (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
          (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D hS
  have hpi := Real.pi_pos
  obtain ⟨hc1, -, -, -, -⟩ := corner_has_alpha_tile D hα hS hk
  obtain ⟨i, hi⟩ : ∃ i : Fin N, (D.tile i).localAngle (D.target.pts k) = α := by
    have : 0 < cntA D (D.target.pts k) α := by omega
    unfold cntA at this
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, by simpa using hi⟩
  obtain ⟨j, hj, hang, hcase⟩ := corner_tile_on_sides_gen D hα0 (by linarith) k hk i hi
  have hU := tile_twoalpha D hS i
  have hopp := opp_a_of_alpha hα hU j hang
  have hor := tri_orient_a hU hab hac j hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  have hlen : dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a := hopp
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  have hlOQ : dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = b ∨
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = c := by
    rcases hor with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hlOP : dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = b ∨
      dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = c := by
    rcases hor with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩
    · exact Or.inr h1
    · exact Or.inl h1
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1 : (D.tile i).pts (j + 1) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hj2 : (D.tile i).pts (j + 2) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hAne : D.target.pts (k + 1) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k (D.target.indep.injective h)
  have hBne : D.target.pts (k + 2) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k (D.target.indep.injective h)
  have vk1 : k ≠ k + 1 := (by decide : ∀ x : Fin 3, x ≠ x + 1) k
  have vk2 : k ≠ k + 2 := (by decide : ∀ x : Fin 3, x ≠ x + 2) k
  have v12 : k + 1 ≠ k + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k
  refine ⟨i, j, hj, hang, hcase, hlen, ?_⟩
  rcases hcase with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · obtain ⟨p, hp0, hp⟩ := Erdos634.Pi3F6.rayparam hAne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := Erdos634.Pi3F6.rayparam hBne hj2 hr2
    refine aux_reflection_2a D hα hS hab hac hword i j k (k + 1) (k + 2) vk1 vk2 v12 hj hlen hp0 hr0
      hp hr ?_ ?_
    · intro h
      rcases hlOP with h' | h'
      · apply hA1; rw [← h', hj, h]
      · apply hA2; rw [← h', hj, h]
    · intro h
      rcases hlOQ with h' | h'
      · apply hB1; rw [← dist_comm, ← h', hj, h]
      · apply hB2; rw [← dist_comm, ← h', hj, h]
  · obtain ⟨p, hp0, hp⟩ := Erdos634.Pi3F6.rayparam hBne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := Erdos634.Pi3F6.rayparam hAne hj2 hr2
    refine aux_reflection_2a D hα hS hab hac hword i j k (k + 2) (k + 1) vk2 vk1 v12.symm hj hlen hp0 hr0
      hp hr ?_ ?_
    · intro h
      rcases hlOP with h' | h'
      · apply hB1; rw [← h', hj, h]
      · apply hB2; rw [← h', hj, h]
    · intro h
      rcases hlOQ with h' | h'
      · apply hA1; rw [← dist_comm, ← h', hj, h]
      · apply hA2; rw [← dist_comm, ← h', hj, h]

end Erdos634.GLC

#print axioms Erdos634.GLC.corner_tile_on_sides_gen
#print axioms Erdos634.GLC.corner_far_reflection_2a
