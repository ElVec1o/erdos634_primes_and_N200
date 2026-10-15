import Mathlib.Tactic
import Erdos634.Draft.T30LPi3F6
import Erdos634.Draft.T30LPi3Cone
import Erdos634.Draft.T30LPi3Clamp

/-!
# F6 from the corner placement: the clamps are derived, not assumed

`corner_far_reflection`: on a `CongruentDissection` with a `SixtyData` model (`α ∉ ℚπ`, `a, b, c` pairwise distinct, word lemma for `c`), at a target
corner `k` of angle `π/3` whose two adjacent sides are not of length `a` or `b` (so the tile's edges there stop short of the other target vertices),
the corner tile `T` (a tile with a vertex at the corner, `Pi3Cone.corner_tile_on_sides`) has its two edges at the corner on the two target sides, ending at
`P, Q`; `PQ` is a `c`-edge; the chord `PQ` is clamped by the two sides (`T30LPi3Clamp.clamps`) and lies in the interior; `P, Q` are non-vertex frontier
points; and by `corner_chord_reflection` the tile across `PQ` is the point reflection of `T` through the midpoint of `PQ`.  No clamp or placement hypothesis remains.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry Erdos634.Pi3Tile

theorem opp_c_of_pi3 {U : Tri} {α a b c : ℝ} (hirr : Irr α) (hU : U.SixtyData α a b c) (j : Fin 3)
    (hj : U.angleAt j = Real.pi / 3) : U.oppLen j = c := by
  obtain ⟨σ, h0, h0', h1, h1', h2, h2'⟩ := hU
  obtain ⟨m, hm⟩ := σ.surjective j
  rw [← hm] at hj ⊢
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 m with rfl | rfl | rfl
  · rw [h0] at hj; exact absurd hj (d_ag hirr)
  · rw [h1] at hj; exact absurd hj (d_bg hirr)
  · exact h2'

theorem aux_reflection {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = Real.pi / 3)
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
  have hlen : dist P Q = c := by
    have := opp_c_of_pi3 hirr (tile_sixty D hS i) j hang
    unfold Tri.oppLen at this
    exact this
  obtain ⟨f, c0, hf, hfle, hf1, hf2, hf3⟩ := exists_supporting (D.tile i) (j + 1)
  have hfle' : ∀ m, f ((D.tile i).pts m) ≤ c0 := fun m => hfle _ (subset_convexHull ℝ _ ⟨m, rfl⟩)
  have e11 : j + 1 + 1 = j + 2 := (by decide : ∀ j : Fin 3, j + 1 + 1 = j + 2) j
  rw [e11] at hf2
  obtain ⟨j', hj', X, -, hcar1, hcar2, -⟩ := corner_chord_reflection D hirr hS hac hbc hword i (j + 1)
    (P := P) (Q := Q) rfl (by rw [e11]) hlen f hf c0 hfle' hf1 hf2 g cg hg (by rw [hPform]; exact hgP) (by rw [hQform]; exact hgQ)
    h ch hh (by rw [hQform]; exact hhQ) (by rw [hPform]; exact hhP)
    (by rw [hPform, hQform]; exact hint) (by rw [hPform]; exact hfr) (by rw [hPform]; exact hnv)
  exact ⟨j', hj', X, hcar1, hcar2⟩

theorem rayparam {u e : Plane} (hu : u ≠ 0) (he : e ≠ 0) (h : SameRay ℝ u e) :
    ∃ p : ℝ, 0 < p ∧ e = p • u := by
  obtain ⟨r1, r2, h1, h2, h12⟩ := h.exists_pos hu he
  refine ⟨r1 / r2, div_pos h1 h2, ?_⟩
  have : e = (1 / r2) • (r1 • u) := by rw [h12, smul_smul, one_div, inv_mul_cancel₀ h2.ne', one_smul]
  rw [this, smul_smul]; congr 1; ring

/-- **F6 from the corner placement.**  See the module header. -/
theorem corner_far_reflection {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (k : Fin 3) (hk : D.target.angleAt k = Real.pi / 3)
    (hA1 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ a)
    (hA2 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ b)
    (hB1 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ a)
    (hB2 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ b) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k ∧
      ∃ j' : Fin N, j' ≠ i ∧ ∃ X : Plane,
        (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
        (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
          (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} := by
  obtain ⟨i, j, hj, hang, hcase⟩ := Erdos634.Pi3Cone.corner_tile_on_sides D hirr hS k hk
  have hU := tile_sixty D hS i
  have hopp := opp_c_of_pi3 hirr hU j hang
  have hor := tri_two_orient hU hac hbc j hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  -- the two edges at the corner have lengths in `{a, b}`
  have hlOQ : dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = a ∨ dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = b := by
    rcases hor with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hlOP : dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = a ∨ dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = b := by
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
  have d1 : (by decide : ∀ x : Fin 3, x ≠ x + 1) k = (by decide : ∀ x : Fin 3, x ≠ x + 1) k := rfl
  have vk1 : k ≠ k + 1 := (by decide : ∀ x : Fin 3, x ≠ x + 1) k
  have vk2 : k ≠ k + 2 := (by decide : ∀ x : Fin 3, x ≠ x + 2) k
  have v12 : k + 1 ≠ k + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k
  refine ⟨i, j, hj, ?_⟩
  rcases hcase with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · obtain ⟨p, hp0, hp⟩ := rayparam hAne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := rayparam hBne hj2 hr2
    refine aux_reflection D hirr hS hac hbc hword i j k (k + 1) (k + 2) vk1 vk2 v12 hj hang hp0 hr0
      hp hr ?_ ?_
    · intro h
      rcases hlOP with h' | h'
      · apply hA1; rw [← h', hj, h]
      · apply hA2; rw [← h', hj, h]
    · intro h
      rcases hlOQ with h' | h'
      · apply hB1; rw [← dist_comm, ← h', hj, h]
      · apply hB2; rw [← dist_comm, ← h', hj, h]
  · obtain ⟨p, hp0, hp⟩ := rayparam hBne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := rayparam hAne hj2 hr2
    refine aux_reflection D hirr hS hac hbc hword i j k (k + 2) (k + 1) vk2 vk1 v12.symm hj hang hp0 hr0
      hp hr ?_ ?_
    · intro h
      rcases hlOP with h' | h'
      · apply hB1; rw [← h', hj, h]
      · apply hB2; rw [← h', hj, h]
    · intro h
      rcases hlOQ with h' | h'
      · apply hA1; rw [← dist_comm, ← h', hj, h]
      · apply hA2; rw [← dist_comm, ← h', hj, h]

end Erdos634.Pi3F6
