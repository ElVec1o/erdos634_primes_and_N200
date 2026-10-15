/-
Draft/AddLawFull.lean -- the addition law for the base-`β` targets `Δ_m`.

Member `(e, f)`, `1 ≤ e < f`; tile `(a, b, c) = (ef, f² − e², f²)`; `N₁ = 3f² − e²`, `Y₁ = e N₁`, `X₁ = f³`.
`Δ_m` is the isosceles triangle with base `m Y₁` and legs `m X₁` (`DTn`, sides in `DT_sides`).

`thm_addlaw`: if `Δ_{m₁}` and `Δ_{m₂}` are cut into copies of the tile, and `f ∣ m₁` or `e = 1`, then `Δ_{m₁+m₂}`
is cut into copies of the tile, with `N₂ + 2 m₁ m₂ N₁ + N₁'` tiles.

Proof.  In the frame `Phi (Fr e f)` of `WideColFull` (unit vectors at angle `π − β`), `Δ_m` is the lower triangle
`LT (m Y₁) (m X₁)` of the frame rectangle.  `LT_add`:
  `LT((m₁+m₂)Y₁, (m₁+m₂)X₁) = LT(m₂Y₁, m₂X₁) ∪ [m₂Y₁, (m₁+m₂)Y₁] × [0, m₂X₁] ∪ ((m₂Y₁, m₂X₁) + LT(m₁Y₁, m₁X₁))`.
The rectangle has sides `m₁ Y₁` (base direction) and `m₂ X₁` (leg direction): it is the `a × c` grid of
`WideColFull.rect_grid` when `f ∣ m₁`, and an `m₁ × m₂` array of unit parallelograms `P₁`
(`PgramE1Full.P1_pgram`, moved into this frame by a point reflection, `seed_e1`) when `e = 1`.

Hypotheses.  `AddLawWitness.lean` exhibits a dissection satisfying them at `(e, f) = (1, 2)`, `m = 2`.  For
`e ≥ 2` no tileable `Δ_m` is known, so the branch `f ∣ m₁` is not known to be non-vacuous there.
No sorry, no native_decide.
-/
import Erdos634.Draft.WideColFull
import Erdos634.Draft.PgramE1Full

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.AddLawFull

open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WideColFull
open Erdos634.Draft.WPgramWrap (Phi_zero Phi_10 Phi_01 MF_sides)
open Erdos634.Draft.WBrickF (MF)
open Erdos634.Draft.WPgramF (hF)

/-- close a field identity: clear denominators, then `ring` -/
local macro "fsr" : tactic => `(tactic| first | (field_simp; ring) | field_simp | ring)

/-! ## The decomposition of the frame triangle -/

theorem LT_add (Y X m₁ m₂ : ℝ) (hY : 0 < Y) (hX : 0 < X) (h1 : 0 < m₁) (h2 : 0 < m₂) :
    (WBrickF.LT (m₂ * Y) (m₂ * X) ∪ Rect (m₂ * Y) ((m₁ + m₂) * Y) 0 (m₂ * X)) ∪
      Sh (m₂ * Y, m₂ * X) (WBrickF.LT (m₁ * Y) (m₁ * X))
      = WBrickF.LT ((m₁ + m₂) * Y) ((m₁ + m₂) * X) := by
  have h12 : 0 < m₁ + m₂ := add_pos h1 h2
  ext p
  obtain ⟨s, t⟩ := p
  simp only [WBrickF.LT, Rect, Sh, Set.mem_union, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub]
  constructor
  · rintro ((⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3, a4⟩)
    · have hk : t * Y ≤ s * X := le_of_mul_le_mul_left (by linarith) h2
      exact ⟨a1, by nlinarith [mul_pos h1 hY], a3,
        by nlinarith [mul_le_mul_of_nonneg_left hk h12.le]⟩
    · have hk : t * Y ≤ s * X := by
        nlinarith [mul_le_mul_of_nonneg_right a4 hY.le, mul_le_mul_of_nonneg_right a1 hX.le]
      exact ⟨by nlinarith [mul_pos h2 hY], a2, a3, by nlinarith [mul_le_mul_of_nonneg_left hk h12.le]⟩
    · have hk' : (t - m₂ * X) * Y ≤ (s - m₂ * Y) * X := le_of_mul_le_mul_left (by linarith) h1
      have hk : t * Y ≤ s * X := by linarith
      exact ⟨by nlinarith [mul_pos h2 hY], by linarith, by nlinarith [mul_pos h2 hX],
        by nlinarith [mul_le_mul_of_nonneg_left hk h12.le]⟩
  · rintro ⟨a1, a2, a3, a4⟩
    have hk : t * Y ≤ s * X := le_of_mul_le_mul_left (by linarith) h12
    by_cases hs : s ≤ m₂ * Y
    · left; left
      exact ⟨a1, hs, a3, by nlinarith [mul_le_mul_of_nonneg_left hk h2.le]⟩
    · push Not at hs
      by_cases ht : t ≤ m₂ * X
      · left; right
        exact ⟨hs.le, a2, a3, ht⟩
      · push Not at ht
        right
        exact ⟨by linarith, by linarith, by linarith, by nlinarith [mul_le_mul_of_nonneg_left hk h1.le]⟩

/-- **The addition step in a frame.**  Tilings of the two triangles and of the rectangle between them give a
tiling of the sum triangle. -/
theorem add_region {F : ℝ} (hFr' : 1 < 4 * F ^ 2) {M : Tri} (Y X m₁ m₂ : ℝ) (hY : 0 < Y) (hX : 0 < X)
    (h1 : 0 < m₁) (h2 : 0 < m₂) {N₁ N₂ Nc : ℕ}
    (R₁ : RTiling (Phi F '' WBrickF.LT (m₁ * Y) (m₁ * X)) M N₁)
    (R₂ : RTiling (Phi F '' WBrickF.LT (m₂ * Y) (m₂ * X)) M N₂)
    (Rc : RTiling (Phi F '' Rect 0 (m₁ * Y) 0 (m₂ * X)) M Nc) :
    Nonempty (RTiling (Phi F '' WBrickF.LT ((m₁ + m₂) * Y) ((m₁ + m₂) * X)) M (N₂ + Nc + N₁)) := by
  have Rc' := BrickGridF.shift_rect Rc (m₂ * Y) 0 ((m₁ + m₂) * Y) (m₂ * X) (by ring) (by ring)
  have R₁' := shiftR R₁ (m₂ * Y, m₂ * X)
  have d1 : Disjoint (interior (Phi F '' WBrickF.LT (m₂ * Y) (m₂ * X)))
      (interior (Phi F '' Rect (m₂ * Y) ((m₁ + m₂) * Y) 0 (m₂ * X))) :=
    S2G.disjoint_image' hFr' (interior_disj_fst (m₂ * Y) (fun p hp => hp.2.1) (fun p hp => hp.1))
  have U1 := union R₂ Rc' d1
  rw [← Set.image_union] at U1
  have d2 : Disjoint
      (interior (Phi F '' (WBrickF.LT (m₂ * Y) (m₂ * X) ∪ Rect (m₂ * Y) ((m₁ + m₂) * Y) 0 (m₂ * X))))
      (interior (Phi F '' Sh (m₂ * Y, m₂ * X) (WBrickF.LT (m₁ * Y) (m₁ * X)))) := by
    refine S2G.disjoint_image' hFr' (interior_disj_snd (m₂ * X) ?_ ?_)
    · rintro p (hp | hp)
      · have a2 : p.1 ≤ m₂ * Y := hp.2.1
        have a4 : p.2 * (m₂ * Y) ≤ p.1 * (m₂ * X) := hp.2.2.2
        have h3 : p.2 * (m₂ * Y) ≤ m₂ * X * (m₂ * Y) := by
          nlinarith [mul_le_mul_of_nonneg_right a2 (mul_pos h2 hX).le]
        exact le_of_mul_le_mul_right h3 (mul_pos h2 hY)
      · exact hp.2.2.2
    · intro p hp
      have h3 : 0 ≤ (p - (m₂ * Y, m₂ * X)).2 := hp.2.2.1
      simp only [Prod.snd_sub] at h3
      linarith
  have U2 := union U1 R₁' d2
  rw [← Set.image_union, LT_add Y X m₁ m₂ hY hX h1 h2] at U2
  exact ⟨U2⟩

/-! ## The triangle `Δ_m` -/

/-- `Δ_m` in the frame: vertices `(0,0)`, `(m Y₁, 0)`, `(m Y₁, m X₁)` -/
noncomputable def DT (E Fv : ℝ) (he : 0 < E) (hef : E < Fv) (m : ℝ) (hm : 0 < m) : Tri :=
  S2G.brickL (Fr E Fv) (hFr he hef) (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3)
    (mul_pos hm (mul_pos he (by nlinarith [he.trans hef])))
    (mul_pos hm (pow_pos (he.trans hef) 3))

theorem carrier_DT (E Fv : ℝ) (he : 0 < E) (hef : E < Fv) (m : ℝ) (hm : 0 < m) :
    (DT E Fv he hef m hm).carrier
      = Phi (Fr E Fv) '' WBrickF.LT (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3) :=
  S2G.carrier_brickL _ _ _ _ _ _

/-- the sides of `Δ_m`: base `m Y₁`, legs `m X₁` -/
theorem DT_sides (E Fv : ℝ) (he : 0 < E) (hef : E < Fv) (m : ℝ) (hm : 0 < m) :
    dist ((DT E Fv he hef m hm).pts 0) ((DT E Fv he hef m hm).pts 1) = m * (E * (3 * Fv ^ 2 - E ^ 2)) ∧
    dist ((DT E Fv he hef m hm).pts 1) ((DT E Fv he hef m hm).pts 2) = m * Fv ^ 3 ∧
    dist ((DT E Fv he hef m hm).pts 2) ((DT E Fv he hef m hm).pts 0) = m * Fv ^ 3 := by
  have hf : 0 < Fv := he.trans hef
  have hN : 0 < 3 * Fv ^ 2 - E ^ 2 := by nlinarith
  have hf0 : Fv ≠ 0 := hf.ne'
  have he0 : E ≠ 0 := he.ne'
  have hN0 : 3 * Fv ^ 2 - E ^ 2 ≠ 0 := hN.ne'
  have hφ := hFr he hef
  have hY : 0 < m * (E * (3 * Fv ^ 2 - E ^ 2)) := mul_pos hm (mul_pos he hN)
  have hX : 0 < m * Fv ^ 3 := mul_pos hm (pow_pos hf 3)
  have hp : (DT E Fv he hef m hm).pts
      = ![Phi (Fr E Fv) (0, 0), Phi (Fr E Fv) (m * (E * (3 * Fv ^ 2 - E ^ 2)), 0),
          Phi (Fr E Fv) (m * (E * (3 * Fv ^ 2 - E ^ 2)), m * Fv ^ 3)] := by
    simp only [DT, S2G.brickL, S2G.triC_pts]
  have p0 : (DT E Fv he hef m hm).pts 0 = Phi (Fr E Fv) (0, 0) := by rw [hp]; rfl
  have p1 : (DT E Fv he hef m hm).pts 1 = Phi (Fr E Fv) (m * (E * (3 * Fv ^ 2 - E ^ 2)), 0) := by
    rw [hp]; rfl
  have p2 : (DT E Fv he hef m hm).pts 2
      = Phi (Fr E Fv) (m * (E * (3 * Fv ^ 2 - E ^ 2)), m * Fv ^ 3) := by rw [hp]; rfl
  rw [p0, p1, p2]
  refine ⟨?_, ?_, ?_⟩
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hY.le
    rw [S2G.sq_Phi' hφ]
    dsimp only
    ring
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hX.le
    rw [S2G.sq_Phi' hφ]
    dsimp only
    ring
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hX.le
    rw [S2G.sq_Phi' hφ]
    dsimp only
    unfold Fr
    fsr

/-- `Δ_m` for natural parameters -/
noncomputable def DTn (e f m : ℕ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) : Tri :=
  DT (e : ℝ) (f : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (m : ℝ) (Nat.cast_pos.2 hm)

theorem DTn_sides (e f m : ℕ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) :
    dist ((DTn e f m he hef hm).pts 0) ((DTn e f m he hef hm).pts 1)
      = (m : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
    dist ((DTn e f m he hef hm).pts 1) ((DTn e f m he hef hm).pts 2) = (m : ℝ) * (f : ℝ) ^ 3 ∧
    dist ((DTn e f m he hef hm).pts 2) ((DTn e f m he hef hm).pts 0) = (m : ℝ) * (f : ℝ) ^ 3 :=
  DT_sides _ _ _ _ _ _

theorem MTn_sides (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    dist ((MTn e f he hef).pts 0) ((MTn e f he hef).pts 1) = (e : ℝ) * (f : ℝ) ∧
    dist ((MTn e f he hef).pts 1) ((MTn e f he hef).pts 2) = (f : ℝ) ^ 2 ∧
    dist ((MTn e f he hef).pts 2) ((MTn e f he hef).pts 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
  MT_sides _ _

/-! ## The unit parallelogram in this frame, `e = 1` -/

theorem Fr_one (F : ℝ) : Fr 1 F = -(F ^ 3 / (3 * F ^ 2 - 1)) := by
  unfold Fr
  norm_num

theorem sD_Fr_one {F : ℝ} (hF1 : 1 < F) : sD (Fr 1 F) = (F ^ 2 - 1) * sD F / (3 * F ^ 2 - 1) := by
  have hF0 : (0 : ℝ) < F := by linarith
  have hA : (0 : ℝ) < F ^ 2 - 1 := by nlinarith
  have hN : (0 : ℝ) < 3 * F ^ 2 - 1 := by nlinarith
  have hN0 : 3 * F ^ 2 - 1 ≠ 0 := hN.ne'
  have hφ := hFr (e := 1) (f := F) one_pos hF1
  refine Erdos634.Draft.SumTwoSquares.eqsq (S2G.sD_pos' hφ).le
    (div_nonneg (mul_nonneg hA.le (sD_pos hF1).le) hN.le) ?_
  rw [S2G.sD_sq' hφ, div_pow, mul_pow, sD_sq hF1, Fr_one, neg_sq, div_pow,
    eq_div_iff (pow_ne_zero 2 hN0)]
  have h3 : (F ^ 3) ^ 2 / (3 * F ^ 2 - 1) ^ 2 * (3 * F ^ 2 - 1) ^ 2 = (F ^ 3) ^ 2 :=
    div_mul_cancel₀ _ (pow_ne_zero 2 hN0)
  linear_combination 4 * h3

theorem g2_aux (F D s : ℝ) (hF0 : F ≠ 0) (hD : D ≠ 0) :
    1 * ((F ^ 2 - 1) * s / D / (2 * -(F ^ 3 / D))) = -(1 / F ^ 3 * (F * (F ^ 2 - 1) * (s / (2 * F)))) := by
  field_simp

/-- at `e = 1` the second frame vector is the reversed leg direction of `PgramE1Full` -/
theorem g2_Fr_one {F : ℝ} (hF1 : 1 < F) : g2 (Fr 1 F) = -(PgramE1Full.wdir F) := by
  have hF0 : (0 : ℝ) < F := by linarith
  have hN : (0 : ℝ) < 3 * F ^ 2 - 1 := by nlinarith
  have hN0 : 3 * F ^ 2 - 1 ≠ 0 := hN.ne'
  have hF0' : F ≠ 0 := hF0.ne'
  have hs := sD_Fr_one hF1
  have hw : PgramE1Full.wdir F = (1 / F ^ 3) • Phi F (F ^ 2, F * (F ^ 2 - 1)) := rfl
  have hg : g2 (Fr 1 F) = Phi (Fr 1 F) (0, 1) := (Phi_01 _).symm
  rw [hw, hg]
  ext i
  fin_cases i
  · show (Phi (Fr 1 F) (0, 1)) 0 = (-((1 / F ^ 3) • Phi F (F ^ 2, F * (F ^ 2 - 1)))) 0
    rw [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, Phi_apply0, Phi_apply0, Fr_one]
    dsimp only
    fsr
  · show (Phi (Fr 1 F) (0, 1)) 1 = (-((1 / F ^ 3) • Phi F (F ^ 2, F * (F ^ 2 - 1)))) 1
    rw [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, Phi_apply1, Phi_apply1, hs, Fr_one]
    dsimp only
    exact g2_aux F (3 * F ^ 2 - 1) (sD F) hF0' hN0

/-- the point reflection `x ↦ c − x` -/
noncomputable def flipIso (c : Plane) : Plane ≃ᵢ Plane :=
  (LinearIsometryEquiv.neg ℝ : Plane ≃ₗᵢ[ℝ] Plane).toIsometryEquiv.trans (IsometryEquiv.addRight c)

theorem flipIso_apply (c x : Plane) : flipIso c x = -x + c := rfl

/-- the rotation `0 ↦ 2, 1 ↦ 0, 2 ↦ 1` of the vertex labels -/
def rot : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 1 2

theorem rot0 : rot 0 = 2 := by decide
theorem rot1 : rot 1 = 0 := by decide
theorem rot2 : rot 2 = 1 := by decide

/-- SSS with the vertices of the second triangle rotated -/
theorem cong_cycle {T U : Tri} (h01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 2) (U.pts 0))
    (h12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 0) (U.pts 1))
    (h20 : dist (T.pts 2) (T.pts 0) = dist (U.pts 1) (U.pts 2)) : T.Congruent U := by
  refine (Erdos634.SssCongruent.congruent_of_dist_three (U := U.relabel rot) ?_ ?_ ?_).trans
    (U.congruent_relabel rot).symm
  · rw [Tri.relabel_pts, Tri.relabel_pts, rot0, rot1]
    exact h01
  · rw [Tri.relabel_pts, Tri.relabel_pts, rot1, rot2]
    exact h12
  · rw [Tri.relabel_pts, Tri.relabel_pts, rot2, rot0]
    exact h20

/-- the tile of `PgramE1Full` is the tile of this file at `e = 1` -/
theorem MF_cong_MT {F : ℝ} (hF1 : 1 < F) : (MF F hF1).Congruent (MT 1 F one_pos hF1) := by
  obtain ⟨s1, s2, s3⟩ := MF_sides hF1
  obtain ⟨t1, t2, t3⟩ := MT_sides (E := 1) (Fv := F) one_pos hF1
  refine cong_cycle ?_ ?_ ?_
  · rw [s1, t3]
    ring
  · rw [s2, t1]
    ring
  · rw [dist_comm, s3, t2]

/-- **The unit parallelogram in the frame, `e = 1`.**  `E` is a real number equal to `1`, so that the statement
applies to the cast of the natural number `1`. -/
theorem seed_e1 (f : ℕ) (hf : 2 ≤ f) (E : ℝ) (hE : E = 1) (he : 0 < E) (hef : E < (f : ℝ)) :
    Nonempty (RTiling (Phi (Fr E (f : ℝ)) '' Rect 0 (E * (3 * (f : ℝ) ^ 2 - E ^ 2)) 0 ((f : ℝ) ^ 3))
      (MT E (f : ℝ) he hef) (2 * (3 * f ^ 2 - 1))) := by
  subst hE
  have h1 := hF f hf
  obtain ⟨R⟩ := PgramE1Full.P1_pgram f hf
  have R2 := map R (flipIso ((3 * (f : ℝ) ^ 2 - 1) • g1))
  have hset : (flipIso ((3 * (f : ℝ) ^ 2 - 1) • g1)) '' {p : Plane | ∃ s t : ℝ, 0 ≤ s ∧
        s ≤ 3 * (f : ℝ) ^ 2 - 1 ∧ 0 ≤ t ∧ t ≤ (f : ℝ) ^ 3 ∧ p = s • g1 + t • PgramE1Full.wdir (f : ℝ)}
      = Phi (Fr 1 (f : ℝ)) '' Rect 0 (1 * (3 * (f : ℝ) ^ 2 - 1 ^ 2)) 0 ((f : ℝ) ^ 3) := by
    have e1 : (1 : ℝ) * (3 * (f : ℝ) ^ 2 - 1 ^ 2) = 3 * (f : ℝ) ^ 2 - 1 := by ring
    rw [e1]
    ext x
    constructor
    · rintro ⟨_, ⟨s, t, a1, a2, a3, a4, rfl⟩, rfl⟩
      rw [flipIso_apply]
      refine ⟨(3 * (f : ℝ) ^ 2 - 1 - s, t), ⟨sub_nonneg.2 a2, sub_le_self _ a1, a3, a4⟩, ?_⟩
      show (3 * (f : ℝ) ^ 2 - 1 - s) • g1 + t • g2 (Fr 1 (f : ℝ)) = _
      rw [g2_Fr_one h1]
      module
    · rintro ⟨⟨s, t⟩, ⟨a1, a2, a3, a4⟩, rfl⟩
      refine ⟨(3 * (f : ℝ) ^ 2 - 1 - s) • g1 + t • PgramE1Full.wdir (f : ℝ),
        ⟨3 * (f : ℝ) ^ 2 - 1 - s, t, sub_nonneg.2 a2, sub_le_self _ a1, a3, a4, rfl⟩, ?_⟩
      rw [flipIso_apply]
      show _ = s • g1 + t • g2 (Fr 1 (f : ℝ))
      rw [g2_Fr_one h1]
      module
  exact ⟨remodel (RTiling.cast hset R2) (MF_cong_MT h1)⟩

/-! ## The rectangle between the two triangles -/

/-- the rectangle `[0, m₁ Y₁] × [0, m₂ X₁]` of the frame is tiled by `2 m₁ m₂ N₁` tiles when `f ∣ m₁` or `e = 1` -/
theorem rect_tiling (e f m₁ m₂ : ℕ) (he : 1 ≤ e) (hef : e < f) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (h : f ∣ m₁ ∨ e = 1) :
    Nonempty (RTiling (Phi (Fr (e : ℝ) (f : ℝ)) ''
        Rect 0 ((m₁ : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) 0 ((m₂ : ℝ) * (f : ℝ) ^ 3))
      (MTn e f he hef) (2 * m₁ * m₂ * (3 * f ^ 2 - e ^ 2))) := by
  rcases h with ⟨p', rfl⟩ | h1
  · have hp : 1 ≤ p' := by
      rcases Nat.eq_zero_or_pos p' with h0 | h0
      · rw [h0, Nat.mul_zero] at hm₁
        omega
      · exact h0
    exact rect_grid e f p' m₂ he hef hp hm₂
  · subst h1
    have hf : 2 ≤ f := hef
    have heR : (0 : ℝ) < ((1 : ℕ) : ℝ) := Nat.cast_pos.2 he
    have hefR : ((1 : ℕ) : ℝ) < (f : ℝ) := Nat.cast_lt.2 hef
    have hfR : (0 : ℝ) < (f : ℝ) := heR.trans hefR
    have hN : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2 := by nlinarith
    obtain ⟨S⟩ := seed_e1 f hf ((1 : ℕ) : ℝ) Nat.cast_one heR hefR
    have G := S2G.grid (hFr heR hefR) (mul_pos heR hN) (pow_pos hfR 3) S (m₁ - 1) (m₂ - 1)
    have c1 : (((m₁ - 1 : ℕ) : ℝ) + 1) = (m₁ : ℝ) := by
      have h : m₁ - 1 + 1 = m₁ := by omega
      exact_mod_cast h
    have c2 : (((m₂ - 1 : ℕ) : ℝ) + 1) = (m₂ : ℝ) := by
      have h : m₂ - 1 + 1 = m₂ := by omega
      exact_mod_cast h
    rw [c1, c2] at G
    have hset : Phi (Fr ((1 : ℕ) : ℝ) (f : ℝ)) ''
          Rect 0 (((1 : ℕ) : ℝ) * (3 * (f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) * (m₁ : ℝ)) 0 ((f : ℝ) ^ 3 * (m₂ : ℝ))
        = Phi (Fr ((1 : ℕ) : ℝ) (f : ℝ)) ''
          Rect 0 ((m₁ : ℝ) * (((1 : ℕ) : ℝ) * (3 * (f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2))) 0
            ((m₂ : ℝ) * (f : ℝ) ^ 3) := by
      rw [mul_comm (((1 : ℕ) : ℝ) * (3 * (f : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2)) (m₁ : ℝ),
        mul_comm ((f : ℝ) ^ 3) (m₂ : ℝ)]
    refine ⟨RTiling.castN ?_ (RTiling.cast hset G)⟩
    have e1 : m₁ - 1 + 1 = m₁ := by omega
    have e2 : m₂ - 1 + 1 = m₂ := by omega
    rw [e1, e2, one_pow]
    ring

/-! ## The addition law -/

/-- **`thm:addlaw`, region form.** -/
theorem addlaw_region (e f m₁ m₂ : ℕ) (he : 1 ≤ e) (hef : e < f) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (h : f ∣ m₁ ∨ e = 1) {N₁ N₂ : ℕ}
    (R₁ : RTiling (DTn e f m₁ he hef hm₁).carrier (MTn e f he hef) N₁)
    (R₂ : RTiling (DTn e f m₂ he hef hm₂).carrier (MTn e f he hef) N₂) :
    Nonempty (RTiling (DTn e f (m₁ + m₂) he hef (by omega)).carrier (MTn e f he hef)
      (N₂ + 2 * m₁ * m₂ * (3 * f ^ 2 - e ^ 2) + N₁)) := by
  have heR : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.2 he
  have hefR : (e : ℝ) < (f : ℝ) := Nat.cast_lt.2 hef
  have hfR : (0 : ℝ) < (f : ℝ) := heR.trans hefR
  have hN : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  obtain ⟨Rc⟩ := rect_tiling e f m₁ m₂ he hef hm₁ hm₂ h
  have R₁' := RTiling.cast (carrier_DT _ _ heR hefR _ (Nat.cast_pos.2 hm₁)) R₁
  have R₂' := RTiling.cast (carrier_DT _ _ heR hefR _ (Nat.cast_pos.2 hm₂)) R₂
  obtain ⟨U⟩ := add_region (hFr heR hefR) ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((f : ℝ) ^ 3)
    (m₁ : ℝ) (m₂ : ℝ) (mul_pos heR hN) (pow_pos hfR 3) (Nat.cast_pos.2 hm₁) (Nat.cast_pos.2 hm₂) R₁' R₂' Rc
  refine ⟨RTiling.cast ?_ U⟩
  unfold DTn
  rw [carrier_DT, Nat.cast_add]

/-- **`thm:addlaw`.**  Let `1 ≤ e < f` and `m₁, m₂ ≥ 1`, with `f ∣ m₁` or `e = 1`.  If `Δ_{m₁}` and `Δ_{m₂}` are
cut into `N₁` and `N₂` triangles congruent to the tile `(ef, f² − e², f²)`, then `Δ_{m₁+m₂}` is cut into
`N₂ + 2 m₁ m₂ (3f² − e²) + N₁` triangles congruent to the tile. -/
theorem thm_addlaw (e f m₁ m₂ : ℕ) (he : 1 ≤ e) (hef : e < f) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (h : f ∣ m₁ ∨ e = 1) {N₁ N₂ : ℕ} (D₁ : CongruentDissection N₁) (D₂ : CongruentDissection N₂)
    (hT₁ : D₁.target.Congruent (DTn e f m₁ he hef hm₁)) (hM₁ : D₁.model.Congruent (MTn e f he hef))
    (hT₂ : D₂.target.Congruent (DTn e f m₂ he hef hm₂)) (hM₂ : D₂.model.Congruent (MTn e f he hef)) :
    ∃ D : CongruentDissection (N₂ + 2 * m₁ * m₂ * (3 * f ^ 2 - e ^ 2) + N₁),
      D.target = DTn e f (m₁ + m₂) he hef (by omega) ∧ D.model = MTn e f he hef := by
  obtain ⟨R₁⟩ := WtoDeltaF.seed_of_cd D₁ _ _ hT₁ hM₁
  obtain ⟨R₂⟩ := WtoDeltaF.seed_of_cd D₂ _ _ hT₂ hM₂
  obtain ⟨U⟩ := addlaw_region e f m₁ m₂ he hef hm₁ hm₂ h R₁ R₂
  exact ⟨toCD U, rfl, rfl⟩

end Erdos634.Draft.AddLawFull

#print axioms Erdos634.Draft.AddLawFull.add_region
#print axioms Erdos634.Draft.AddLawFull.seed_e1
#print axioms Erdos634.Draft.AddLawFull.thm_addlaw
