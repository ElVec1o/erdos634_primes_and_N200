/-
Draft/WideColFull.lean: wide parallelograms for every member `(e, f)`, `1 ≤ e < f`.

Tile `(a, b, c) = (ef, f² − e², f²)`, `N₁ = 3f² − e²`, `Y₁ = e N₁` (base), `X₁ = f³` (leg), `cos β = Y₁ / (2 X₁)`.
The `a × c` cell is the parallelogram with sides `a`, `c` and angle `β`: two tiles glued along their `b`-edge.

* `widecol_arith`: for coprime `(e, f)`, `a ∣ p Y₁ ↔ f ∣ p` (the base side is a whole number of `a`-cells exactly
  when `f ∣ p`); `widecol_leg`: `c ∣ q X₁` always.
* `widecol_grid`: for `p = f p'`, the parallelogram with sides `p Y₁` and `q X₁` and angle `β` is tiled by
  `2 p q N₁` copies of the tile: the `(p N₁ / f) × (q f)` grid of `a × c` cells.

Frame.  `S2G` works in the skew frame `Phi F` (unit vectors `g1`, `g2 F` with inner product `1/(2F)`) for every real
`F` with `1 < 4F²`, negative values included.  With `F = −f³ / (e N₁)` the two vectors make the angle `π − β`, the
cell `[0,a] × [0,c]` is the `a × c` parallelogram, and its diagonal from `(0,0)` to `(a,c)` has length `b`.  The
region `{s g1 + t g2}` is re-read from its other base corner as `{s (−g1) + t g2}`, where the angle is `β`.
No sorry, no native_decide.
-/
import Erdos634.Draft.S2GFrame
import Erdos634.Draft.WPgramWrap

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WideColFull

open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.WPgramWrap (Phi_zero Phi_10 Phi_01)

/-- close a field identity: clear denominators, then `ring` -/
local macro "fsr" : tactic => `(tactic| first | (field_simp; ring) | field_simp | ring)

/-! ## Arithmetic -/

/-- `gcd(f, 3f² − e²) = 1` for coprime `(e, f)` -/
theorem coprime_f_N (e f : ℕ) (hco : Nat.Coprime e f) (hef : e < f) : Nat.Coprime f (3 * f ^ 2 - e ^ 2) := by
  have hle : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith [Nat.pow_lt_pow_left hef (two_ne_zero)]
  have hd1 : Nat.gcd f (3 * f ^ 2 - e ^ 2) ∣ f := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd f (3 * f ^ 2 - e ^ 2) ∣ 3 * f ^ 2 - e ^ 2 := Nat.gcd_dvd_right _ _
  have hd3 : Nat.gcd f (3 * f ^ 2 - e ^ 2) ∣ 3 * f ^ 2 := (dvd_pow hd1 two_ne_zero).mul_left 3
  have hd4 : Nat.gcd f (3 * f ^ 2 - e ^ 2) ∣ e ^ 2 :=
    (Nat.dvd_add_right hd2).mp (by rw [Nat.sub_add_cancel hle]; exact hd3)
  have hc2 : Nat.Coprime f (e ^ 2) := hco.symm.pow_right 2
  have h := Nat.dvd_gcd hd1 hd4
  rw [Nat.Coprime.gcd_eq_one hc2] at h
  exact Nat.dvd_one.mp h

/-- **The base side `p Y₁` is a whole number of `a`-cells exactly when `f ∣ p`.** -/
theorem widecol_arith (e f p : ℕ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    e * f ∣ p * (e * (3 * f ^ 2 - e ^ 2)) ↔ f ∣ p := by
  constructor
  · intro h
    rw [Nat.mul_left_comm] at h
    have h1 : f ∣ p * (3 * f ^ 2 - e ^ 2) := (Nat.mul_dvd_mul_iff_left (by omega)).1 h
    exact (coprime_f_N e f hco hef).dvd_of_dvd_mul_right h1
  · rintro ⟨k, rfl⟩
    exact ⟨k * (3 * f ^ 2 - e ^ 2), by ring⟩

/-- the leg side `q X₁` is always a whole number of `c`-cells -/
theorem widecol_leg (f q : ℕ) : f ^ 2 ∣ q * f ^ 3 := ⟨q * f, by ring⟩

/-! ## The frame at angle `π − β` -/

/-- frame parameter: `1/(2 Fr) = −cos β` -/
noncomputable def Fr (e f : ℝ) : ℝ := -(f ^ 3 / (e * (3 * f ^ 2 - e ^ 2)))

theorem hFr {e f : ℝ} (he : 0 < e) (hef : e < f) : 1 < 4 * Fr e f ^ 2 := by
  have hf : 0 < f := he.trans hef
  have hN : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith
  have hd : 0 < e * (3 * f ^ 2 - e ^ 2) := mul_pos he hN
  have key : e * (3 * f ^ 2 - e ^ 2) < 2 * f ^ 3 := by
    have h1 : 2 * f ^ 3 - e * (3 * f ^ 2 - e ^ 2) = (f - e) ^ 2 * (2 * f + e) := by ring
    have h2 : 0 < (f - e) ^ 2 * (2 * f + e) := mul_pos (pow_pos (sub_pos.2 hef) 2) (by linarith)
    linarith
  have h2 : 1 / 2 < f ^ 3 / (e * (3 * f ^ 2 - e ^ 2)) := by
    rw [lt_div_iff₀ hd]
    linarith
  unfold Fr
  rw [neg_sq]
  nlinarith

theorem norm_g1' {F : ℝ} (hF : 1 < 4 * F ^ 2) : ‖g1‖ = 1 := by
  have h := Erdos634.Draft.S2G.sq_Phi' hF (1, 0) (0, 0)
  rw [Phi_10, Phi_zero, dist_zero_right] at h
  have h1 : ‖g1‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]; simp
  exact Erdos634.Draft.SumTwoSquares.eqsq (norm_nonneg _) zero_le_one h1

theorem norm_g2' {F : ℝ} (hF : 1 < 4 * F ^ 2) : ‖g2 F‖ = 1 := by
  have h := Erdos634.Draft.S2G.sq_Phi' hF (0, 1) (0, 0)
  rw [Phi_01, Phi_zero, dist_zero_right] at h
  have h1 : ‖g2 F‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]; simp
  exact Erdos634.Draft.SumTwoSquares.eqsq (norm_nonneg _) zero_le_one h1

/-! ## The tile and the cell -/

section real

variable {E Fv : ℝ}

/-- the tile: the lower half of the cell `[0, a] × [0, c]` -/
noncomputable def MT (E Fv : ℝ) (he : 0 < E) (hef : E < Fv) : Tri :=
  Erdos634.Draft.S2G.brickL (Fr E Fv) (hFr he hef) (E * Fv) (Fv ^ 2) (mul_pos he (he.trans hef))
    (pow_pos (he.trans hef) 2)

theorem MT_pts (he : 0 < E) (hef : E < Fv) :
    (MT E Fv he hef).pts = ![Phi (Fr E Fv) (0, 0), Phi (Fr E Fv) (E * Fv, 0), Phi (Fr E Fv) (E * Fv, Fv ^ 2)] := by
  simp only [MT, Erdos634.Draft.S2G.brickL, Erdos634.Draft.S2G.triC_pts]

theorem MT_p0 (he : 0 < E) (hef : E < Fv) : (MT E Fv he hef).pts 0 = Phi (Fr E Fv) (0, 0) := by
  rw [MT_pts]; rfl

theorem MT_p1 (he : 0 < E) (hef : E < Fv) : (MT E Fv he hef).pts 1 = Phi (Fr E Fv) (E * Fv, 0) := by
  rw [MT_pts]; rfl

theorem MT_p2 (he : 0 < E) (hef : E < Fv) : (MT E Fv he hef).pts 2 = Phi (Fr E Fv) (E * Fv, Fv ^ 2) := by
  rw [MT_pts]; rfl

/-- the sides of the tile: `a = ef`, `c = f²`, `b = f² − e²` -/
theorem MT_sides (he : 0 < E) (hef : E < Fv) :
    dist ((MT E Fv he hef).pts 0) ((MT E Fv he hef).pts 1) = E * Fv ∧
    dist ((MT E Fv he hef).pts 1) ((MT E Fv he hef).pts 2) = Fv ^ 2 ∧
    dist ((MT E Fv he hef).pts 2) ((MT E Fv he hef).pts 0) = Fv ^ 2 - E ^ 2 := by
  have hf : 0 < Fv := he.trans hef
  have hN : 0 < 3 * Fv ^ 2 - E ^ 2 := by nlinarith
  have hf0 : Fv ≠ 0 := hf.ne'
  have he0 : E ≠ 0 := he.ne'
  have hN0 : 3 * Fv ^ 2 - E ^ 2 ≠ 0 := hN.ne'
  have hF := hFr he hef
  have hb : 0 ≤ Fv ^ 2 - E ^ 2 := by nlinarith [mul_pos (sub_pos.2 hef) (add_pos hf he)]
  rw [MT_p0 he hef, MT_p1 he hef, MT_p2 he hef]
  refine ⟨?_, ?_, ?_⟩
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg (mul_pos he hf).le
    rw [Erdos634.Draft.S2G.sq_Phi' hF]
    dsimp only
    ring
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg (pow_pos hf 2).le
    rw [Erdos634.Draft.S2G.sq_Phi' hF]
    dsimp only
    ring
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hb
    rw [Erdos634.Draft.S2G.sq_Phi' hF]
    dsimp only
    unfold Fr
    fsr

/-- the angle of the tile between its sides `a` and `c` (the angle `β`, opposite `b`) is the angle between
`−g1` and `g2` -/
theorem MT_angle (he : 0 < E) (hef : E < Fv) :
    (MT E Fv he hef).angleAt 1 = InnerProductGeometry.angle (-g1) (g2 (Fr E Fv)) := by
  have hf : 0 < Fv := he.trans hef
  have e21 : (MT E Fv he hef).pts 2 -ᵥ (MT E Fv he hef).pts 1 = (Fv ^ 2) • g2 (Fr E Fv) := by
    rw [MT_p2 he hef, MT_p1 he hef, vsub_eq_sub]
    unfold Phi
    dsimp only
    module
  have e01 : (MT E Fv he hef).pts 0 -ᵥ (MT E Fv he hef).pts 1 = (E * Fv) • (-g1) := by
    rw [MT_p0 he hef, MT_p1 he hef, vsub_eq_sub]
    unfold Phi
    dsimp only
    module
  unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
  rw [show ((1 : Fin 3) + 1) = 2 from rfl, show ((1 : Fin 3) + 2) = 0 from rfl, e21, e01,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (pow_pos hf 2),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (mul_pos he hf), InnerProductGeometry.angle_comm]

/-- the `(k+1) × (l+1)` grid of `a × c` cells, two tiles per cell -/
theorem grid_real (he : 0 < E) (hef : E < Fv) (k l : ℕ) :
    Nonempty (RTiling (Phi (Fr E Fv) '' Rect 0 (E * Fv * ((k : ℝ) + 1)) 0 (Fv ^ 2 * ((l : ℝ) + 1)))
      (MT E Fv he hef) (2 * (k + 1) * (l + 1))) :=
  ⟨Erdos634.Draft.S2G.grid (hFr he hef) (mul_pos he (he.trans hef)) (pow_pos (he.trans hef) 2)
    (Erdos634.Draft.S2G.brick_rt (Fr E Fv) (hFr he hef) (E * Fv) (Fv ^ 2) (mul_pos he (he.trans hef))
      (pow_pos (he.trans hef) 2) (MT E Fv he hef) (Tri.Congruent.refl _)
      (Erdos634.Draft.S2G.cong_U_cell (hFr he hef) (E * Fv) (Fv ^ 2) (mul_pos he (he.trans hef))
        (pow_pos (he.trans hef) 2))) k l⟩

end real

/-- the frame rectangle `[0,S] × [0,T]`, moved so that its corner `S g1` is the origin, is the parallelogram
spanned by `−g1` and `g2` -/
theorem pgram_set (F S T : ℝ) :
    (IsometryEquiv.addRight (-(S • g1)) : Plane ≃ᵢ Plane) '' (Phi F '' Rect 0 S 0 T)
      = {x : Plane | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ S ∧ 0 ≤ t ∧ t ≤ T ∧ x = s • (-g1) + t • g2 F} := by
  ext x
  constructor
  · rintro ⟨_, ⟨⟨s, t⟩, ⟨h1, h2, h3, h4⟩, rfl⟩, rfl⟩
    refine ⟨S - s, t, sub_nonneg.2 h2, sub_le_self S h1, h3, h4, ?_⟩
    show s • g1 + t • g2 F + -(S • g1) = _
    module
  · rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
    refine ⟨Phi F (S - s, t), ⟨(S - s, t), ⟨sub_nonneg.2 h2, sub_le_self S h1, h3, h4⟩, rfl⟩, ?_⟩
    show (S - s) • g1 + t • g2 F + -(S • g1) = _
    module

/-- the tile `(ef, f², f² − e²)` for natural `1 ≤ e < f` -/
noncomputable def MTn (e f : ℕ) (he : 1 ≤ e) (hef : e < f) : Tri :=
  MT (e : ℝ) (f : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef)

/-- frame form of the grid: for `p = f p'` the frame rectangle `[0, p Y₁] × [0, q X₁]` is tiled by
`2 p q (3f² − e²)` tiles -/
theorem rect_grid (e f p' q : ℕ) (he : 1 ≤ e) (hef : e < f) (hp : 1 ≤ p') (hq : 1 ≤ q) :
    Nonempty (RTiling (Phi (Fr (e : ℝ) (f : ℝ)) ''
        Rect 0 (((f * p' : ℕ) : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) 0 ((q : ℝ) * (f : ℝ) ^ 3))
      (MTn e f he hef) (2 * (f * p') * q * (3 * f ^ 2 - e ^ 2))) := by
  have heR : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.2 he
  have hefR : (e : ℝ) < (f : ℝ) := Nat.cast_lt.2 hef
  have hsq : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef two_ne_zero
  have hN : 1 ≤ 3 * f ^ 2 - e ^ 2 := by omega
  have hk : 1 ≤ p' * (3 * f ^ 2 - e ^ 2) := Nat.mul_pos hp hN
  have hl : 1 ≤ q * f := Nat.mul_pos hq (by omega)
  have h1k : p' * (3 * f ^ 2 - e ^ 2) - 1 + 1 = p' * (3 * f ^ 2 - e ^ 2) := by omega
  have h1l : q * f - 1 + 1 = q * f := by omega
  have hNR : ((3 * f ^ 2 - e ^ 2 : ℕ) : ℝ) = 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have h : 3 * f ^ 2 - e ^ 2 + e ^ 2 = 3 * f ^ 2 := by omega
    have h' : ((3 * f ^ 2 - e ^ 2 : ℕ) : ℝ) + (e : ℝ) ^ 2 = 3 * (f : ℝ) ^ 2 := by exact_mod_cast h
    linarith
  have ck : (((p' * (3 * f ^ 2 - e ^ 2) - 1 : ℕ) : ℝ) + 1) = (p' : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have h2 : (((p' * (3 * f ^ 2 - e ^ 2) - 1 : ℕ) : ℝ) + 1) = ((p' * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast h1k
    rw [h2, Nat.cast_mul, hNR]
  have cl : (((q * f - 1 : ℕ) : ℝ) + 1) = (q : ℝ) * (f : ℝ) := by exact_mod_cast h1l
  obtain ⟨R⟩ := grid_real heR hefR (p' * (3 * f ^ 2 - e ^ 2) - 1) (q * f - 1)
  have hS : (e : ℝ) * (f : ℝ) * ((((p' * (3 * f ^ 2 - e ^ 2) - 1 : ℕ) : ℝ)) + 1)
      = ((f * p' : ℕ) : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [ck, Nat.cast_mul]
    ring
  have hT : (f : ℝ) ^ 2 * ((((q * f - 1 : ℕ) : ℝ)) + 1) = (q : ℝ) * (f : ℝ) ^ 3 := by
    rw [cl]
    ring
  rw [hS, hT] at R
  refine ⟨RTiling.castN ?_ R⟩
  rw [h1k, h1l]
  ring

/-- **`prop:widecol`, the grid.**  For `1 ≤ e < f` and `p = f p'`, the parallelogram with sides `p Y₁` (direction
`u`) and `q X₁` (direction `w`), `Y₁ = e (3f² − e²)`, `X₁ = f³`, whose angle is the angle `β` of the tile
`(ef, f² − e², f²)` between its sides `ef` and `f²`, is tiled by `2 p q (3f² − e²)` copies of the tile. -/
theorem widecol_grid (e f p' q : ℕ) (he : 1 ≤ e) (hef : e < f) (hp : 1 ≤ p') (hq : 1 ≤ q) :
    ∃ (u w : Plane) (M : Tri), ‖u‖ = 1 ∧ ‖w‖ = 1 ∧
      dist (M.pts 0) (M.pts 1) = (e : ℝ) * f ∧ dist (M.pts 1) (M.pts 2) = (f : ℝ) ^ 2 ∧
      dist (M.pts 2) (M.pts 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      InnerProductGeometry.angle u w = M.angleAt 1 ∧
      Nonempty (RTiling {x : Plane | ∃ s t : ℝ, 0 ≤ s ∧
          s ≤ ((f * p' : ℕ) : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧ 0 ≤ t ∧
          t ≤ (q : ℝ) * (f : ℝ) ^ 3 ∧ x = s • u + t • w} M (2 * (f * p') * q * (3 * f ^ 2 - e ^ 2))) := by
  have heR : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.2 he
  have hefR : (e : ℝ) < (f : ℝ) := Nat.cast_lt.2 hef
  have hF := hFr heR hefR
  obtain ⟨s1, s2, s3⟩ := MT_sides heR hefR
  obtain ⟨R⟩ := rect_grid e f p' q he hef hp hq
  have R2 := map R (IsometryEquiv.addRight
    (-((((f * p' : ℕ) : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) • g1)))
  rw [pgram_set] at R2
  refine ⟨-g1, g2 (Fr (e : ℝ) (f : ℝ)), MTn e f he hef, ?_, norm_g2' hF, s1, s2, s3,
    (MT_angle heR hefR).symm, ⟨R2⟩⟩
  rw [norm_neg]
  exact norm_g1' hF

end Erdos634.Draft.WideColFull

#print axioms Erdos634.Draft.WideColFull.widecol_arith
#print axioms Erdos634.Draft.WideColFull.rect_grid
#print axioms Erdos634.Draft.WideColFull.widecol_grid
