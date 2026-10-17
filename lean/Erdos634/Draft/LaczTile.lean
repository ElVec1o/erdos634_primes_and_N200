/-
Draft/LaczTile.lean — the TILINGS of the pieces of Laczkovich's macro-dissection (geometry in `Draft.LaczGeom`) and the
assembly: for real `x y z` with `LP x y z` and natural scales the isosceles triangle `HT` is tiled by copies of the tile
`(u², v²-u², uv)` (`u = x, v = y`), see `laczReal`.  Frame `f = -x/y`, model `Mod = brickL f (xy) (bq)`.
UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.LaczGeom

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.LaczFamily
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.S2L (pack_exists)
open Erdos634.Draft.BrickGridF (shift_rect)

/-- the frame parameter: basis angle `π - α`, `cos = 1/(2f) = -v/(2u)`. -/
noncomputable def fr (x y : ℝ) : ℝ := -x / y

theorem hfr {x y z : ℝ} (h : LP x y z) : 1 < 4 * (fr x y) ^ 2 := by
  obtain ⟨hx, hy, hz, hxy, hy2, -⟩ := h
  have e : (fr x y) ^ 2 = x ^ 2 / y ^ 2 := by unfold fr; rw [neg_div, neg_sq, div_pow]
  rw [e, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
  nlinarith

theorem hcc {x y z : ℝ} (h : LP x y z) : 0 < x * y := mul_pos h.hx h.hy
theorem hbb {x y z : ℝ} (h : LP x y z) : 0 < bq x y := h.hb

/-- the model tile: legs `c = xy` and `b = y²-x²` along the axes, hypotenuse `a = x²`. -/
noncomputable def Mod {x y z : ℝ} (h : LP x y z) : Tri := brickL (fr x y) (hfr h) _ _ (hcc h) (hbb h)

theorem hab_id {x y z : ℝ} (h : LP x y z) : (x * y) ^ 2 + (bq x y) ^ 2 + (x * y) * (bq x y) / fr x y = (x ^ 2) ^ 2 := by
  have h1 : x ≠ 0 := h.hx.ne'
  have h2 : y ≠ 0 := h.hy.ne'
  unfold fr bq; field_simp; ring

/-- a scaled copy of the tile. -/
noncomputable def lad {x y z : ℝ} (h : LP x y z) (O V1 V2 : ℝ × ℝ) (k : ℕ) (hk0 : 0 < k) (hdet : cross O V1 V2 ≠ 0)
    (H01 : (V1.1 - O.1) ^ 2 + (V1.2 - O.2) ^ 2 + (V1.1 - O.1) * (V1.2 - O.2) / fr x y = ((k : ℝ) * (x * y)) ^ 2)
    (H12 : (V2.1 - V1.1) ^ 2 + (V2.2 - V1.2) ^ 2 + (V2.1 - V1.1) * (V2.2 - V1.2) / fr x y = ((k : ℝ) * bq x y) ^ 2)
    (H20 : (V2.1 - O.1) ^ 2 + (V2.2 - O.2) ^ 2 + (V2.1 - O.1) * (V2.2 - O.2) / fr x y = (k : ℝ) ^ 2 * (x ^ 2) ^ 2) :
    RTiling (Phi (fr x y) '' convexHull ℝ ({O, V1, V2} : Set (ℝ × ℝ))) (Mod h) (k * k) :=
  scaledRT (fr x y) (hfr h) O V1 V2 k hk0 (fun hh => hdet (by unfold cross; linarith)) _
    (baseTri_cong _ _ _ _ ((x ^ 2) ^ 2) (hcc h) (hbb h) (hab_id h) _ _ _ k hk0 _ H01 H12 H20)

theorem det_bl {x y z : ℝ} (h : LP x y z) : cross (P2 x y z) (P0 x y z) (P1 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have e : cross (P2 x y z) (P0 x y z) (P1 x y z) = -(z^2*y^3*x^7*(bq x y)^3) := by ug; ring
  rw [e]
  exact neg_ne_zero.mpr (by positivity)

noncomputable def R_bl {x y z : ℝ} (h : LP x y z) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = z*x^3*y*bq x y) :
    RTiling (Phi (fr x y) '' Hbl x y z) (Mod h) (k * k) :=
  lad h (P2 x y z) (P0 x y z) (P1 x y z) k hk0 (det_bl h)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P2, P0, P1, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P2, P0, P1, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P2, P0, P1, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)

theorem det_lg {x y z : ℝ} (h : LP x y z) : cross (P2 x y z) (P1 x y z) (P3 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have e : cross (P2 x y z) (P1 x y z) (P3 x y z) = -(y*z^2*x^9*(bq x y)^3) := by ug; ring
  rw [e]
  exact neg_ne_zero.mpr (by positivity)

noncomputable def R_lg {x y z : ℝ} (h : LP x y z) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = z*x^4*bq x y) :
    RTiling (Phi (fr x y) '' Hlg x y z) (Mod h) (k * k) :=
  lad h (P2 x y z) (P1 x y z) (P3 x y z) k hk0 (det_lg h)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P2, P1, P3, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P2, P1, P3, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P2, P1, P3, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)

theorem det_gr {x y z : ℝ} (h : LP x y z) : cross (P1 x y z) (P4 x y z) (P0 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have e : cross (P1 x y z) (P4 x y z) (P0 x y z) = (z^2*x^3*y^3*(bq x y)^5) := by ug; ring
  rw [e]
  positivity

noncomputable def R_gr {x y z : ℝ} (h : LP x y z) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = z*x*y*(bq x y)^2) :
    RTiling (Phi (fr x y) '' Hgr x y z) (Mod h) (k * k) :=
  lad h (P1 x y z) (P4 x y z) (P0 x y z) k hk0 (det_gr h)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P1, P4, P0, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P1, P4, P0, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P1, P4, P0, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)

theorem det_lb {x y z : ℝ} (h : LP x y z) : cross (P0 x y z) (P5 x y z) (P2 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have e : cross (P0 x y z) (P5 x y z) (P2 x y z) = (z^2*x^5*y^5*(bq x y)^3) := by ug; ring
  rw [e]
  positivity

noncomputable def R_lb {x y z : ℝ} (h : LP x y z) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = z*x^2*y^2*bq x y) :
    RTiling (Phi (fr x y) '' Hlb x y z) (Mod h) (k * k) :=
  lad h (P0 x y z) (P5 x y z) (P2 x y z) k hk0 (det_lb h)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P0, P5, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P0, P5, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P0, P5, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)

theorem det_or {x y z : ℝ} (h : LP x y z) : cross (P6 x y z) (P3 x y z) (P2 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have e : cross (P6 x y z) (P3 x y z) (P2 x y z) = (y*z^2*x^13*(bq x y)) := by ug; ring
  rw [e]
  positivity

noncomputable def R_or {x y z : ℝ} (h : LP x y z) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = z*x^6) :
    RTiling (Phi (fr x y) '' Hor x y z) (Mod h) (k * k) :=
  lad h (P6 x y z) (P3 x y z) (P2 x y z) k hk0 (det_or h)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P6, P3, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P6, P3, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P6, P3, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)

theorem det_pk {x y z : ℝ} (h : LP x y z) : cross (P5 x y z) (P7 x y z) (P2 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have e : cross (P5 x y z) (P7 x y z) (P2 x y z) = (x*z^2*y^5*(bq x y)^5) := by ug; ring
  rw [e]
  positivity

noncomputable def R_pk {x y z : ℝ} (h : LP x y z) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = z*y^2*(bq x y)^2) :
    RTiling (Phi (fr x y) '' Hpk x y z) (Mod h) (k * k) :=
  lad h (P5 x y z) (P7 x y z) (P2 x y z) k hk0 (det_pk h)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P5, P7, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P5, P7, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P5, P7, P2, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)

theorem det_rd {x y z : ℝ} (h : LP x y z) : cross (P3 x y z) (P8 x y z) (P6 x y z) ≠ 0 := by
  obtain ⟨hx, hy, hz, hxy, hy2, hb, hq1, hq2, hq3, hq4, hq5, hV⟩ := h
  have e : cross (P3 x y z) (P8 x y z) (P6 x y z) = -(z^2*y^3*x^11*(bq x y)) := by ug; ring
  rw [e]
  exact neg_ne_zero.mpr (by positivity)

noncomputable def R_rd {x y z : ℝ} (h : LP x y z) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = z*x^5*y) :
    RTiling (Phi (fr x y) '' Hrd x y z) (Mod h) (k * k) :=
  lad h (P3 x y z) (P8 x y z) (P6 x y z) k hk0 (det_rd h)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P3, P8, P6, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P3, P8, P6, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)
    (by have h1 : x ≠ 0 := h.hx.ne'
        have h2 : y ≠ 0 := h.hy.ne'
        rw [hk]; simp only [fr, P3, P8, P6, bq, Ub, Vb, Vp, q1, q5]; field_simp; ring)


/-! ### the parallelogram `[0,U] × [0,V]`: two grids of bricks -/

theorem cong_swap {f : ℝ} (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickL f hf A B hA hB).Congruent (brickL f hf B A hB hA) := by
  have h0 : f ≠ 0 := f_ne hf
  refine ((brickL f hf A B hA hB).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Tri.relabel, brickL, triC_pts] <;>
    (refine dPhi' _ _ _ _ ?_; rw [sq_Phi' hf, sq_Phi' hf]; field_simp; ring)

/-- bricks `c × b` (width `c = xy` along the first axis, height `b`): `(k+1)(l+1)` cells, `2(k+1)(l+1)` tiles. -/
noncomputable def GA {x y z : ℝ} (h : LP x y z) (k l : ℕ) :
    RTiling (Phi (fr x y) '' Rect 0 (x * y * ((k : ℝ) + 1)) 0 (bq x y * ((l : ℝ) + 1))) (Mod h)
      (2 * (k + 1) * (l + 1)) :=
  grid (hfr h) (hcc h) (hbb h)
    (brick_rt (fr x y) (hfr h) _ _ (hcc h) (hbb h) (Mod h) (by unfold Mod; exact Tri.Congruent.refl _)
      (by unfold Mod; exact cong_U_cell (hfr h) _ _ (hcc h) (hbb h))) k l

/-- bricks `b × c`. -/
noncomputable def GB0 {x y z : ℝ} (h : LP x y z) (k l : ℕ) :
    RTiling (Phi (fr x y) '' Rect 0 (bq x y * ((k : ℝ) + 1)) 0 (x * y * ((l : ℝ) + 1))) (Mod h)
      (2 * (k + 1) * (l + 1)) :=
  grid (hfr h) (hbb h) (hcc h)
    (brick_rt (fr x y) (hfr h) _ _ (hbb h) (hcc h) (Mod h)
      (by unfold Mod; exact cong_swap (hfr h) _ _ (hbb h) (hcc h))
      (by unfold Mod; exact ((cong_U_cell (hfr h) _ _ (hbb h) (hcc h)).trans
        (cong_swap (hfr h) _ _ (hbb h) (hcc h))))) k l

/-- the bricks `b × c`, lifted by `b (lA+1)`. -/
noncomputable def GB {x y z : ℝ} (h : LP x y z) (k l lA : ℕ) :
    RTiling (Phi (fr x y) '' Rect 0 (bq x y * ((k : ℝ) + 1)) (bq x y * ((lA : ℝ) + 1))
      (x * y * ((l : ℝ) + 1) + bq x y * ((lA : ℝ) + 1))) (Mod h) (2 * (k + 1) * (l + 1)) :=
  shift_rect (GB0 h k l) 0 (bq x y * ((lA : ℝ) + 1)) (bq x y * ((k : ℝ) + 1))
    (x * y * ((l : ℝ) + 1) + bq x y * ((lA : ℝ) + 1)) (add_zero _).symm rfl

end Erdos634.Draft.LaczFamily
