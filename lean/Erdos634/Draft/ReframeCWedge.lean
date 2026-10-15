/-
Draft/ReframeCWedge.lean  In `AllThreshold`.

Geometry for PIECE C3 (`prop:reframe` (c)): the apex triangle `T'` of `T_f(1,f)` above the chord at the height of `T_1`, and its
cut along a cevian from the apex.

Frame `Φ_F`.  A *wedge triangle* `Tw F hF v0 c ya yb` is the triangle with vertices `(0, v0)`, `(c, ya)`, `(c, yb)`
(`c > 0`, `ya < yb`): the apex `(0, v0)` and the two ends of a vertical chord at the abscissa `c`.

    wedgeSet, hull_wedge     -- its hull is `{x ≤ c, 0 ≤ ℓ_ya, ℓ_yb ≤ 0}` with `ℓ_y p = c (p.2 − v0) − (y − v0) p.1`
    Tw, carrier_Tw           -- the triangle and its carrier `Φ_F '' wedgeSet`
    frame_wedge              -- with `t + 1 = F`: the wedge `(0, B₀ F), (A₀ t, B₀), (A₀ t, B₀ F + F² t)` is
                             --   `DS (A₀ F) (B₀ F) (C₀ F) ∩ {x ≤ A₀ t}` (the upper part of `T_F` above the chord)
    wedge_lower, wedge_upper -- cutting the wedge `(ya, yb)` along the cevian to `(c, yX)`, `ya < yX < yb`: the two parts are
                             --   the wedges `(ya, yX)` and `(yX, yb)`
    cut_pieces               -- a congruent dissection of the wedge `(ya, yb)` in which the open cevian
                             --   `(Φ(0, v0), Φ(c, yX))` meets no tile interior gives congruent dissections of both parts
                             --   (the same model), through `ChordCut.straddlers_eq_empty_of_wall`,
                             --   `restrict_below`, `restrict_above`
    sidesW_upper, sidesW_lower
                             -- the parts that are copies of `W_t(1,F)`: sides `t F³`, `t F (F²−1)`, `t (2F²−1)`

Here `vA F = (2F²−1) F`, `cX F t = F (F²−1) t`, `yB F = 2F²−1`, `yC F t = (2F²−1) F + F² t`, `yK F t = vA F − t (F²−1)`
(the ordinate of the foot of the cevian towards `Q'` on the chord), and `t + 1 = F` (`t = f − 1`, `F = f`).
Every statement is an equation or an implication between explicit objects; `cut_pieces` is an implication (hypothesis:
a dissection of the wedge with the cevian uncrossed), which `ChordCutWitness` shows has instances of the same kind.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.ChordCut
import Erdos634.Draft.SignedDecompE1
import Erdos634.Draft.LayerE1Chord

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.ReframeCWedge
open Erdos634.Draft.WFrameF
open Erdos634.Draft.WBrickF (triC triC_pts carrier_triC PhiL)
open Erdos634.Draft.WtoDeltaF (DS)
open Erdos634.Draft.SignedDecompE1 (tri_le' tri_ge' mem3 hasSides_triC hasSides_eq dist_Phi_eq)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi skewX_ne_zero)
open Erdos634.ChordTraceReal (straddlers)

/-! ## The second skew coordinate and the cutting forms -/

/-- `q ↦ q₁ (2F) / sD F`: the second skew coordinate of the frame `Φ_F` (`= (Psi F q).2`) -/
noncomputable def skewY (F : ℝ) : Plane →ₗ[ℝ] ℝ where
  toFun q := q 1 * (2 * F) / sD F
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem skewY_Phi {F : ℝ} (hF : 1 < F) (p : ℝ × ℝ) : skewY F (Phi F p) = p.2 := by
  calc skewY F (Phi F p) = (Psi F (Phi F p)).2 := rfl
    _ = p.2 := by rw [Psi_Phi hF p]

/-- the linear form `q ↦ c · y(q) − m · x(q)` in the skew coordinates -/
noncomputable def cutFun (F c m : ℝ) : Plane →ₗ[ℝ] ℝ := c • skewY F - m • skewX F

theorem cutFun_Phi {F : ℝ} (hF : 1 < F) (c m : ℝ) (p : ℝ × ℝ) :
    cutFun F c m (Phi F p) = c * p.2 - m * p.1 := by
  simp only [cutFun, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, skewY_Phi hF, skewX_Phi hF]

/-- the plane form of the cutting: `Φ_F '' (S ∩ {P}) = Φ_F '' S ∩ {Q}` when `Q ∘ Φ_F = P` -/
theorem image_inter_iff {F : ℝ} (S : Set (ℝ × ℝ)) (P : ℝ × ℝ → Prop) (Q : Plane → Prop)
    (h : ∀ p, Q (Phi F p) ↔ P p) : Phi F '' (S ∩ {p | P p}) = Phi F '' S ∩ {q | Q q} := by
  ext y
  constructor
  · rintro ⟨p, ⟨hp, hpc⟩, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, (h p).mpr hpc⟩
  · rintro ⟨⟨p, hp, rfl⟩, hy⟩
    exact ⟨p, ⟨hp, (h p).mp hy⟩, rfl⟩

/-! ## The wedge -/

/-- the wedge at the apex `(0, v0)` over the vertical chord `x = c`, `ya ≤ y ≤ yb` -/
def wedgeSet (v0 c ya yb : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ c ∧ 0 ≤ c * (p.2 - v0) - (ya - v0) * p.1 ∧ c * (p.2 - v0) - (yb - v0) * p.1 ≤ 0}

theorem hull_wedge {v0 c ya yb : ℝ} (hc : 0 < c) (hab : ya < yb) :
    convexHull ℝ ({((0 : ℝ), v0), (c, ya), (c, yb)} : Set (ℝ × ℝ)) = wedgeSet v0 c ya yb := by
  have hd := sub_pos.2 hab
  have hcd := mul_pos hc hd
  apply Set.Subset.antisymm
  · intro p hp
    have h1 := tri_le' 1 0 c (by linarith) (by linarith) (by linarith) p hp
    have h2 := tri_ge' (-(ya - v0)) c (c * v0) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    have h3 := tri_le' (-(yb - v0)) c (c * v0) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    exact ⟨by linarith, by nlinarith, by nlinarith⟩
  · rintro p ⟨h1, h2, h3⟩
    exact mem3 (c * (yb - ya)) ((c - p.1) * (yb - ya)) ((yb - v0) * p.1 - c * (p.2 - v0))
      (c * (p.2 - v0) - (ya - v0) * p.1)
      (mul_pos hc hd) (mul_nonneg (by linarith) hd.le) (by linarith) h2 (by ring) p (by ring) (by ring)

/-- the wedge triangle -/
noncomputable def Tw (F : ℝ) (hF : 1 < F) (v0 c ya yb : ℝ) (hc : 0 < c) (hab : ya < yb) :
    Erdos634.Geometry.Tri :=
  triC F hF (0, v0) (c, ya) (c, yb) (by
    show (c - 0) * (yb - v0) - (c - 0) * (ya - v0) ≠ 0
    intro h
    nlinarith [mul_pos hc (sub_pos.2 hab)])

theorem carrier_Tw (F : ℝ) (hF : 1 < F) (v0 c ya yb : ℝ) (hc : 0 < c) (hab : ya < yb) :
    (Tw F hF v0 c ya yb hc hab).carrier = Phi F '' wedgeSet v0 c ya yb := by
  unfold Tw
  rw [carrier_triC, hull_wedge hc hab]

/-- a point of the wedge has `x ≥ 0` -/
theorem wedge_fst_nonneg {v0 c ya yb : ℝ} (hab : ya < yb) {p : ℝ × ℝ} (hp : p ∈ wedgeSet v0 c ya yb) :
    0 ≤ p.1 := by
  obtain ⟨_, h2, h3⟩ := hp
  by_contra hn
  have hn' : p.1 < 0 := not_le.mp hn
  have := mul_neg_of_pos_of_neg (sub_pos.2 hab) hn'
  nlinarith

/-- cutting the wedge along the cevian to `(c, yX)`: the lower part -/
theorem wedge_lower {v0 c y1 y2 yX : ℝ} (h1X : y1 < yX) (hX2 : yX < y2) :
    wedgeSet v0 c y1 yX =
      wedgeSet v0 c y1 y2 ∩ {p | c * (p.2 - v0) - (yX - v0) * p.1 ≤ 0} := by
  ext p
  simp only [wedgeSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hx, h1, hX⟩
    have hx0 : 0 ≤ p.1 := by
      by_contra hn
      have := mul_neg_of_pos_of_neg (sub_pos.2 h1X) (not_le.mp hn)
      nlinarith
    have := mul_nonneg (sub_pos.2 hX2).le hx0
    exact ⟨⟨hx, h1, by nlinarith⟩, hX⟩
  · rintro ⟨⟨hx, h1, _⟩, hX⟩
    exact ⟨hx, h1, hX⟩

/-- cutting the wedge along the cevian to `(c, yX)`: the upper part -/
theorem wedge_upper {v0 c y1 y2 yX : ℝ} (h1X : y1 < yX) (hX2 : yX < y2) :
    wedgeSet v0 c yX y2 =
      wedgeSet v0 c y1 y2 ∩ {p | 0 ≤ c * (p.2 - v0) - (yX - v0) * p.1} := by
  ext p
  simp only [wedgeSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hx, hX, h2⟩
    have hx0 : 0 ≤ p.1 := by
      by_contra hn
      have := mul_neg_of_pos_of_neg (sub_pos.2 hX2) (not_le.mp hn)
      nlinarith
    have := mul_nonneg (sub_pos.2 h1X).le hx0
    exact ⟨⟨hx, by nlinarith, h2⟩, hX⟩
  · rintro ⟨⟨hx, _, h2⟩, hX⟩
    exact ⟨hx, hX, h2⟩

/-- a point of the wedge on the line through the apex and `(c, yX)` lies on the segment -/
theorem wedge_line_mem_segment {v0 c y1 y2 yX : ℝ} (hc : 0 < c) (h12 : y1 < y2) {p : ℝ × ℝ}
    (hp : p ∈ wedgeSet v0 c y1 y2) (hl : c * (p.2 - v0) - (yX - v0) * p.1 = 0) :
    p ∈ segment ℝ ((0 : ℝ), v0) (c, yX) := by
  have hx0 := wedge_fst_nonneg h12 hp
  have hxc : p.1 ≤ c := hp.1
  have hl0 : 0 ≤ p.1 / c := div_nonneg hx0 hc.le
  have hl1 : p.1 / c ≤ 1 := by rw [div_le_one hc]; exact hxc
  refine ⟨1 - p.1 / c, p.1 / c, by linarith, hl0, by ring, ?_⟩
  have hcne : c ≠ 0 := hc.ne'
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    first | (field_simp; ring1) | field_simp
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    first | (field_simp; linarith) | field_simp

/-! ## The cut -/

/-- **A congruent dissection of the wedge `(ya, yb)` in which the open cevian `(Φ(0, v0), Φ(c, yX))` meets no tile
interior gives congruent dissections (same model) of the two wedges `(ya, yX)` and `(yX, yb)`.** -/
theorem cut_pieces {N : ℕ} {F : ℝ} (hF : 1 < F) {v0 c y1 y2 yX : ℝ} (hc : 0 < c) (h1X : y1 < yX)
    (hX2 : yX < y2) (D' : CongruentDissection N)
    (hD' : D'.target = Tw F hF v0 c y1 y2 hc (h1X.trans hX2))
    (hwall : ∀ y ∈ openSegment ℝ (Phi F (0, v0)) (Phi F (c, yX)), ∀ i,
      y ∉ interior (D'.tile i).carrier) :
    (∃ (N1 : ℕ) (D1 : CongruentDissection N1), D1.target = Tw F hF v0 c y1 yX hc h1X ∧
        D1.model = D'.model) ∧
      (∃ (N2 : ℕ) (D2 : CongruentDissection N2), D2.target = Tw F hF v0 c yX y2 hc hX2 ∧
        D2.model = D'.model) := by
  have h12 := h1X.trans hX2
  have hg : cutFun F c (yX - v0) ≠ 0 := by
    intro h
    have h1 := cutFun_Phi hF c (yX - v0) (0, 1)
    rw [h] at h1
    simp at h1
    linarith
  have hline : ∀ y ∈ D'.target.carrier, cutFun F c (yX - v0) y = c * v0 →
      y ∈ segment ℝ (Phi F (0, v0)) (Phi F (c, yX)) := by
    intro y hy hyl
    rw [hD', carrier_Tw] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [cutFun_Phi hF] at hyl
    have hl : c * (p.2 - v0) - (yX - v0) * p.1 = 0 := by linarith
    have hseg := wedge_line_mem_segment hc h12 hp hl
    have himg := image_segment ℝ (PhiL F).toAffineMap ((0 : ℝ), v0) (c, yX)
    have hmem : Phi F p ∈ (PhiL F).toAffineMap '' segment ℝ ((0 : ℝ), v0) (c, yX) := ⟨p, hseg, rfl⟩
    rw [himg] at hmem
    exact hmem
  have h0 : straddlers D'.toDissection (cutFun F c (yX - v0)) (c * v0) = ∅ :=
    Erdos634.Draft.ChordCut.straddlers_eq_empty_of_wall D'.toDissection _ _
      (P := Phi F (0, v0)) (Q := Phi F (c, yX)) hline hwall
  have hlow : (Tw F hF v0 c y1 yX hc h1X).carrier =
      D'.target.carrier ∩ {q | cutFun F c (yX - v0) q ≤ c * v0} := by
    rw [hD', carrier_Tw, carrier_Tw, wedge_lower h1X hX2]
    exact image_inter_iff _ (fun p => c * (p.2 - v0) - (yX - v0) * p.1 ≤ 0)
      (fun q => cutFun F c (yX - v0) q ≤ c * v0)
      (fun p => by dsimp only; rw [cutFun_Phi hF]; constructor <;> intro h <;> linarith)
  have hup : (Tw F hF v0 c yX y2 hc hX2).carrier =
      D'.target.carrier ∩ {q | c * v0 ≤ cutFun F c (yX - v0) q} := by
    rw [hD', carrier_Tw, carrier_Tw, wedge_upper h1X hX2]
    exact image_inter_iff _ (fun p => 0 ≤ c * (p.2 - v0) - (yX - v0) * p.1)
      (fun q => c * v0 ≤ cutFun F c (yX - v0) q)
      (fun p => by dsimp only; rw [cutFun_Phi hF]; constructor <;> intro h <;> linarith)
  exact ⟨Erdos634.Draft.ChordCut.restrict_below D' _ hg _ h0 _ hlow,
    Erdos634.Draft.ChordCut.restrict_above D' _ hg _ h0 _ hup⟩

/-! ## The apex triangle of `T_F` in the wedge form -/

/-- the apex ordinate `B₀ F` -/
def vA (F : ℝ) : ℝ := (2 * F ^ 2 - 1) * F
/-- the abscissa of the chord: `A₀ t`, `A₀ = F (F² − 1)` -/
def cX (F t : ℝ) : ℝ := F * (F ^ 2 - 1) * t
/-- the lower end of the chord: `B₀` -/
def yB (F : ℝ) : ℝ := 2 * F ^ 2 - 1
/-- the upper end of the chord: `B₀ F + F² t` -/
def yC (F t : ℝ) : ℝ := (2 * F ^ 2 - 1) * F + F ^ 2 * t
/-- the foot on the chord of the cevian towards `Q'`: `B₀ F − t (F² − 1)` -/
def yK (F t : ℝ) : ℝ := (2 * F ^ 2 - 1) * F - t * (F ^ 2 - 1)

theorem nonneg_iff_of_pos {c a b : ℝ} (hc : 0 < c) (h : a = c * b) : 0 ≤ a ↔ 0 ≤ b := by
  rw [h]
  exact mul_nonneg_iff_of_pos_left hc

/-- **The upper part of `T_F` above the chord at the height of `T_1`, as a wedge.**  With `t + 1 = F`. -/
theorem frame_wedge (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    wedgeSet (vA F) (cX F t) (yB F) (yC F t) =
      DS (F * (F ^ 2 - 1) * F) ((2 * F ^ 2 - 1) * F) ((3 * F ^ 2 - 1) * F) ∩
        {p | p.1 ≤ F * (F ^ 2 - 1) * t} := by
  obtain rfl : F = t + 1 := htF.symm
  have hF0 : 0 < t + 1 := by linarith
  have hA : 0 < (t + 1) * ((t + 1) ^ 2 - 1) := mul_pos hF0 (by nlinarith)
  ext p
  simp only [wedgeSet, vA, cX, yB, yC, DS, Set.mem_setOf_eq, Set.mem_inter_iff]
  have idw2 : (t + 1) * ((t + 1) ^ 2 - 1) * t * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))
        - (2 * (t + 1) ^ 2 - 1 - (2 * (t + 1) ^ 2 - 1) * (t + 1)) * p.1
      = t * ((2 * (t + 1) ^ 2 - 1) * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))) := by
    ring
  have idw3 : (t + 1) * ((t + 1) ^ 2 - 1) * t * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))
        - ((2 * (t + 1) ^ 2 - 1) * (t + 1) + (t + 1) ^ 2 * t - (2 * (t + 1) ^ 2 - 1) * (t + 1)) * p.1
      = -(t * ((t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1)))) := by
    ring
  have idD2 : (2 * (t + 1) ^ 2 - 1) * (t + 1) * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * (t + 1) * p.2
        - (t + 1) * ((t + 1) ^ 2 - 1) * (t + 1) * ((2 * (t + 1) ^ 2 - 1) * (t + 1))
      = (t + 1) * ((2 * (t + 1) ^ 2 - 1) * p.1
        + (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))) := by
    ring
  have idD3 : ((3 * (t + 1) ^ 2 - 1) * (t + 1) - (2 * (t + 1) ^ 2 - 1) * (t + 1)) * p.1
        - (t + 1) * ((t + 1) ^ 2 - 1) * (t + 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))
      = (t + 1) * ((t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))) := by
    ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hE1 : 0 ≤ (2 * (t + 1) ^ 2 - 1) * p.1
        + (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1)) :=
      (nonneg_iff_of_pos ht idw2).mp (by linarith [h2])
    have hE2 : 0 ≤ (t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1)) := by
      have h : 0 ≤ t * ((t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))) := by
        linarith [idw3, h3]
      exact (mul_nonneg_iff_of_pos_left ht).mp h
    have g2 := mul_nonneg hF0.le hE1
    have g3 := mul_nonneg hF0.le hE2
    refine ⟨⟨?_, by linarith [g2, idD2], by linarith [g3, idD3]⟩, h1⟩
    nlinarith [hA]
  · rintro ⟨⟨_, h2, h3⟩, h1⟩
    have hE1 : 0 ≤ (2 * (t + 1) ^ 2 - 1) * p.1
        + (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1)) :=
      (nonneg_iff_of_pos hF0 idD2).mp (by linarith [h2])
    have hE2 : 0 ≤ (t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1)) :=
      (nonneg_iff_of_pos hF0 idD3).mp (by linarith [h3])
    have g2 := mul_nonneg ht.le hE1
    have g3 := mul_nonneg ht.le hE2
    exact ⟨h1, by linarith [g2, idw2], by linarith [g3, idw3]⟩

/-- the ordinates on the chord are in the order `yB < yK < yC` and `yB < vA < yC` (`F = t + 1 > 1`) -/
theorem ordinates (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    yB F < yK F t ∧ yK F t < yC F t ∧ yB F < vA F ∧ vA F < yC F t := by
  obtain rfl : F = t + 1 := htF.symm
  simp only [yB, yK, yC, vA]
  have h2 := mul_pos ht ht
  have h3 := mul_pos ht h2
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-! ## Side lengths of the wedge triangles -/

theorem d_vert {F : ℝ} (hF : 1 < F) (c ya yb : ℝ) (h : ya ≤ yb) :
    dist (Phi F (c, ya)) (Phi F (c, yb)) = yb - ya := by
  refine dist_Phi_eq F hF _ _ _ (sub_nonneg.2 h) ?_
  show (c - c) ^ 2 + (ya - yb) ^ 2 + (c - c) * (ya - yb) / F = (yb - ya) ^ 2
  ring

theorem dAB (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    dist (Phi F (0, vA F)) (Phi F (cX F t, yB F)) = t * F ^ 3 := by
  have hFp : 0 < F := by linarith
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF _ _ _ (mul_pos ht (pow_pos hFp 3)).le ?_
  obtain rfl : F = t + 1 := htF.symm
  simp only [vA, cX, yB]
  first | ring1 | (field_simp; ring1) | field_simp

theorem dAC (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    dist (Phi F (0, vA F)) (Phi F (cX F t, yC F t)) = t * F ^ 3 := by
  have hFp : 0 < F := by linarith
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF _ _ _ (mul_pos ht (pow_pos hFp 3)).le ?_
  obtain rfl : F = t + 1 := htF.symm
  simp only [vA, cX, yC]
  first | ring1 | (field_simp; ring1) | field_simp

theorem dAK (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    dist (Phi F (0, vA F)) (Phi F (cX F t, yK F t)) = t * (F * (F ^ 2 - 1)) := by
  have hFp : 0 < F := by linarith
  have hF0 : F ≠ 0 := hFp.ne'
  have hA : 0 < F ^ 2 - 1 := by nlinarith
  refine dist_Phi_eq F hF _ _ _ (mul_pos ht (mul_pos hFp hA)).le ?_
  obtain rfl : F = t + 1 := htF.symm
  simp only [vA, cX, yK]
  first | ring1 | (field_simp; ring1) | field_simp

theorem dAM (F t : ℝ) (hF : 1 < F) (ht : 0 < t) :
    dist (Phi F (0, vA F)) (Phi F (cX F t, vA F)) = t * (F * (F ^ 2 - 1)) := by
  have hFp : 0 < F := by linarith
  have hF0 : F ≠ 0 := hFp.ne'
  have hA : 0 < F ^ 2 - 1 := by nlinarith
  refine dist_Phi_eq F hF _ _ _ (mul_pos ht (mul_pos hFp hA)).le ?_
  simp only [cX]
  first | ring1 | (field_simp; ring1) | field_simp

/-- **The part above the cevian towards `Q'`** is a copy of `W_t(1,F)`: sides `t F³`, `t F (F²−1)`, `t (2F²−1)`. -/
theorem sidesW_upper (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) (hc : 0 < cX F t)
    (hab : yK F t < yC F t) :
    HasSides (Tw F hF (vA F) (cX F t) (yK F t) (yC F t) hc hab) (t * F ^ 3) (t * (F * (F ^ 2 - 1)))
      (t * (2 * F ^ 2 - 1)) := by
  have base : HasSides (Tw F hF (vA F) (cX F t) (yK F t) (yC F t) hc hab)
      (yC F t - yK F t) (t * F ^ 3) (t * (F * (F ^ 2 - 1))) :=
    hasSides_triC F hF (0, vA F) (cX F t, yK F t) (cX F t, yC F t) _ _ _ _
      (d_vert hF _ _ _ hab.le) ((dist_comm _ _).trans (dAC F t hF ht htF)) (dAK F t hF ht htF)
  refine hasSides_eq (hasSides_rot base) rfl rfl ?_
  simp only [yC, yK]
  ring

/-- **The part below the cevian towards `Q`** (the horizontal one) is a copy of `W_t(1,F)`. -/
theorem sidesW_lower (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) (hc : 0 < cX F t)
    (hab : yB F < vA F) :
    HasSides (Tw F hF (vA F) (cX F t) (yB F) (vA F) hc hab) (t * F ^ 3) (t * (F * (F ^ 2 - 1)))
      (t * (2 * F ^ 2 - 1)) := by
  have base : HasSides (Tw F hF (vA F) (cX F t) (yB F) (vA F) hc hab)
      (vA F - yB F) (t * (F * (F ^ 2 - 1))) (t * F ^ 3) :=
    hasSides_triC F hF (0, vA F) (cX F t, yB F) (cX F t, vA F) _ _ _ _
      (d_vert hF _ _ _ hab.le) ((dist_comm _ _).trans (dAM F t hF ht)) (dAB F t hF ht htF)
  have e : vA F - yB F = t * (2 * F ^ 2 - 1) := by
    obtain rfl : F = t + 1 := htF.symm
    simp only [vA, yB]
    ring
  exact hasSides_eq (hasSides_swap (hasSides_rot base)) rfl rfl e

end Erdos634.Draft.ReframeCWedge

#print axioms Erdos634.Draft.ReframeCWedge.hull_wedge
#print axioms Erdos634.Draft.ReframeCWedge.frame_wedge
#print axioms Erdos634.Draft.ReframeCWedge.cut_pieces
#print axioms Erdos634.Draft.ReframeCWedge.sidesW_upper
#print axioms Erdos634.Draft.ReframeCWedge.sidesW_lower
