/-
Draft/LayerE1Geom.lean -- frame geometry of the layer of the base-β target of the members `(1, f)` (paper: `prop:layer`).

Frame `Φ_F`, `F = d + 2` (`d ≥ 0`), scale `t` with `F ≤ 2t` (so `t` may be SMALLER than `F`); `A = F (F² − 1)`,
`B = 2F² − 1`, `C = 3F² − 1`, `L₀ = (F − 1)(F² − 1)`.  In this frame `T_t` is the triangle `(A t, 0)`, `(A t, C t)`,
`(0, B t)` (`WtoDeltaF.DS (A t) (B t) (C t)`), and `T_{t+1}` is filled by nine regions:

  `Y0 = T_t + (0, B)`,
  `Y1` = the rectangle `[A t, A t + A] × [B + L₀, H]`, `H = B (t + 1) + t F²` (two brick grids),
  `Y2` = the triangle `(A t + A, H + F²)`, `(A t + A, H)`, `(A t, H)` (the tile at scale `F`),
  and the six cap pieces `Z3, …, Z8` of `Draft.CollarE1Geom` at `τ = 0`, translated by `(A (t − F), 0)`.

Proved here: every region lies in `T_{t+1}` (`Yf_sub`) and any two have
disjoint interiors (`dY_all`, 36 pairs: the 15 pairs inside the cap are those of `CollarE1Geom`, carried by the
translation; the others are separated by the lines `x = A t`, `y = B + L₀`, `y = H`).  The bounds of the cap pieces
are read from `CollarE1Geom` at `τ = 0` (`xg_i`, `yl_i`, `Zi_sub`), so no polynomial certificate is regenerated.

The cap is D. Paliy's cap of six pieces ("A six-block cap for every primitive W and beta tile", unrefereed), and so are
the tilings at the scales `M ≥ f`.  The layout (containment, exact area, 36 separations, tile counts) was also checked
in exact rational arithmetic for 19 pairs `(F, t)` with `2 ≤ F ≤ 9`, including `t < F` and `2t = F`.
No sorry, no native_decide.
-/
import Erdos634.Draft.CollarE1Geom

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.LayerE1
open Erdos634.Draft.CollarE1
open Erdos634.Draft.WtoDeltaF (DS)

noncomputable section

/-! ## Translates in skew coordinates -/

/-- a point of the interior of a translate comes from a point of the interior -/
theorem interior_Sh_sub (v : ℝ × ℝ) (X : Set (ℝ × ℝ)) : ∀ p ∈ interior (Sh v X), p - v ∈ interior X := by
  intro p hp
  obtain ⟨U, hU, hUo, hpU⟩ := mem_interior.mp hp
  have hc : Continuous fun q : ℝ × ℝ => q + v := continuous_id.add continuous_const
  refine mem_interior.mpr ⟨(fun q : ℝ × ℝ => q + v) ⁻¹' U, ?_, hUo.preimage hc, ?_⟩
  · intro q hq
    have hq' : q + v ∈ U := hq
    have h1 : q + v ∈ Sh v X := hU hq'
    have h2 : q + v - v ∈ X := h1
    simpa using h2
  · show p - v + v ∈ U
    simpa using hpU

/-- translation keeps interiors disjoint -/
theorem disj_Sh (v : ℝ × ℝ) {X Y : Set (ℝ × ℝ)} (h : Disjoint (interior X) (interior Y)) :
    Disjoint (interior (Sh v X)) (interior (Sh v Y)) := by
  rw [Set.disjoint_left] at h
  rw [Set.disjoint_left]
  intro p hpX hpY
  exact h (interior_Sh_sub v X p hpX) (interior_Sh_sub v Y p hpY)

/-! ## The constants and the regions -/

/-- `C = 3F² − 1` -/
def cC (d : ℝ) : ℝ := 3 * (d + 2) ^ 2 - 1
/-- the number of rows of height `F` of the layer at scale `t`: `x_a = (2t − F) F + 1` -/
def xa (d t : ℝ) : ℝ := (2 * t - (d + 2)) * (d + 2) + 1
/-- `H = B (t + 1) + t F²`: the height at which the line `x = A t` meets the upper side of `T_{t+1}` -/
def cH (d t : ℝ) : ℝ := cB d * (t + 1) + t * (d + 2) ^ 2
/-- the translation that carries the cap of the collar at `τ = 0` (scale `F`) to the cap of the layer at scale `t` -/
def vsh (d t : ℝ) : ℝ × ℝ := (cA d * (t - (d + 2)), 0)

/-- the three corners of the tile at scale `F` on top of the layer -/
def uA (d t : ℝ) : ℝ × ℝ := (cA d * t + cA d, cH d t + (d + 2) ^ 2)
def uB (d t : ℝ) : ℝ × ℝ := (cA d * t + cA d, cH d t)
def uC (d t : ℝ) : ℝ × ℝ := (cA d * t, cH d t)

/-- `T_t`, translated by `(0, B)` -/
def Y0 (d t : ℝ) : Set (ℝ × ℝ) := Sh (0, cB d) (DS (cA d * t) (cB d * t) (cC d * t))
/-- the rectangle of the two brick grids -/
def Y1 (d t : ℝ) : Set (ℝ × ℝ) := Rect (cA d * t) (cA d * t + cA d) (cB d + cL d) (cH d t)
/-- the tile at scale `F` -/
def Y2 (d t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {uA d t, uB d t, uC d t}
/-- the target `T_{t+1}` -/
def YT (d t : ℝ) : Set (ℝ × ℝ) := DS (cA d * (t + 1)) (cB d * (t + 1)) (cC d * (t + 1))
/-- the nine regions, indexed -/
def Yf (d t : ℝ) : Fin 9 → Set (ℝ × ℝ) := fun i => match i with
  | ⟨0, _⟩ => Y0 d t
  | ⟨1, _⟩ => Y1 d t
  | ⟨2, _⟩ => Y2 d t
  | ⟨3, _⟩ => Sh (vsh d t) (Z3 d 0)
  | ⟨4, _⟩ => Sh (vsh d t) (Z4 d 0)
  | ⟨5, _⟩ => Sh (vsh d t) (Z5 d 0)
  | ⟨6, _⟩ => Sh (vsh d t) (Z6 d 0)
  | ⟨7, _⟩ => Sh (vsh d t) (Z7 d 0)
  | ⟨8, _⟩ => Sh (vsh d t) (Z8 d 0)
  | ⟨k + 9, h⟩ => absurd h (by omega)

/-! ## Elementary facts -/

theorem cC_pos {d : ℝ} (hd : 0 ≤ d) : 0 < cC d := by
  have e : cC d = 3 * d ^ 2 + 12 * d + 11 := by simp only [cC]; ring
  rw [e]; positivity

theorem cB_lt_cC {d : ℝ} (hd : 0 ≤ d) : cB d < cC d := by
  have e : cC d - cB d = (d + 2) ^ 2 := by simp only [cC, cB]; ring
  have h : (0 : ℝ) < (d + 2) ^ 2 := by positivity
  linarith

theorem tpos {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : 0 < t := by linarith

/-- `x_a ≥ 1`: this is where `F ≤ 2t` is used -/
theorem xa_pos {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : 0 < xa d t := by
  have h : 0 ≤ (2 * t - (d + 2)) * (d + 2) := mul_nonneg (by linarith) (by linarith)
  have e : xa d t = (2 * t - (d + 2)) * (d + 2) + 1 := rfl
  linarith

/-- the heights: `(B + L₀) + x_a F + (t + 1)(F² − 1) = H` -/
theorem cH_ge' {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : cB d + cL d + (d + 2) * xa d t ≤ cH d t := by
  have e : cH d t - (cB d + cL d + (d + 2) * xa d t) = (t + 1) * ((d + 2) ^ 2 - 1) := by
    simp only [cH, cB, cL, xa]; ring
  have h : 0 ≤ (t + 1) * ((d + 2) ^ 2 - 1) := mul_nonneg (by linarith) (by nlinarith [sq_nonneg d])
  linarith

theorem cH_ge {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : cB d + cL d ≤ cH d t := by
  have h1 := cH_ge' hd h2t
  have h2 : 0 ≤ (d + 2) * xa d t := mul_nonneg (by linarith) (xa_pos hd h2t).le
  linarith

/-! ## Membership in `T_{t+1}` -/

theorem mem_YT {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) (p : ℝ × ℝ) (h1 : p.1 ≤ cA d * (t + 1))
    (h2 : cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2)
    (h3 : cA d * (p.2 - cB d * (t + 1)) ≤ (d + 2) ^ 2 * p.1) : p ∈ YT d t := by
  show p.1 ≤ cA d * (t + 1) ∧
    cA d * (t + 1) * (cB d * (t + 1)) ≤ cB d * (t + 1) * p.1 + cA d * (t + 1) * p.2 ∧
    cA d * (t + 1) * (p.2 - cB d * (t + 1)) ≤ (cC d * (t + 1) - cB d * (t + 1)) * p.1
  have ht1 : (0 : ℝ) ≤ t + 1 := by linarith
  have e : (cC d * (t + 1) - cB d * (t + 1)) * p.1 = (t + 1) * ((d + 2) ^ 2 * p.1) := by
    simp only [cC, cB]; ring
  have k2 := mul_le_mul_of_nonneg_left h2 ht1
  have k3 := mul_le_mul_of_nonneg_left h3 ht1
  refine ⟨h1, by linarith, by linarith⟩

/-- the third inequality of `T_{t+1}` for a point with `x ≥ A t`, `y ≤ H` -/
theorem iii_of {d : ℝ} (hd : 0 ≤ d) (t : ℝ) (p : ℝ × ℝ) (hx : cA d * t ≤ p.1) (hy : p.2 ≤ cH d t) :
    cA d * (p.2 - cB d * (t + 1)) ≤ (d + 2) ^ 2 * p.1 := by
  have hA := cA_pos hd (le_refl (0 : ℝ))
  have e : cH d t = cB d * (t + 1) + t * (d + 2) ^ 2 := rfl
  have e1 : p.2 - cB d * (t + 1) ≤ t * (d + 2) ^ 2 := by linarith
  have k1 := mul_le_mul_of_nonneg_left e1 hA.le
  have k2 := mul_le_mul_of_nonneg_left hx (sq_nonneg (d + 2))
  linarith

/-! ## `Y0`, `Y1`, `Y2` -/

theorem Y0_mem (d t : ℝ) (p : ℝ × ℝ) (hp : p ∈ Y0 d t) :
    p.1 ≤ cA d * t ∧ cA d * t * (cB d * t) ≤ cB d * t * p.1 + cA d * t * (p.2 - cB d) ∧
      cA d * t * (p.2 - cB d - cB d * t) ≤ (cC d * t - cB d * t) * p.1 := by
  have hp' : (p - (0, cB d)).1 ≤ cA d * t ∧
      cA d * t * (cB d * t) ≤ cB d * t * (p - (0, cB d)).1 + cA d * t * (p - (0, cB d)).2 ∧
      cA d * t * ((p - (0, cB d)).2 - cB d * t) ≤ (cC d * t - cB d * t) * (p - (0, cB d)).1 := hp
  simpa only [Prod.fst_sub, Prod.snd_sub, sub_zero] using hp'

theorem Y0_sub {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : Y0 d t ⊆ YT d t := by
  intro p hp
  obtain ⟨ha, hb, hc⟩ := Y0_mem d t p hp
  have hA := cA_pos hd (le_refl (0 : ℝ))
  have ht := tpos hd h2t
  have ec : (cC d * t - cB d * t) * p.1 = t * ((d + 2) ^ 2 * p.1) := by simp only [cC, cB]; ring
  have kb : t * (cA d * cB d * (t + 1)) ≤ t * (cB d * p.1 + cA d * p.2) := by linarith
  have kc : t * (cA d * (p.2 - cB d * (t + 1))) ≤ t * ((d + 2) ^ 2 * p.1) := by linarith
  exact mem_YT hd h2t p (by linarith) (le_of_mul_le_mul_left kb ht) (le_of_mul_le_mul_left kc ht)

theorem Y1_sub {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : Y1 d t ⊆ YT d t := by
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hA := cA_pos hd (le_refl (0 : ℝ))
  have hB := cB_pos hd (le_refl (0 : ℝ))
  have hL := cL_pos hd (le_refl (0 : ℝ))
  have k1 := mul_le_mul_of_nonneg_left h1 hB.le
  have k3 := mul_le_mul_of_nonneg_left h3 hA.le
  have k5 := mul_pos hA hL
  exact mem_YT hd h2t p (by linarith) (by linarith) (iii_of hd t p h1 h4)

theorem x_le_Y0 (d t : ℝ) : ∀ p ∈ Y0 d t, p.1 ≤ cA d * t := fun p hp => (Y0_mem d t p hp).1
theorem x_ge_Y1 (d t : ℝ) : ∀ p ∈ Y1 d t, cA d * t ≤ p.1 := fun p hp => hp.1
theorem y_ge_Y1 (d t : ℝ) : ∀ p ∈ Y1 d t, cB d + cL d ≤ p.2 := fun p hp => hp.2.2.1
theorem y_le_Y1 (d t : ℝ) : ∀ p ∈ Y1 d t, p.2 ≤ cH d t := fun p hp => hp.2.2.2

theorem x_ge_Y2 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Y2 d t, cA d * t ≤ p.1 := by
  have hA := cA_pos hd (le_refl (0 : ℝ))
  exact Erdos634.Draft.S2L.tri_fst_ge (A := uA d t) (B := uB d t) (C := uC d t) (cA d * t)
    (by show cA d * t ≤ cA d * t + cA d; linarith) (by show cA d * t ≤ cA d * t + cA d; linarith)
    (by show cA d * t ≤ cA d * t; exact le_refl _)

theorem y_ge_Y2 (d t : ℝ) : ∀ p ∈ Y2 d t, cH d t ≤ p.2 :=
  Erdos634.Draft.S2L.tri_snd_ge (A := uA d t) (B := uB d t) (C := uC d t) (cH d t)
    (by show cH d t ≤ cH d t + (d + 2) ^ 2; linarith [sq_nonneg (d + 2)])
    (by show cH d t ≤ cH d t; exact le_refl _) (by show cH d t ≤ cH d t; exact le_refl _)

theorem y_ge_Y2' {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : ∀ p ∈ Y2 d t, cB d + cL d ≤ p.2 :=
  fun p hp => le_trans (cH_ge hd h2t) (y_ge_Y2 d t p hp)

theorem Y2_sub {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : Y2 d t ⊆ YT d t := by
  have hA := cA_pos hd (le_refl (0 : ℝ))
  have hB := cB_pos hd (le_refl (0 : ℝ))
  have ht := tpos hd h2t
  have hF2 : (0 : ℝ) ≤ (d + 2) ^ 2 := sq_nonneg (d + 2)
  have pAB : 0 < cA d * cB d := mul_pos hA hB
  have pAF : 0 ≤ cA d * (d + 2) ^ 2 := mul_nonneg hA.le hF2
  have pABt : 0 ≤ cA d * cB d * t := mul_nonneg pAB.le ht.le
  have pAtF : 0 ≤ cA d * (t * (d + 2) ^ 2) := mul_nonneg hA.le (mul_nonneg ht.le hF2)
  -- the three inequalities of `T_{t+1}` at the three corners (`cH` written out)
  have h1 : ∀ p ∈ Y2 d t, p.1 ≤ cA d * (t + 1) :=
    Erdos634.Draft.S2L.tri_fst_le (A := uA d t) (B := uB d t) (C := uC d t) (cA d * (t + 1))
      (by show cA d * t + cA d ≤ cA d * (t + 1); linarith)
      (by show cA d * t + cA d ≤ cA d * (t + 1); linarith)
      (by show cA d * t ≤ cA d * (t + 1); linarith)
  have h2 : ∀ p ∈ Y2 d t, cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 :=
    Erdos634.Draft.S2L.tri_ge (A := uA d t) (B := uB d t) (C := uC d t) (cB d) (cA d) (cA d * cB d * (t + 1))
      (by show cA d * cB d * (t + 1)
            ≤ cB d * (cA d * t + cA d) + cA d * (cB d * (t + 1) + t * (d + 2) ^ 2 + (d + 2) ^ 2)
          linarith)
      (by show cA d * cB d * (t + 1) ≤ cB d * (cA d * t + cA d) + cA d * (cB d * (t + 1) + t * (d + 2) ^ 2)
          linarith)
      (by show cA d * cB d * (t + 1) ≤ cB d * (cA d * t) + cA d * (cB d * (t + 1) + t * (d + 2) ^ 2)
          linarith)
  have h3 : ∀ p ∈ Y2 d t, (-((d + 2) ^ 2)) * p.1 + cA d * p.2 ≤ cA d * (cB d * (t + 1)) :=
    Erdos634.Draft.S2L.tri_le (A := uA d t) (B := uB d t) (C := uC d t) (-((d + 2) ^ 2)) (cA d)
      (cA d * (cB d * (t + 1)))
      (by show (-((d + 2) ^ 2)) * (cA d * t + cA d) + cA d * (cB d * (t + 1) + t * (d + 2) ^ 2 + (d + 2) ^ 2)
            ≤ cA d * (cB d * (t + 1))
          linarith)
      (by show (-((d + 2) ^ 2)) * (cA d * t + cA d) + cA d * (cB d * (t + 1) + t * (d + 2) ^ 2)
            ≤ cA d * (cB d * (t + 1))
          linarith)
      (by show (-((d + 2) ^ 2)) * (cA d * t) + cA d * (cB d * (t + 1) + t * (d + 2) ^ 2)
            ≤ cA d * (cB d * (t + 1))
          linarith)
  intro p hp
  have k3 := h3 p hp
  exact mem_YT hd h2t p (h1 p hp) (h2 p hp) (by linarith)

/-! ## The cap: the six pieces of `CollarE1Geom` at `τ = 0`, translated -/

/-- the four bounds of a translated cap piece, from the bounds of `CollarE1Geom` at `τ = 0` -/
theorem cap_bounds {d : ℝ} (hd : 0 ≤ d) (t : ℝ) {Z : Set (ℝ × ℝ)}
    (hx : ∀ q ∈ Z, cA d * ct d 0 ≤ q.1) (hy : ∀ q ∈ Z, q.2 ≤ cB d + cL d) (hs : Z ⊆ ZT d 0) :
    ∀ p ∈ Sh (vsh d t) Z, cA d * t ≤ p.1 ∧ p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧
      cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 := by
  intro p hp
  have hq : p - vsh d t ∈ Z := hp
  have e1 : (p - vsh d t).1 = p.1 - cA d * (t - (d + 2)) := rfl
  have e2 : (p - vsh d t).2 = p.2 - 0 := rfl
  have ec : ct d 0 = d + 2 + 0 := rfl
  have h1 := hx _ hq
  have h2 := hy _ hq
  have h3 : (p - vsh d t).1 ≤ cA d * (ct d 0 + 1) ∧ (p - vsh d t).2 ≤ cB d * (ct d 0 + 1) ∧
      cA d * (ct d 0 + 1) * (cB d * (ct d 0 + 1))
        ≤ cB d * (ct d 0 + 1) * (p - vsh d t).1 + cA d * (ct d 0 + 1) * (p - vsh d t).2 := hs hq
  obtain ⟨h31, -, h33⟩ := h3
  rw [e1, ec] at h1 h31
  rw [e2] at h2
  rw [e1, e2, ec] at h33
  have h3pos : (0 : ℝ) < d + 2 + 0 + 1 := by linarith
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have key : (d + 2 + 0 + 1) * (cA d * cB d * (t + 1)) ≤ (d + 2 + 0 + 1) * (cB d * p.1 + cA d * p.2) := by
    linarith
  exact le_of_mul_le_mul_left key h3pos

theorem cap_sub {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) {Z : Set (ℝ × ℝ)}
    (h : ∀ p ∈ Sh (vsh d t) Z, cA d * t ≤ p.1 ∧ p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧
      cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2) : Sh (vsh d t) Z ⊆ YT d t := by
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := h p hp
  exact mem_YT hd h2t p h2 h4 (iii_of hd t p h1 (le_trans h3 (cH_ge hd h2t)))

theorem cap3 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z3 d 0), cA d * t ≤ p.1 ∧
    p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧ cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 :=
  cap_bounds hd t (xg_3 hd (le_refl (0 : ℝ))) (yl_3 hd (le_refl (0 : ℝ))) (Z3_sub hd (le_refl (0 : ℝ)))
theorem xgY3 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z3 d 0), cA d * t ≤ p.1 :=
  fun p hp => (cap3 hd t p hp).1
theorem ylY3 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z3 d 0), p.2 ≤ cB d + cL d :=
  fun p hp => (cap3 hd t p hp).2.2.1
theorem cap4 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z4 d 0), cA d * t ≤ p.1 ∧
    p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧ cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 :=
  cap_bounds hd t (xg_4 hd (le_refl (0 : ℝ))) (yl_4 hd (le_refl (0 : ℝ))) (Z4_sub hd (le_refl (0 : ℝ)))
theorem xgY4 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z4 d 0), cA d * t ≤ p.1 :=
  fun p hp => (cap4 hd t p hp).1
theorem ylY4 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z4 d 0), p.2 ≤ cB d + cL d :=
  fun p hp => (cap4 hd t p hp).2.2.1
theorem cap5 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z5 d 0), cA d * t ≤ p.1 ∧
    p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧ cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 :=
  cap_bounds hd t (xg_5 hd (le_refl (0 : ℝ))) (yl_5 hd (le_refl (0 : ℝ))) (Z5_sub hd (le_refl (0 : ℝ)))
theorem xgY5 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z5 d 0), cA d * t ≤ p.1 :=
  fun p hp => (cap5 hd t p hp).1
theorem ylY5 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z5 d 0), p.2 ≤ cB d + cL d :=
  fun p hp => (cap5 hd t p hp).2.2.1
theorem cap6 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z6 d 0), cA d * t ≤ p.1 ∧
    p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧ cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 :=
  cap_bounds hd t (xg_6 hd (le_refl (0 : ℝ))) (yl_6 hd (le_refl (0 : ℝ))) (Z6_sub hd (le_refl (0 : ℝ)))
theorem xgY6 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z6 d 0), cA d * t ≤ p.1 :=
  fun p hp => (cap6 hd t p hp).1
theorem ylY6 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z6 d 0), p.2 ≤ cB d + cL d :=
  fun p hp => (cap6 hd t p hp).2.2.1
theorem cap7 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z7 d 0), cA d * t ≤ p.1 ∧
    p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧ cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 :=
  cap_bounds hd t (xg_7 hd (le_refl (0 : ℝ))) (yl_7 hd (le_refl (0 : ℝ))) (Z7_sub hd (le_refl (0 : ℝ)))
theorem xgY7 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z7 d 0), cA d * t ≤ p.1 :=
  fun p hp => (cap7 hd t p hp).1
theorem ylY7 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z7 d 0), p.2 ≤ cB d + cL d :=
  fun p hp => (cap7 hd t p hp).2.2.1
theorem cap8 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z8 d 0), cA d * t ≤ p.1 ∧
    p.1 ≤ cA d * (t + 1) ∧ p.2 ≤ cB d + cL d ∧ cA d * cB d * (t + 1) ≤ cB d * p.1 + cA d * p.2 :=
  cap_bounds hd t (xg_8 hd (le_refl (0 : ℝ))) (yl_8 hd (le_refl (0 : ℝ))) (Z8_sub hd (le_refl (0 : ℝ)))
theorem xgY8 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z8 d 0), cA d * t ≤ p.1 :=
  fun p hp => (cap8 hd t p hp).1
theorem ylY8 {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : ∀ p ∈ Sh (vsh d t) (Z8 d 0), p.2 ≤ cB d + cL d :=
  fun p hp => (cap8 hd t p hp).2.2.1

/-! ## The nine regions lie in `T_{t+1}` -/
theorem Yf_sub {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) : ∀ a : Fin 9, Yf d t a ⊆ YT d t :=
  fun a => match a with
  | ⟨0, _⟩ => Y0_sub hd h2t
  | ⟨1, _⟩ => Y1_sub hd h2t
  | ⟨2, _⟩ => Y2_sub hd h2t
  | ⟨3, _⟩ => cap_sub hd h2t (cap3 hd t)
  | ⟨4, _⟩ => cap_sub hd h2t (cap4 hd t)
  | ⟨5, _⟩ => cap_sub hd h2t (cap5 hd t)
  | ⟨6, _⟩ => cap_sub hd h2t (cap6 hd t)
  | ⟨7, _⟩ => cap_sub hd h2t (cap7 hd t)
  | ⟨8, _⟩ => cap_sub hd h2t (cap8 hd t)
  | ⟨k + 9, h⟩ => absurd h (by omega)

/-! ## Pairwise disjoint interiors (36 pairs) -/
theorem dY_0_1 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Y1 d t)) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (x_ge_Y1 d t)
theorem dY_0_2 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Y2 d t)) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (x_ge_Y2 hd t)
theorem dY_0_3 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Sh (vsh d t) (Z3 d 0))) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (xgY3 hd t)
theorem dY_0_4 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Sh (vsh d t) (Z4 d 0))) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (xgY4 hd t)
theorem dY_0_5 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Sh (vsh d t) (Z5 d 0))) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (xgY5 hd t)
theorem dY_0_6 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Sh (vsh d t) (Z6 d 0))) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (xgY6 hd t)
theorem dY_0_7 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Sh (vsh d t) (Z7 d 0))) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (xgY7 hd t)
theorem dY_0_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y0 d t)) (interior (Sh (vsh d t) (Z8 d 0))) :=
  interior_disj_fst (cA d * t) (x_le_Y0 d t) (xgY8 hd t)
theorem dY_1_2 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y1 d t)) (interior (Y2 d t)) :=
  interior_disj_snd (cH d t) (y_le_Y1 d t) (y_ge_Y2 d t)
theorem dY_1_3 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y1 d t)) (interior (Sh (vsh d t) (Z3 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY3 hd t) (y_ge_Y1 d t)).symm
theorem dY_1_4 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y1 d t)) (interior (Sh (vsh d t) (Z4 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY4 hd t) (y_ge_Y1 d t)).symm
theorem dY_1_5 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y1 d t)) (interior (Sh (vsh d t) (Z5 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY5 hd t) (y_ge_Y1 d t)).symm
theorem dY_1_6 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y1 d t)) (interior (Sh (vsh d t) (Z6 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY6 hd t) (y_ge_Y1 d t)).symm
theorem dY_1_7 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y1 d t)) (interior (Sh (vsh d t) (Z7 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY7 hd t) (y_ge_Y1 d t)).symm
theorem dY_1_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y1 d t)) (interior (Sh (vsh d t) (Z8 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY8 hd t) (y_ge_Y1 d t)).symm
theorem dY_2_3 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y2 d t)) (interior (Sh (vsh d t) (Z3 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY3 hd t) (y_ge_Y2' hd h2t)).symm
theorem dY_2_4 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y2 d t)) (interior (Sh (vsh d t) (Z4 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY4 hd t) (y_ge_Y2' hd h2t)).symm
theorem dY_2_5 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y2 d t)) (interior (Sh (vsh d t) (Z5 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY5 hd t) (y_ge_Y2' hd h2t)).symm
theorem dY_2_6 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y2 d t)) (interior (Sh (vsh d t) (Z6 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY6 hd t) (y_ge_Y2' hd h2t)).symm
theorem dY_2_7 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y2 d t)) (interior (Sh (vsh d t) (Z7 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY7 hd t) (y_ge_Y2' hd h2t)).symm
theorem dY_2_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Y2 d t)) (interior (Sh (vsh d t) (Z8 d 0))) :=
  (interior_disj_snd (cB d + cL d) (ylY8 hd t) (y_ge_Y2' hd h2t)).symm
theorem dY_3_4 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z3 d 0))) (interior (Sh (vsh d t) (Z4 d 0))) :=
  disj_Sh (vsh d t) (dZ_3_4 hd (le_refl (0 : ℝ)))
theorem dY_3_5 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z3 d 0))) (interior (Sh (vsh d t) (Z5 d 0))) :=
  disj_Sh (vsh d t) (dZ_3_5 hd (le_refl (0 : ℝ)))
theorem dY_3_6 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z3 d 0))) (interior (Sh (vsh d t) (Z6 d 0))) :=
  disj_Sh (vsh d t) (dZ_3_6 hd (le_refl (0 : ℝ)))
theorem dY_3_7 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z3 d 0))) (interior (Sh (vsh d t) (Z7 d 0))) :=
  disj_Sh (vsh d t) (dZ_3_7 hd (le_refl (0 : ℝ)))
theorem dY_3_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z3 d 0))) (interior (Sh (vsh d t) (Z8 d 0))) :=
  disj_Sh (vsh d t) (dZ_3_8 hd (le_refl (0 : ℝ)))
theorem dY_4_5 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z4 d 0))) (interior (Sh (vsh d t) (Z5 d 0))) :=
  disj_Sh (vsh d t) (dZ_4_5 hd (le_refl (0 : ℝ)))
theorem dY_4_6 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z4 d 0))) (interior (Sh (vsh d t) (Z6 d 0))) :=
  disj_Sh (vsh d t) (dZ_4_6 hd (le_refl (0 : ℝ)))
theorem dY_4_7 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z4 d 0))) (interior (Sh (vsh d t) (Z7 d 0))) :=
  disj_Sh (vsh d t) (dZ_4_7 hd (le_refl (0 : ℝ)))
theorem dY_4_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z4 d 0))) (interior (Sh (vsh d t) (Z8 d 0))) :=
  disj_Sh (vsh d t) (dZ_4_8 hd (le_refl (0 : ℝ)))
theorem dY_5_6 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z5 d 0))) (interior (Sh (vsh d t) (Z6 d 0))) :=
  disj_Sh (vsh d t) (dZ_5_6 hd (le_refl (0 : ℝ)))
theorem dY_5_7 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z5 d 0))) (interior (Sh (vsh d t) (Z7 d 0))) :=
  disj_Sh (vsh d t) (dZ_5_7 hd (le_refl (0 : ℝ)))
theorem dY_5_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z5 d 0))) (interior (Sh (vsh d t) (Z8 d 0))) :=
  disj_Sh (vsh d t) (dZ_5_8 hd (le_refl (0 : ℝ)))
theorem dY_6_7 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z6 d 0))) (interior (Sh (vsh d t) (Z7 d 0))) :=
  disj_Sh (vsh d t) (dZ_6_7 hd (le_refl (0 : ℝ)))
theorem dY_6_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z6 d 0))) (interior (Sh (vsh d t) (Z8 d 0))) :=
  disj_Sh (vsh d t) (dZ_6_8 hd (le_refl (0 : ℝ)))
theorem dY_7_8 {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    Disjoint (interior (Sh (vsh d t) (Z7 d 0))) (interior (Sh (vsh d t) (Z8 d 0))) :=
  disj_Sh (vsh d t) (dZ_7_8 hd (le_refl (0 : ℝ)))

/-! ## The nine regions as a family -/
theorem dY_all {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) :
    ∀ a b : Fin 9, a ≠ b → Disjoint (interior (Yf d t a)) (interior (Yf d t b)) := by
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => dY_0_1 hd h2t
  | ⟨0, _⟩, ⟨2, _⟩ => dY_0_2 hd h2t
  | ⟨0, _⟩, ⟨3, _⟩ => dY_0_3 hd h2t
  | ⟨0, _⟩, ⟨4, _⟩ => dY_0_4 hd h2t
  | ⟨0, _⟩, ⟨5, _⟩ => dY_0_5 hd h2t
  | ⟨0, _⟩, ⟨6, _⟩ => dY_0_6 hd h2t
  | ⟨0, _⟩, ⟨7, _⟩ => dY_0_7 hd h2t
  | ⟨0, _⟩, ⟨8, _⟩ => dY_0_8 hd h2t
  | ⟨1, _⟩, ⟨0, _⟩ => (dY_0_1 hd h2t).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => dY_1_2 hd h2t
  | ⟨1, _⟩, ⟨3, _⟩ => dY_1_3 hd h2t
  | ⟨1, _⟩, ⟨4, _⟩ => dY_1_4 hd h2t
  | ⟨1, _⟩, ⟨5, _⟩ => dY_1_5 hd h2t
  | ⟨1, _⟩, ⟨6, _⟩ => dY_1_6 hd h2t
  | ⟨1, _⟩, ⟨7, _⟩ => dY_1_7 hd h2t
  | ⟨1, _⟩, ⟨8, _⟩ => dY_1_8 hd h2t
  | ⟨2, _⟩, ⟨0, _⟩ => (dY_0_2 hd h2t).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (dY_1_2 hd h2t).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => dY_2_3 hd h2t
  | ⟨2, _⟩, ⟨4, _⟩ => dY_2_4 hd h2t
  | ⟨2, _⟩, ⟨5, _⟩ => dY_2_5 hd h2t
  | ⟨2, _⟩, ⟨6, _⟩ => dY_2_6 hd h2t
  | ⟨2, _⟩, ⟨7, _⟩ => dY_2_7 hd h2t
  | ⟨2, _⟩, ⟨8, _⟩ => dY_2_8 hd h2t
  | ⟨3, _⟩, ⟨0, _⟩ => (dY_0_3 hd h2t).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (dY_1_3 hd h2t).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (dY_2_3 hd h2t).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => dY_3_4 hd h2t
  | ⟨3, _⟩, ⟨5, _⟩ => dY_3_5 hd h2t
  | ⟨3, _⟩, ⟨6, _⟩ => dY_3_6 hd h2t
  | ⟨3, _⟩, ⟨7, _⟩ => dY_3_7 hd h2t
  | ⟨3, _⟩, ⟨8, _⟩ => dY_3_8 hd h2t
  | ⟨4, _⟩, ⟨0, _⟩ => (dY_0_4 hd h2t).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (dY_1_4 hd h2t).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (dY_2_4 hd h2t).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (dY_3_4 hd h2t).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨4, _⟩, ⟨5, _⟩ => dY_4_5 hd h2t
  | ⟨4, _⟩, ⟨6, _⟩ => dY_4_6 hd h2t
  | ⟨4, _⟩, ⟨7, _⟩ => dY_4_7 hd h2t
  | ⟨4, _⟩, ⟨8, _⟩ => dY_4_8 hd h2t
  | ⟨5, _⟩, ⟨0, _⟩ => (dY_0_5 hd h2t).symm
  | ⟨5, _⟩, ⟨1, _⟩ => (dY_1_5 hd h2t).symm
  | ⟨5, _⟩, ⟨2, _⟩ => (dY_2_5 hd h2t).symm
  | ⟨5, _⟩, ⟨3, _⟩ => (dY_3_5 hd h2t).symm
  | ⟨5, _⟩, ⟨4, _⟩ => (dY_4_5 hd h2t).symm
  | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hab
  | ⟨5, _⟩, ⟨6, _⟩ => dY_5_6 hd h2t
  | ⟨5, _⟩, ⟨7, _⟩ => dY_5_7 hd h2t
  | ⟨5, _⟩, ⟨8, _⟩ => dY_5_8 hd h2t
  | ⟨6, _⟩, ⟨0, _⟩ => (dY_0_6 hd h2t).symm
  | ⟨6, _⟩, ⟨1, _⟩ => (dY_1_6 hd h2t).symm
  | ⟨6, _⟩, ⟨2, _⟩ => (dY_2_6 hd h2t).symm
  | ⟨6, _⟩, ⟨3, _⟩ => (dY_3_6 hd h2t).symm
  | ⟨6, _⟩, ⟨4, _⟩ => (dY_4_6 hd h2t).symm
  | ⟨6, _⟩, ⟨5, _⟩ => (dY_5_6 hd h2t).symm
  | ⟨6, _⟩, ⟨6, _⟩ => absurd rfl hab
  | ⟨6, _⟩, ⟨7, _⟩ => dY_6_7 hd h2t
  | ⟨6, _⟩, ⟨8, _⟩ => dY_6_8 hd h2t
  | ⟨7, _⟩, ⟨0, _⟩ => (dY_0_7 hd h2t).symm
  | ⟨7, _⟩, ⟨1, _⟩ => (dY_1_7 hd h2t).symm
  | ⟨7, _⟩, ⟨2, _⟩ => (dY_2_7 hd h2t).symm
  | ⟨7, _⟩, ⟨3, _⟩ => (dY_3_7 hd h2t).symm
  | ⟨7, _⟩, ⟨4, _⟩ => (dY_4_7 hd h2t).symm
  | ⟨7, _⟩, ⟨5, _⟩ => (dY_5_7 hd h2t).symm
  | ⟨7, _⟩, ⟨6, _⟩ => (dY_6_7 hd h2t).symm
  | ⟨7, _⟩, ⟨7, _⟩ => absurd rfl hab
  | ⟨7, _⟩, ⟨8, _⟩ => dY_7_8 hd h2t
  | ⟨8, _⟩, ⟨0, _⟩ => (dY_0_8 hd h2t).symm
  | ⟨8, _⟩, ⟨1, _⟩ => (dY_1_8 hd h2t).symm
  | ⟨8, _⟩, ⟨2, _⟩ => (dY_2_8 hd h2t).symm
  | ⟨8, _⟩, ⟨3, _⟩ => (dY_3_8 hd h2t).symm
  | ⟨8, _⟩, ⟨4, _⟩ => (dY_4_8 hd h2t).symm
  | ⟨8, _⟩, ⟨5, _⟩ => (dY_5_8 hd h2t).symm
  | ⟨8, _⟩, ⟨6, _⟩ => (dY_6_8 hd h2t).symm
  | ⟨8, _⟩, ⟨7, _⟩ => (dY_7_8 hd h2t).symm
  | ⟨8, _⟩, ⟨8, _⟩ => absurd rfl hab
  | ⟨k + 9, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 9, h⟩ => absurd h (by omega)

end

end Erdos634.Draft.LayerE1

#print axioms Erdos634.Draft.LayerE1.Yf_sub
#print axioms Erdos634.Draft.LayerE1.dY_all
