/-
Draft/LayerGGeom.lean  In `AllThreshold`.

Frame geometry of the LAYER of height `e H₁` of the base-β target `T_M(e, f)` of every member (paper: `prop:layerall` (b)).
Frame `Φ_F`, `F = f / e` (the frame of `CollarG`: `u = e`, `g = f − e`, `f = u + g`), `a = u f`, `b = f² − u²`, `c = f²`,
`A = f b`, `B = u (2f² − u²)`, `C = u (3f² − u²)`, `L₀ = u g b`.  In this frame `T_M` is the triangle `(A M, 0)`, `(A M, C M)`, `(0, B M)`
(`WtoDeltaF.DS (A M) (B M) (C M)`), the base is the line `x = A M`, and for `M` with `x_a = 2 M f − (f² + 2 u f − u²) ≥ 0`
(that is `2 f (M − u) ≥ b`) the layer `T_M ∩ {x ≥ A (M − u)}` is filled by ten regions (the frame is the mirror image of the picture of the
paper: the tile at scale `e f` is at the end `C` of the base, high `y`, and the cap at the end `B`, low `y`; the order of the pieces along the
base from the scaled tile is that of the paper):

  `LY0 = T_{M−u} + (0, B u)`     the part of `T_M` left of the chord `x = X₀ = A (M − u)`,
  `LS1`                          the triangle `(A M, C M)`, `(A M, Y_a)`, `(X₀, Y_a)` (the tile at scale `e f`),
  `LRa = [X₀, A M] × [Y_b, Y_a]` `e f` columns times `x_a` rows of cells `b × a` (paper: the `x_a` columns of `e f` parallelograms),
  `LRb = [X₀, A M] × [Y₁, Y_b]` `b` columns times `u M` rows of cells `a × b` (paper: the `e M` columns of `b` parallelograms),
  and the six cap pieces `Z3, …, Z8` of `Draft.CollarGGeom` at `σ = 1`, translated by `(A (M − f − 1), 0)`,

with `Y₁ = B u + L₀`, `Y_b = Y₁ + u M b`, `Y_a = Y_b + x_a a = C (M − u) + B u` (the height at which the chord meets the upper side of `T_M`).
Proved here: every region lies in `T_M` (`Lf_sub`), `LY0` lies in `x ≤ X₀` and the nine others in `x ≥ X₀`, and any two regions have disjoint
interiors (`dL_all`, 45 pairs: the 15 pairs inside the cap are those of `CollarGGeom` at `σ = 1`, carried by the translation; the others are
separated by the lines `x = X₀`, `y = Y_a`, `y = Y_b`, `y = Y₁`).  The bounds of the cap pieces are read from `CollarGGeom` (`xg_i`, `yl_i`,
`Zi_sub`), so no polynomial certificate is regenerated: the only inequality specific to the layer is `Y₁ ≤ Y_a`, i.e. `L₀ ≤ C (M − u)`, which
follows from `x_a ≥ 0`.  The 45 pair lemmas and their dispatch `dL_all` are boilerplate generated from the table of
separating lines above.

The cap is D. Paliy's cap of six pieces ("A six-block cap for every primitive W and beta tile", unrefereed),
written in one skew frame in `CollarGGeom`.  The layout was also checked in exact rational arithmetic on all coprime `e < f ≤ 9`, every scale
`M` with `x_a ≥ 0` up to `M = 2 f`: congruence of each piece, containment in `T_M`, side of the chord, 45 separations, areas = tile counts,
total = `P M²`.
No sorry, no native_decide.
-/
import Erdos634.Draft.CollarG

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.LayerG
open Erdos634.Draft.CollarG (ca cb cA cB cC cL ct ZT Z3 Z4 Z5 Z6 Z7 Z8 Pg hapos hbpos cApos cBpos hPpos
  xg_3 xg_4 xg_5 xg_6 xg_7 xg_8 yl_3 yl_4 yl_5 yl_6 yl_7 yl_8 Z3_sub Z4_sub Z5_sub Z6_sub Z7_sub Z8_sub
  dZ_3_4 dZ_3_5 dZ_3_6 dZ_3_7 dZ_3_8 dZ_4_5 dZ_4_6 dZ_4_7 dZ_4_8 dZ_5_6 dZ_5_7 dZ_5_8 dZ_6_7 dZ_6_8 dZ_7_8)
open Erdos634.Draft.WtoDeltaF (DS)
open Erdos634.Draft.S2L (hull_le hull_ge)

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

/-- `x_a = 2 M f − (f² + 2 u f − u²)`: the number of rows of the first kind (`f = u + g`, `u = e`) -/
def lxa (u g M : ℝ) : ℝ := 2 * M * (u + g) - ((u + g) ^ 2 + 2 * u * (u + g) - u ^ 2)
/-- the chord `x = X₀ = A (M − u)`: the base of the translate of `T_{M−u}` -/
def lX0 (u g M : ℝ) : ℝ := cA u g * (M - u)
/-- the base of `T_M`: `x = A M` -/
def lX1 (u g M : ℝ) : ℝ := cA u g * M
/-- the top of the cap: `Y₁ = B u + L₀` -/
def lY1 (u g : ℝ) : ℝ := cB u g * u + cL u g
/-- the top of `LRb`: `Y_b = Y₁ + u M b` -/
def lYb (u g M : ℝ) : ℝ := lY1 u g + u * M * cb u g
/-- the top of `LRa` and the foot of the scaled tile: `Y_a = Y_b + x_a a` -/
def lYa (u g M : ℝ) : ℝ := lYb u g M + lxa u g M * ca u g
/-- the corner `C M` of `T_M` -/
def lYt (u g M : ℝ) : ℝ := cC u g * M
/-- the translation that carries the cap of the collar at `σ = 1` (scale `g + 1`, target `W_{f+1}`) to the cap of the layer at scale `M` -/
def lvsh (u g M : ℝ) : ℝ × ℝ := (cA u g * (M - (u + g) - 1), 0)

def lSa (u g M : ℝ) : ℝ × ℝ := (lX1 u g M, lYt u g M)
def lSb (u g M : ℝ) : ℝ × ℝ := (lX1 u g M, lYa u g M)
def lSc (u g M : ℝ) : ℝ × ℝ := (lX0 u g M, lYa u g M)

/-- `T_{M−u}`, translated by `(0, B u)` -/
def LY0 (u g M : ℝ) : Set (ℝ × ℝ) :=
  Sh (0, cB u g * u) (DS (cA u g * (M - u)) (cB u g * (M - u)) (cC u g * (M - u)))
/-- the tile at scale `e f` -/
def LS1 (u g M : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {lSa u g M, lSb u g M, lSc u g M}
/-- `e f` columns times `x_a` rows of cells `b × a` -/
def LRa (u g M : ℝ) : Set (ℝ × ℝ) :=
  Pg (lX0 u g M, lYb u g M) ((u * (u + g)) • (cb u g, (0 : ℝ))) ((lxa u g M) • ((0 : ℝ), ca u g))
/-- `b` columns times `u M` rows of cells `a × b` -/
def LRb (u g M : ℝ) : Set (ℝ × ℝ) :=
  Pg (lX0 u g M, lY1 u g) ((cb u g) • (ca u g, (0 : ℝ))) ((u * M) • ((0 : ℝ), cb u g))
/-- the target `T_M` -/
def LT (u g M : ℝ) : Set (ℝ × ℝ) := DS (cA u g * M) (cB u g * M) (cC u g * M)
/-- the ten regions, indexed -/
def Lf (u g M : ℝ) : Fin 10 → Set (ℝ × ℝ) := fun i => match i with
  | ⟨0, _⟩ => LY0 u g M
  | ⟨1, _⟩ => LS1 u g M
  | ⟨2, _⟩ => LRa u g M
  | ⟨3, _⟩ => LRb u g M
  | ⟨4, _⟩ => Sh (lvsh u g M) (Z3 u g 1)
  | ⟨5, _⟩ => Sh (lvsh u g M) (Z4 u g 1)
  | ⟨6, _⟩ => Sh (lvsh u g M) (Z5 u g 1)
  | ⟨7, _⟩ => Sh (lvsh u g M) (Z6 u g 1)
  | ⟨8, _⟩ => Sh (lvsh u g M) (Z7 u g 1)
  | ⟨9, _⟩ => Sh (lvsh u g M) (Z8 u g 1)
  | ⟨k + 10, h⟩ => absurd h (by omega)

section real
variable {u g M : ℝ}

/-! ## Elementary facts -/

/-- `x_a ≥ 0` forces `M > u` (`2 f (M − u) = x_a + b`) -/
theorem lM_gt (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : u < M := by
  have h : 2 * (u + g) * (M - u) = lxa u g M + g * (2 * u + g) := by simp only [lxa]; ring
  have h1 : 0 < g * (2 * u + g) := by positivity
  have h3 : 0 < 2 * (u + g) := by positivity
  have h2 : 0 < 2 * (u + g) * (M - u) := by linarith
  have := (mul_pos_iff_of_pos_left h3).mp h2
  linarith

theorem lM_pos (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : 0 < M := by
  have := lM_gt hu hg hx; linarith

theorem lcL_pos (hu : 0 < u) (hg : 0 < g) : 0 < cL u g := by
  have e : cL u g = u * g * cb u g := rfl
  rw [e]; exact mul_pos (mul_pos hu hg) (hbpos hu hg)

theorem lcC_pos (hu : 0 < u) (hg : 0 < g) : 0 < cC u g := by
  have := hPpos hu hg
  simp only [cC]; exact mul_pos hu this

theorem lcB_lt_cC (hu : 0 < u) (hg : 0 < g) : cB u g < cC u g := by
  have e : cC u g - cB u g = u * (u + g) ^ 2 := by simp only [cC, cB]; ring
  have : 0 < u * (u + g) ^ 2 := by positivity
  linarith

theorem lYa_eq : lYa u g M = cC u g * (M - u) + cB u g * u := by
  simp only [lYa, lYb, lY1, lxa, cL, cB, cC, ca, cb]; ring

theorem lYt_sub : lYt u g M - lYa u g M = ca u g * ca u g := by
  rw [lYa_eq]; simp only [lYt, cC, cB, ca]; ring

theorem lX0_le_lX1 (hu : 0 < u) (hg : 0 < g) : lX0 u g M ≤ lX1 u g M := by
  have := mul_pos (cApos hu hg) hu
  simp only [lX0, lX1]; nlinarith

theorem lY1_le_lYb (hu : 0 < u) (hg : 0 < g) (hM : 0 ≤ M) : lY1 u g ≤ lYb u g M := by
  have : 0 ≤ u * M * cb u g := mul_nonneg (mul_nonneg hu.le hM) (hbpos hu hg).le
  simp only [lYb]; linarith

theorem lYb_le_lYa (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : lYb u g M ≤ lYa u g M := by
  have := mul_nonneg hx (hapos hu hg).le
  simp only [lYa]; linarith

theorem lYa_le_lYt : lYa u g M ≤ lYt u g M := by
  have := lYt_sub (u := u) (g := g) (M := M)
  nlinarith [mul_self_nonneg (ca u g)]

theorem lY1_le_lYa (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : lY1 u g ≤ lYa u g M :=
  le_trans (lY1_le_lYb hu hg (lM_pos hu hg hx).le) (lYb_le_lYa hu hg hx)

/-! ## Membership in `T_M` -/

theorem mem_LT (hM : 0 ≤ M) (p : ℝ × ℝ) (h1 : p.1 ≤ cA u g * M)
    (h2 : cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2)
    (h3 : cA u g * (p.2 - cB u g * M) ≤ (cC u g - cB u g) * p.1) : p ∈ LT u g M := by
  show p.1 ≤ cA u g * M ∧ cA u g * M * (cB u g * M) ≤ cB u g * M * p.1 + cA u g * M * p.2 ∧
    cA u g * M * (p.2 - cB u g * M) ≤ (cC u g * M - cB u g * M) * p.1
  have k2 := mul_le_mul_of_nonneg_left h2 hM
  have k3 := mul_le_mul_of_nonneg_left h3 hM
  exact ⟨h1, by linarith, by linarith⟩

/-- the third inequality of `T_M` for a point right of the chord and below the height `Y_a` -/
theorem third_of (hu : 0 < u) (hg : 0 < g) (p : ℝ × ℝ) (hx0 : lX0 u g M ≤ p.1) (hy : p.2 ≤ lYa u g M) :
    cA u g * (p.2 - cB u g * M) ≤ (cC u g - cB u g) * p.1 := by
  have hA := cApos hu hg
  have hCB := lcB_lt_cC hu hg
  have e := lYa_eq (u := u) (g := g) (M := M)
  have k1 := mul_le_mul_of_nonneg_left hy hA.le
  have k2 := mul_le_mul_of_nonneg_left hx0 (sub_nonneg.mpr hCB.le)
  simp only [lX0] at k2
  rw [e] at k1
  nlinarith [k1, k2]

/-- the second inequality of `T_M` for a point right of the chord and above the height `Y₁` -/
theorem lower_of (hu : 0 < u) (hg : 0 < g) (p : ℝ × ℝ) (hx0 : lX0 u g M ≤ p.1) (hy : lY1 u g ≤ p.2) :
    cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 := by
  have hA := cApos hu hg
  have hB := cBpos hu hg
  have hL := lcL_pos hu hg
  have k1 := mul_le_mul_of_nonneg_left hx0 hB.le
  have k2 := mul_le_mul_of_nonneg_left hy hA.le
  simp only [lX0, lY1] at k1 k2
  nlinarith [mul_pos hA hL]

/-- a set in the box `[X₀, A M] × [Y₁, Y_a]` lies in `T_M` -/
theorem box_sub (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) {S : Set (ℝ × ℝ)}
    (h : ∀ p ∈ S, lX0 u g M ≤ p.1 ∧ p.1 ≤ lX1 u g M ∧ lY1 u g ≤ p.2 ∧ p.2 ≤ lYa u g M) : S ⊆ LT u g M := by
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := h p hp
  exact mem_LT (lM_pos hu hg hx).le p h2 (lower_of hu hg p h1 h3) (third_of hu hg p h1 h4)

/-! ## `LY0` -/

theorem LY0_mem (p : ℝ × ℝ) (hp : p ∈ LY0 u g M) :
    p.1 ≤ cA u g * (M - u) ∧
    cA u g * (M - u) * (cB u g * (M - u)) ≤ cB u g * (M - u) * p.1 + cA u g * (M - u) * (p.2 - cB u g * u) ∧
    cA u g * (M - u) * (p.2 - cB u g * u - cB u g * (M - u)) ≤ (cC u g * (M - u) - cB u g * (M - u)) * p.1 := by
  have hp' : (p - (0, cB u g * u)).1 ≤ cA u g * (M - u) ∧
      cA u g * (M - u) * (cB u g * (M - u)) ≤ cB u g * (M - u) * (p - (0, cB u g * u)).1
        + cA u g * (M - u) * (p - (0, cB u g * u)).2 ∧
      cA u g * (M - u) * ((p - (0, cB u g * u)).2 - cB u g * (M - u))
        ≤ (cC u g * (M - u) - cB u g * (M - u)) * (p - (0, cB u g * u)).1 := hp
  simpa only [Prod.fst_sub, Prod.snd_sub, sub_zero] using hp'

theorem LY0_sub (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : LY0 u g M ⊆ LT u g M := by
  intro p hp
  obtain ⟨ha, hb, hc⟩ := LY0_mem p hp
  have hs : 0 < M - u := sub_pos.mpr (lM_gt hu hg hx)
  have hA := cApos hu hg
  have kb : (M - u) * (cA u g * cB u g * M) ≤ (M - u) * (cB u g * p.1 + cA u g * p.2) := by nlinarith [hb]
  have kc : (M - u) * (cA u g * (p.2 - cB u g * M)) ≤ (M - u) * ((cC u g - cB u g) * p.1) := by nlinarith [hc]
  exact mem_LT (lM_pos hu hg hx).le p (by nlinarith [ha, mul_pos hA hu])
    (le_of_mul_le_mul_left kb hs) (le_of_mul_le_mul_left kc hs)

theorem Lx_le_0 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LY0 u g M, p.1 ≤ lX0 u g M :=
  fun p hp => (LY0_mem p hp).1

/-! ## `LS1`, the tile at scale `e f` -/

theorem Lx_ge_1 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LS1 u g M, lX0 u g M ≤ p.1 :=
  Erdos634.Draft.S2L.tri_fst_ge (A := lSa u g M) (B := lSb u g M) (C := lSc u g M) (lX0 u g M)
    (lX0_le_lX1 hu hg) (lX0_le_lX1 hu hg) (le_refl _)

theorem Ly_ge_1 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LS1 u g M, lYa u g M ≤ p.2 :=
  Erdos634.Draft.S2L.tri_snd_ge (A := lSa u g M) (B := lSb u g M) (C := lSc u g M) (lYa u g M)
    lYa_le_lYt (le_refl _) (le_refl _)

theorem LS1_sub (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : LS1 u g M ⊆ LT u g M := by
  have hA := cApos hu hg
  have hB := cBpos hu hg
  have hC := lcC_pos hu hg
  have hM := lM_pos hu hg hx
  have hMu := lM_gt hu hg hx
  have e := lYa_eq (u := u) (g := g) (M := M)
  have hYa : 0 ≤ lYa u g M := by
    rw [e]; nlinarith [mul_pos hC (sub_pos.mpr hMu), mul_pos hB hu]
  have pAC : 0 ≤ cA u g * (cC u g * M) := by positivity
  have pAYa : 0 ≤ cA u g * lYa u g M := mul_nonneg hA.le hYa
  have pACM : 0 ≤ cA u g * (cC u g * (M - u)) := mul_nonneg hA.le (mul_nonneg hC.le (by linarith))
  have kYt := mul_le_mul_of_nonneg_left (lYa_le_lYt (u := u) (g := g) (M := M)) hA.le
  have h1 : ∀ p ∈ LS1 u g M, p.1 ≤ cA u g * M :=
    Erdos634.Draft.S2L.tri_fst_le (A := lSa u g M) (B := lSb u g M) (C := lSc u g M) (cA u g * M)
      (le_refl _) (le_refl _) (lX0_le_lX1 hu hg)
  have h2 : ∀ p ∈ LS1 u g M, cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 :=
    Erdos634.Draft.S2L.tri_ge (A := lSa u g M) (B := lSb u g M) (C := lSc u g M) (cB u g) (cA u g)
      (cA u g * cB u g * M)
      (by simp only [lSa, lX1, lYt]; nlinarith [pAC])
      (by simp only [lSb, lX1]; nlinarith [pAYa])
      (by simp only [lSc, lX0, e]; nlinarith [pACM])
  have h3 : ∀ p ∈ LS1 u g M, (-(cC u g - cB u g)) * p.1 + cA u g * p.2 ≤ cA u g * (cB u g * M) :=
    Erdos634.Draft.S2L.tri_le (A := lSa u g M) (B := lSb u g M) (C := lSc u g M) (-(cC u g - cB u g)) (cA u g)
      (cA u g * (cB u g * M))
      (by simp only [lSa, lX1, lYt]; nlinarith)
      (by simp only [lSb, lX1]; simp only [lYt] at kYt; nlinarith [kYt])
      (by simp only [lSc, lX0, e]; nlinarith)
  intro p hp
  have k3 := h3 p hp
  exact mem_LT hM.le p (h1 p hp) (h2 p hp) (by linarith)

/-! ## `LRa`, `LRb` -/

theorem hull_box {S : Set (ℝ × ℝ)} {a b c d : ℝ} (h : ∀ v ∈ S, a ≤ v.1 ∧ v.1 ≤ b ∧ c ≤ v.2 ∧ v.2 ≤ d) :
    ∀ p ∈ convexHull ℝ S, a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d := by
  intro p hp
  have h1 := hull_ge (S := S) 1 0 a (fun v hv => by have := (h v hv).1; linarith) p hp
  have h2 := hull_le (S := S) 1 0 b (fun v hv => by have := (h v hv).2.1; linarith) p hp
  have h3 := hull_ge (S := S) 0 1 c (fun v hv => by have := (h v hv).2.2.1; linarith) p hp
  have h4 := hull_le (S := S) 0 1 d (fun v hv => by have := (h v hv).2.2.2; linarith) p hp
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- an axis-parallel parallelogram `n (w, 0) × m (0, h)` at `(x₀, y₀)` lies in the box -/
theorem Pg_box {x0 y0 n w m h : ℝ} (hnw : 0 ≤ n * w) (hmh : 0 ≤ m * h) :
    ∀ p ∈ Pg (x0, y0) (n • (w, (0 : ℝ))) (m • ((0 : ℝ), h)),
      x0 ≤ p.1 ∧ p.1 ≤ x0 + n * w ∧ y0 ≤ p.2 ∧ p.2 ≤ y0 + m * h := by
  apply hull_box
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_zero, add_zero, zero_add] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem LRa_box (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    ∀ p ∈ LRa u g M, lX0 u g M ≤ p.1 ∧ p.1 ≤ lX1 u g M ∧ lYb u g M ≤ p.2 ∧ p.2 ≤ lYa u g M := by
  intro p hp
  have hb := Pg_box (x0 := lX0 u g M) (y0 := lYb u g M) (n := u * (u + g)) (w := cb u g) (m := lxa u g M)
    (h := ca u g) (mul_nonneg (by positivity) (hbpos hu hg).le) (mul_nonneg hx (hapos hu hg).le) p hp
  have e1 : lX0 u g M + u * (u + g) * cb u g = lX1 u g M := by simp only [lX0, lX1, cA, cb]; ring
  have e2 : lYb u g M + lxa u g M * ca u g = lYa u g M := rfl
  obtain ⟨b1, b2, b3, b4⟩ := hb
  exact ⟨b1, by linarith, b3, by linarith⟩

theorem LRb_box (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    ∀ p ∈ LRb u g M, lX0 u g M ≤ p.1 ∧ p.1 ≤ lX1 u g M ∧ lY1 u g ≤ p.2 ∧ p.2 ≤ lYb u g M := by
  intro p hp
  have hM := lM_pos hu hg hx
  have hb := Pg_box (x0 := lX0 u g M) (y0 := lY1 u g) (n := cb u g) (w := ca u g) (m := u * M)
    (h := cb u g) (mul_nonneg (hbpos hu hg).le (hapos hu hg).le)
    (mul_nonneg (mul_nonneg hu.le hM.le) (hbpos hu hg).le) p hp
  have e1 : lX0 u g M + cb u g * ca u g = lX1 u g M := by simp only [lX0, lX1, cA, cb, ca]; ring
  have e2 : lY1 u g + u * M * cb u g = lYb u g M := rfl
  obtain ⟨b1, b2, b3, b4⟩ := hb
  exact ⟨b1, by linarith, b3, by linarith⟩

theorem LRa_sub (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : LRa u g M ⊆ LT u g M :=
  box_sub hu hg hx (fun p hp => by
    obtain ⟨b1, b2, b3, b4⟩ := LRa_box hu hg hx p hp
    exact ⟨b1, b2, le_trans (lY1_le_lYb hu hg (lM_pos hu hg hx).le) b3, b4⟩)

theorem LRb_sub (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : LRb u g M ⊆ LT u g M :=
  box_sub hu hg hx (fun p hp => by
    obtain ⟨b1, b2, b3, b4⟩ := LRb_box hu hg hx p hp
    exact ⟨b1, b2, b3, le_trans b4 (lYb_le_lYa hu hg hx)⟩)

theorem Lx_ge_2 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRa u g M, lX0 u g M ≤ p.1 :=
  fun p hp => (LRa_box hu hg hx p hp).1
theorem Ly_le_2 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRa u g M, p.2 ≤ lYa u g M :=
  fun p hp => (LRa_box hu hg hx p hp).2.2.2
theorem Ly_ge_2 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRa u g M, lYb u g M ≤ p.2 :=
  fun p hp => (LRa_box hu hg hx p hp).2.2.1
theorem Ly_ge_2_Y1 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRa u g M, lY1 u g ≤ p.2 :=
  fun p hp => le_trans (lY1_le_lYb hu hg (lM_pos hu hg hx).le) (Ly_ge_2 hu hg hx p hp)
theorem Lx_ge_3 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRb u g M, lX0 u g M ≤ p.1 :=
  fun p hp => (LRb_box hu hg hx p hp).1
theorem Ly_ge_3 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRb u g M, lY1 u g ≤ p.2 :=
  fun p hp => (LRb_box hu hg hx p hp).2.2.1
theorem Ly_le_3 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRb u g M, p.2 ≤ lYb u g M :=
  fun p hp => (LRb_box hu hg hx p hp).2.2.2
theorem Ly_leYa_3 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ LRb u g M, p.2 ≤ lYa u g M :=
  fun p hp => le_trans (Ly_le_3 hu hg hx p hp) (lYb_le_lYa hu hg hx)

/-! ## The cap: the six pieces of `CollarGGeom` at `σ = 1`, translated -/

/-- the four bounds of a translated cap piece, from the bounds of `CollarGGeom` at `σ = 1` -/
theorem lcap_bounds (hu : 0 < u) (hg : 0 < g) (M : ℝ) {Z : Set (ℝ × ℝ)}
    (hx : ∀ q ∈ Z, cA u g * ct g 1 ≤ q.1) (hy : ∀ q ∈ Z, q.2 ≤ cB u g * u + cL u g) (hs : Z ⊆ ZT u g 1) :
    ∀ p ∈ Sh (lvsh u g M) Z, lX0 u g M ≤ p.1 ∧ p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧
      cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 := by
  intro p hp
  have hq : p - lvsh u g M ∈ Z := hp
  have e1 : (p - lvsh u g M).1 = p.1 - cA u g * (M - (u + g) - 1) := rfl
  have e2 : (p - lvsh u g M).2 = p.2 - 0 := rfl
  have ec : ct g 1 = g + 1 := rfl
  have h1 := hx _ hq
  have h2 := hy _ hq
  have h3 : (p - lvsh u g M).1 ≤ cA u g * (ct g 1 + u) ∧ (p - lvsh u g M).2 ≤ cB u g * (ct g 1 + u) ∧
      cA u g * (ct g 1 + u) * (cB u g * (ct g 1 + u))
        ≤ cB u g * (ct g 1 + u) * (p - lvsh u g M).1 + cA u g * (ct g 1 + u) * (p - lvsh u g M).2 := hs hq
  obtain ⟨h31, -, h33⟩ := h3
  rw [e1, ec] at h1 h31
  rw [e2] at h2
  rw [e1, e2, ec] at h33
  have hF : 0 < g + 1 + u := by positivity
  refine ⟨by simp only [lX0]; linarith, by simp only [lX1]; linarith, by simp only [lY1]; linarith, ?_⟩
  have key : (g + 1 + u) * (cA u g * cB u g * M) ≤ (g + 1 + u) * (cB u g * p.1 + cA u g * p.2) := by
    nlinarith [h33]
  exact le_of_mul_le_mul_left key hF

theorem cap_sub (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) {Z : Set (ℝ × ℝ)}
    (h : ∀ p ∈ Sh (lvsh u g M) Z, lX0 u g M ≤ p.1 ∧ p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧
      cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2) : Sh (lvsh u g M) Z ⊆ LT u g M := by
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := h p hp
  exact mem_LT (lM_pos hu hg hx).le p h2 h4 (third_of hu hg p h1 (le_trans h3 (lY1_le_lYa hu hg hx)))

theorem cap_b3 (hu : 0 < u) (hg : 0 < g) (M : ℝ) : ∀ p ∈ Sh (lvsh u g M) (Z3 u g 1), lX0 u g M ≤ p.1 ∧
    p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧ cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 :=
  lcap_bounds hu hg M (xg_3 hu hg one_pos) (yl_3 hu hg one_pos) (Z3_sub hu hg one_pos)
theorem cap_b4 (hu : 0 < u) (hg : 0 < g) (M : ℝ) : ∀ p ∈ Sh (lvsh u g M) (Z4 u g 1), lX0 u g M ≤ p.1 ∧
    p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧ cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 :=
  lcap_bounds hu hg M (xg_4 hu hg one_pos) (yl_4 hu hg one_pos) (Z4_sub hu hg one_pos)
theorem cap_b5 (hu : 0 < u) (hg : 0 < g) (M : ℝ) : ∀ p ∈ Sh (lvsh u g M) (Z5 u g 1), lX0 u g M ≤ p.1 ∧
    p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧ cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 :=
  lcap_bounds hu hg M (xg_5 hu hg one_pos) (yl_5 hu hg one_pos) (Z5_sub hu hg one_pos)
theorem cap_b6 (hu : 0 < u) (hg : 0 < g) (M : ℝ) : ∀ p ∈ Sh (lvsh u g M) (Z6 u g 1), lX0 u g M ≤ p.1 ∧
    p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧ cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 :=
  lcap_bounds hu hg M (xg_6 hu hg one_pos) (yl_6 hu hg one_pos) (Z6_sub hu hg one_pos)
theorem cap_b7 (hu : 0 < u) (hg : 0 < g) (M : ℝ) : ∀ p ∈ Sh (lvsh u g M) (Z7 u g 1), lX0 u g M ≤ p.1 ∧
    p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧ cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 :=
  lcap_bounds hu hg M (xg_7 hu hg one_pos) (yl_7 hu hg one_pos) (Z7_sub hu hg one_pos)
theorem cap_b8 (hu : 0 < u) (hg : 0 < g) (M : ℝ) : ∀ p ∈ Sh (lvsh u g M) (Z8 u g 1), lX0 u g M ≤ p.1 ∧
    p.1 ≤ lX1 u g M ∧ p.2 ≤ lY1 u g ∧ cA u g * cB u g * M ≤ cB u g * p.1 + cA u g * p.2 :=
  lcap_bounds hu hg M (xg_8 hu hg one_pos) (yl_8 hu hg one_pos) (Z8_sub hu hg one_pos)

theorem Lx_ge_4 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z3 u g 1), lX0 u g M ≤ p.1 :=
  fun p hp => (cap_b3 hu hg M p hp).1
theorem Lx_ge_5 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z4 u g 1), lX0 u g M ≤ p.1 :=
  fun p hp => (cap_b4 hu hg M p hp).1
theorem Lx_ge_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z5 u g 1), lX0 u g M ≤ p.1 :=
  fun p hp => (cap_b5 hu hg M p hp).1
theorem Lx_ge_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z6 u g 1), lX0 u g M ≤ p.1 :=
  fun p hp => (cap_b6 hu hg M p hp).1
theorem Lx_ge_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z7 u g 1), lX0 u g M ≤ p.1 :=
  fun p hp => (cap_b7 hu hg M p hp).1
theorem Lx_ge_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z8 u g 1), lX0 u g M ≤ p.1 :=
  fun p hp => (cap_b8 hu hg M p hp).1

theorem Ly_le_4 (hu : 0 < u) (hg : 0 < g) : ∀ p ∈ Sh (lvsh u g M) (Z3 u g 1), p.2 ≤ lY1 u g :=
  fun p hp => (cap_b3 hu hg M p hp).2.2.1
theorem Ly_le_5 (hu : 0 < u) (hg : 0 < g) : ∀ p ∈ Sh (lvsh u g M) (Z4 u g 1), p.2 ≤ lY1 u g :=
  fun p hp => (cap_b4 hu hg M p hp).2.2.1
theorem Ly_le_6 (hu : 0 < u) (hg : 0 < g) : ∀ p ∈ Sh (lvsh u g M) (Z5 u g 1), p.2 ≤ lY1 u g :=
  fun p hp => (cap_b5 hu hg M p hp).2.2.1
theorem Ly_le_7 (hu : 0 < u) (hg : 0 < g) : ∀ p ∈ Sh (lvsh u g M) (Z6 u g 1), p.2 ≤ lY1 u g :=
  fun p hp => (cap_b6 hu hg M p hp).2.2.1
theorem Ly_le_8 (hu : 0 < u) (hg : 0 < g) : ∀ p ∈ Sh (lvsh u g M) (Z7 u g 1), p.2 ≤ lY1 u g :=
  fun p hp => (cap_b7 hu hg M p hp).2.2.1
theorem Ly_le_9 (hu : 0 < u) (hg : 0 < g) : ∀ p ∈ Sh (lvsh u g M) (Z8 u g 1), p.2 ≤ lY1 u g :=
  fun p hp => (cap_b8 hu hg M p hp).2.2.1

theorem Ly_leYa_4 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z3 u g 1), p.2 ≤ lYa u g M :=
  fun p hp => le_trans (Ly_le_4 hu hg p hp) (lY1_le_lYa hu hg hx)
theorem Ly_leYa_5 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z4 u g 1), p.2 ≤ lYa u g M :=
  fun p hp => le_trans (Ly_le_5 hu hg p hp) (lY1_le_lYa hu hg hx)
theorem Ly_leYa_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z5 u g 1), p.2 ≤ lYa u g M :=
  fun p hp => le_trans (Ly_le_6 hu hg p hp) (lY1_le_lYa hu hg hx)
theorem Ly_leYa_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z6 u g 1), p.2 ≤ lYa u g M :=
  fun p hp => le_trans (Ly_le_7 hu hg p hp) (lY1_le_lYa hu hg hx)
theorem Ly_leYa_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z7 u g 1), p.2 ≤ lYa u g M :=
  fun p hp => le_trans (Ly_le_8 hu hg p hp) (lY1_le_lYa hu hg hx)
theorem Ly_leYa_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ p ∈ Sh (lvsh u g M) (Z8 u g 1), p.2 ≤ lYa u g M :=
  fun p hp => le_trans (Ly_le_9 hu hg p hp) (lY1_le_lYa hu hg hx)

/-! ## The ten regions lie in `T_M` -/

theorem Lf_sub (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) : ∀ a : Fin 10, Lf u g M a ⊆ LT u g M :=
  fun a => match a with
  | ⟨0, _⟩ => LY0_sub hu hg hx
  | ⟨1, _⟩ => LS1_sub hu hg hx
  | ⟨2, _⟩ => LRa_sub hu hg hx
  | ⟨3, _⟩ => LRb_sub hu hg hx
  | ⟨4, _⟩ => cap_sub hu hg hx (cap_b3 hu hg M)
  | ⟨5, _⟩ => cap_sub hu hg hx (cap_b4 hu hg M)
  | ⟨6, _⟩ => cap_sub hu hg hx (cap_b5 hu hg M)
  | ⟨7, _⟩ => cap_sub hu hg hx (cap_b6 hu hg M)
  | ⟨8, _⟩ => cap_sub hu hg hx (cap_b7 hu hg M)
  | ⟨9, _⟩ => cap_sub hu hg hx (cap_b8 hu hg M)
  | ⟨k + 10, h⟩ => absurd h (by omega)

/-- the nine regions of the layer lie right of the chord `x = X₀` -/
theorem Lf_right (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    ∀ a : Fin 10, a ≠ ⟨0, by omega⟩ → ∀ p ∈ Lf u g M a, lX0 u g M ≤ p.1 := fun a => match a with
  | ⟨0, _⟩ => fun h => absurd rfl h
  | ⟨1, _⟩ => fun _ => Lx_ge_1 hu hg hx
  | ⟨2, _⟩ => fun _ => Lx_ge_2 hu hg hx
  | ⟨3, _⟩ => fun _ => Lx_ge_3 hu hg hx
  | ⟨4, _⟩ => fun _ => Lx_ge_4 hu hg hx
  | ⟨5, _⟩ => fun _ => Lx_ge_5 hu hg hx
  | ⟨6, _⟩ => fun _ => Lx_ge_6 hu hg hx
  | ⟨7, _⟩ => fun _ => Lx_ge_7 hu hg hx
  | ⟨8, _⟩ => fun _ => Lx_ge_8 hu hg hx
  | ⟨9, _⟩ => fun _ => Lx_ge_9 hu hg hx
  | ⟨k + 10, h⟩ => absurd h (by omega)

/-! ## Pairwise disjoint interiors (45 pairs) -/

theorem dL_0_1 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (LS1 u g M)) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_1 hu hg hx)

theorem dL_0_2 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (LRa u g M)) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_2 hu hg hx)

theorem dL_0_3 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (LRb u g M)) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_3 hu hg hx)

theorem dL_0_4 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (Sh (lvsh u g M) (Z3 u g 1))) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_4 hu hg hx)

theorem dL_0_5 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (Sh (lvsh u g M) (Z4 u g 1))) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_5 hu hg hx)

theorem dL_0_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (Sh (lvsh u g M) (Z5 u g 1))) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_6 hu hg hx)

theorem dL_0_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (Sh (lvsh u g M) (Z6 u g 1))) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_7 hu hg hx)

theorem dL_0_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_8 hu hg hx)

theorem dL_0_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LY0 u g M)) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  interior_disj_fst (lX0 u g M) (Lx_le_0 hu hg hx) (Lx_ge_9 hu hg hx)

theorem dL_1_2 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (LRa u g M)) :=
  (interior_disj_snd (lYa u g M) (Ly_le_2 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_1_3 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (LRb u g M)) :=
  (interior_disj_snd (lYa u g M) (Ly_leYa_3 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_1_4 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (Sh (lvsh u g M) (Z3 u g 1))) :=
  (interior_disj_snd (lYa u g M) (Ly_leYa_4 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_1_5 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (Sh (lvsh u g M) (Z4 u g 1))) :=
  (interior_disj_snd (lYa u g M) (Ly_leYa_5 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_1_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (Sh (lvsh u g M) (Z5 u g 1))) :=
  (interior_disj_snd (lYa u g M) (Ly_leYa_6 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_1_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (Sh (lvsh u g M) (Z6 u g 1))) :=
  (interior_disj_snd (lYa u g M) (Ly_leYa_7 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_1_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  (interior_disj_snd (lYa u g M) (Ly_leYa_8 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_1_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LS1 u g M)) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  (interior_disj_snd (lYa u g M) (Ly_leYa_9 hu hg hx) (Ly_ge_1 hu hg hx)).symm

theorem dL_2_3 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRa u g M)) (interior (LRb u g M)) :=
  (interior_disj_snd (lYb u g M) (Ly_le_3 hu hg hx) (Ly_ge_2 hu hg hx)).symm

theorem dL_2_4 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRa u g M)) (interior (Sh (lvsh u g M) (Z3 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_4 hu hg) (Ly_ge_2_Y1 hu hg hx)).symm

theorem dL_2_5 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRa u g M)) (interior (Sh (lvsh u g M) (Z4 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_5 hu hg) (Ly_ge_2_Y1 hu hg hx)).symm

theorem dL_2_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRa u g M)) (interior (Sh (lvsh u g M) (Z5 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_6 hu hg) (Ly_ge_2_Y1 hu hg hx)).symm

theorem dL_2_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRa u g M)) (interior (Sh (lvsh u g M) (Z6 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_7 hu hg) (Ly_ge_2_Y1 hu hg hx)).symm

theorem dL_2_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRa u g M)) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_8 hu hg) (Ly_ge_2_Y1 hu hg hx)).symm

theorem dL_2_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRa u g M)) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_9 hu hg) (Ly_ge_2_Y1 hu hg hx)).symm

theorem dL_3_4 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRb u g M)) (interior (Sh (lvsh u g M) (Z3 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_4 hu hg) (Ly_ge_3 hu hg hx)).symm

theorem dL_3_5 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRb u g M)) (interior (Sh (lvsh u g M) (Z4 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_5 hu hg) (Ly_ge_3 hu hg hx)).symm

theorem dL_3_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRb u g M)) (interior (Sh (lvsh u g M) (Z5 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_6 hu hg) (Ly_ge_3 hu hg hx)).symm

theorem dL_3_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRb u g M)) (interior (Sh (lvsh u g M) (Z6 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_7 hu hg) (Ly_ge_3 hu hg hx)).symm

theorem dL_3_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRb u g M)) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_8 hu hg) (Ly_ge_3 hu hg hx)).symm

theorem dL_3_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (LRb u g M)) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  (interior_disj_snd (lY1 u g) (Ly_le_9 hu hg) (Ly_ge_3 hu hg hx)).symm

theorem dL_4_5 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z3 u g 1))) (interior (Sh (lvsh u g M) (Z4 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_3_4 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_4_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z3 u g 1))) (interior (Sh (lvsh u g M) (Z5 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_3_5 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_4_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z3 u g 1))) (interior (Sh (lvsh u g M) (Z6 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_3_6 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_4_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z3 u g 1))) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_3_7 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_4_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z3 u g 1))) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_3_8 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_5_6 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z4 u g 1))) (interior (Sh (lvsh u g M) (Z5 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_4_5 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_5_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z4 u g 1))) (interior (Sh (lvsh u g M) (Z6 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_4_6 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_5_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z4 u g 1))) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_4_7 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_5_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z4 u g 1))) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_4_8 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_6_7 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z5 u g 1))) (interior (Sh (lvsh u g M) (Z6 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_5_6 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_6_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z5 u g 1))) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_5_7 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_6_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z5 u g 1))) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_5_8 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_7_8 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z6 u g 1))) (interior (Sh (lvsh u g M) (Z7 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_6_7 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_7_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z6 u g 1))) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_6_8 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_8_9 (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    Disjoint (interior (Sh (lvsh u g M) (Z7 u g 1))) (interior (Sh (lvsh u g M) (Z8 u g 1))) :=
  disj_Sh (lvsh u g M) (dZ_7_8 hu hg (one_pos : (0:ℝ) < 1))

theorem dL_all (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M) :
    ∀ a b : Fin 10, a ≠ b → Disjoint (interior (Lf u g M a)) (interior (Lf u g M b)) := by
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => dL_0_1 hu hg hx
  | ⟨0, _⟩, ⟨2, _⟩ => dL_0_2 hu hg hx
  | ⟨0, _⟩, ⟨3, _⟩ => dL_0_3 hu hg hx
  | ⟨0, _⟩, ⟨4, _⟩ => dL_0_4 hu hg hx
  | ⟨0, _⟩, ⟨5, _⟩ => dL_0_5 hu hg hx
  | ⟨0, _⟩, ⟨6, _⟩ => dL_0_6 hu hg hx
  | ⟨0, _⟩, ⟨7, _⟩ => dL_0_7 hu hg hx
  | ⟨0, _⟩, ⟨8, _⟩ => dL_0_8 hu hg hx
  | ⟨0, _⟩, ⟨9, _⟩ => dL_0_9 hu hg hx
  | ⟨1, _⟩, ⟨0, _⟩ => (dL_0_1 hu hg hx).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => dL_1_2 hu hg hx
  | ⟨1, _⟩, ⟨3, _⟩ => dL_1_3 hu hg hx
  | ⟨1, _⟩, ⟨4, _⟩ => dL_1_4 hu hg hx
  | ⟨1, _⟩, ⟨5, _⟩ => dL_1_5 hu hg hx
  | ⟨1, _⟩, ⟨6, _⟩ => dL_1_6 hu hg hx
  | ⟨1, _⟩, ⟨7, _⟩ => dL_1_7 hu hg hx
  | ⟨1, _⟩, ⟨8, _⟩ => dL_1_8 hu hg hx
  | ⟨1, _⟩, ⟨9, _⟩ => dL_1_9 hu hg hx
  | ⟨2, _⟩, ⟨0, _⟩ => (dL_0_2 hu hg hx).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (dL_1_2 hu hg hx).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => dL_2_3 hu hg hx
  | ⟨2, _⟩, ⟨4, _⟩ => dL_2_4 hu hg hx
  | ⟨2, _⟩, ⟨5, _⟩ => dL_2_5 hu hg hx
  | ⟨2, _⟩, ⟨6, _⟩ => dL_2_6 hu hg hx
  | ⟨2, _⟩, ⟨7, _⟩ => dL_2_7 hu hg hx
  | ⟨2, _⟩, ⟨8, _⟩ => dL_2_8 hu hg hx
  | ⟨2, _⟩, ⟨9, _⟩ => dL_2_9 hu hg hx
  | ⟨3, _⟩, ⟨0, _⟩ => (dL_0_3 hu hg hx).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (dL_1_3 hu hg hx).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (dL_2_3 hu hg hx).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => dL_3_4 hu hg hx
  | ⟨3, _⟩, ⟨5, _⟩ => dL_3_5 hu hg hx
  | ⟨3, _⟩, ⟨6, _⟩ => dL_3_6 hu hg hx
  | ⟨3, _⟩, ⟨7, _⟩ => dL_3_7 hu hg hx
  | ⟨3, _⟩, ⟨8, _⟩ => dL_3_8 hu hg hx
  | ⟨3, _⟩, ⟨9, _⟩ => dL_3_9 hu hg hx
  | ⟨4, _⟩, ⟨0, _⟩ => (dL_0_4 hu hg hx).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (dL_1_4 hu hg hx).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (dL_2_4 hu hg hx).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (dL_3_4 hu hg hx).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨4, _⟩, ⟨5, _⟩ => dL_4_5 hu hg hx
  | ⟨4, _⟩, ⟨6, _⟩ => dL_4_6 hu hg hx
  | ⟨4, _⟩, ⟨7, _⟩ => dL_4_7 hu hg hx
  | ⟨4, _⟩, ⟨8, _⟩ => dL_4_8 hu hg hx
  | ⟨4, _⟩, ⟨9, _⟩ => dL_4_9 hu hg hx
  | ⟨5, _⟩, ⟨0, _⟩ => (dL_0_5 hu hg hx).symm
  | ⟨5, _⟩, ⟨1, _⟩ => (dL_1_5 hu hg hx).symm
  | ⟨5, _⟩, ⟨2, _⟩ => (dL_2_5 hu hg hx).symm
  | ⟨5, _⟩, ⟨3, _⟩ => (dL_3_5 hu hg hx).symm
  | ⟨5, _⟩, ⟨4, _⟩ => (dL_4_5 hu hg hx).symm
  | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hab
  | ⟨5, _⟩, ⟨6, _⟩ => dL_5_6 hu hg hx
  | ⟨5, _⟩, ⟨7, _⟩ => dL_5_7 hu hg hx
  | ⟨5, _⟩, ⟨8, _⟩ => dL_5_8 hu hg hx
  | ⟨5, _⟩, ⟨9, _⟩ => dL_5_9 hu hg hx
  | ⟨6, _⟩, ⟨0, _⟩ => (dL_0_6 hu hg hx).symm
  | ⟨6, _⟩, ⟨1, _⟩ => (dL_1_6 hu hg hx).symm
  | ⟨6, _⟩, ⟨2, _⟩ => (dL_2_6 hu hg hx).symm
  | ⟨6, _⟩, ⟨3, _⟩ => (dL_3_6 hu hg hx).symm
  | ⟨6, _⟩, ⟨4, _⟩ => (dL_4_6 hu hg hx).symm
  | ⟨6, _⟩, ⟨5, _⟩ => (dL_5_6 hu hg hx).symm
  | ⟨6, _⟩, ⟨6, _⟩ => absurd rfl hab
  | ⟨6, _⟩, ⟨7, _⟩ => dL_6_7 hu hg hx
  | ⟨6, _⟩, ⟨8, _⟩ => dL_6_8 hu hg hx
  | ⟨6, _⟩, ⟨9, _⟩ => dL_6_9 hu hg hx
  | ⟨7, _⟩, ⟨0, _⟩ => (dL_0_7 hu hg hx).symm
  | ⟨7, _⟩, ⟨1, _⟩ => (dL_1_7 hu hg hx).symm
  | ⟨7, _⟩, ⟨2, _⟩ => (dL_2_7 hu hg hx).symm
  | ⟨7, _⟩, ⟨3, _⟩ => (dL_3_7 hu hg hx).symm
  | ⟨7, _⟩, ⟨4, _⟩ => (dL_4_7 hu hg hx).symm
  | ⟨7, _⟩, ⟨5, _⟩ => (dL_5_7 hu hg hx).symm
  | ⟨7, _⟩, ⟨6, _⟩ => (dL_6_7 hu hg hx).symm
  | ⟨7, _⟩, ⟨7, _⟩ => absurd rfl hab
  | ⟨7, _⟩, ⟨8, _⟩ => dL_7_8 hu hg hx
  | ⟨7, _⟩, ⟨9, _⟩ => dL_7_9 hu hg hx
  | ⟨8, _⟩, ⟨0, _⟩ => (dL_0_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨1, _⟩ => (dL_1_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨2, _⟩ => (dL_2_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨3, _⟩ => (dL_3_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨4, _⟩ => (dL_4_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨5, _⟩ => (dL_5_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨6, _⟩ => (dL_6_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨7, _⟩ => (dL_7_8 hu hg hx).symm
  | ⟨8, _⟩, ⟨8, _⟩ => absurd rfl hab
  | ⟨8, _⟩, ⟨9, _⟩ => dL_8_9 hu hg hx
  | ⟨9, _⟩, ⟨0, _⟩ => (dL_0_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨1, _⟩ => (dL_1_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨2, _⟩ => (dL_2_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨3, _⟩ => (dL_3_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨4, _⟩ => (dL_4_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨5, _⟩ => (dL_5_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨6, _⟩ => (dL_6_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨7, _⟩ => (dL_7_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨8, _⟩ => (dL_8_9 hu hg hx).symm
  | ⟨9, _⟩, ⟨9, _⟩ => absurd rfl hab
  | ⟨k + 10, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 10, h⟩ => absurd h (by omega)

end real

end

end Erdos634.Draft.LayerG

#print axioms Erdos634.Draft.LayerG.Lf_sub
#print axioms Erdos634.Draft.LayerG.Lf_right
#print axioms Erdos634.Draft.LayerG.dL_all
