/-
Draft/SideRunGAngles.lean  In `AllThreshold`.  An addition to the ten
modules of the every-member side theorem (module 11).

**`thm:siderunall` with the triangle given by its CORNER ANGLES**, as the paper states it.

PAPER STATEMENT.  `1 ≤ e < f` coprime, `(a, b, c) = (ef, f² − e², f²)`, angles `α, β, γ` opposite `a, b, c`.  Let `Δ` be a triangle
with a side `s` whose two corners have the angles `β, β` or `α + β, β`, cut into congruent triangles with sides `(a, b, c)`.  Then `s`
carries `f` consecutive tiles of type `C_1` or `f` of type `C_2`; in particular `|s| ≥ f³`.

THE LEAN STATEMENTS (`thm_siderunall_angles_T`, `thm_siderunall_angles_W`).  `Δ` is the target of a `CongruentDissection D₀` whose
model has the sides `ef, f² − e², f²` (`HasSides`); the vertices of `Δ` are named by a permutation `τ` of `Fin 3`: `τ 0 = Q`,
`τ 1 = B` (the ends of `s`), `τ 2 = A` (the third vertex).  The hypotheses are the two corner angles,
`cornerAngle A Q B = β` (resp. `α + β`) and `cornerAngle Q B A = β`, with `α = modelAlpha e f`, `β = modelBeta e f` (these are the
angles opposite `a`, `b` of every triangle with sides `a, b, c`: `SideRunGMain.modelAngles_of_sidesG`).  The conclusion is the run of
`f` tiles of `D₀` on the segment `[Q, B]` (`LaysBaseOn`) with `f³ ≤ |QB|`.

HOW.  `law_sines_corners` (law of sines in `Δ`), `corners_sides_T`, `corners_sides_W` (the sides of `Δ` from its corners, the model
triangle supplying the ratios of the sines of `α`, `β`, `γ`) turn the corners into the side lengths `s f³, s f³, s e (3f² − e²)`
(resp. `s f³, s f (f² − e²), s e (2f² − e²)`) for a real `s > 0`; then `SideRunGMain.thm_siderunall_T_pinned` /
`thm_siderunall_W_pinned` (vertices named) give the run.

DIFFERENCES FROM THE PAPER.  (i) The angles `α`, `β` are named `modelAlpha e f`, `modelBeta e f` (`α = (π − 2β)/3`, `β = arccos
(e (3f² − e²) / (2f³))`); that they are the angles of the tile opposite `a`, `b` is proved (`modelAngles_of_sidesG`).  (ii) "Cut
into congruent triangles with sides `(a, b, c)`" is a `CongruentDissection` whose model has `HasSides` `(a, b, c)` (any number of
tiles, reflections allowed).  (iii) The angle of a corner is the unoriented `cornerAngle` in `[0, π]`.  (iv) The types `C_1`, `C_2`
are `LaysBaseOn ... Ty.C1`, `Ty.C2` (see `SideRunGMain`).

WITNESSES (no vacuity).  `angles_witness_T`, `angles_witness_W`: for every coprime member the seed tilings of `T_f(e, f)` and `W_f(e, f)`
(`UniformThreshold.betaTilable_self`, `CollarG.wTilable_seed`) satisfy every hypothesis of `thm_siderunall_angles_T`, `thm_siderunall_angles_W`
(corner angles computed by the cosine rule from the side lengths).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMain

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.TilePlacement Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

variable {N : ℕ}

/-! ## 1. The law of sines in a triangle with named vertices -/

/-- **Law of sines for the triangle `Q = T.pts (τ 0)`, `B = T.pts (τ 1)`, `A = T.pts (τ 2)` with the corners `θQ`, `θB` at `Q`, `B`**:
the angle at `A` is `π − θQ − θB`, and `sin θQ · |QB| = sin (π − θQ − θB) · |BA|`, `sin θB · |QB| = sin (π − θQ − θB) · |AQ|`. -/
theorem law_sines_corners (T : Erdos634.Geometry.Tri) (τ : Equiv.Perm (Fin 3)) {θQ θB : ℝ}
    (hQ : cornerAngle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) = θQ)
    (hB : cornerAngle (T.pts (τ 0)) (T.pts (τ 1)) (T.pts (τ 2)) = θB) :
    Real.sin θQ * dist (T.pts (τ 0)) (T.pts (τ 1)) =
        Real.sin (Real.pi - θQ - θB) * dist (T.pts (τ 1)) (T.pts (τ 2)) ∧
    Real.sin θB * dist (T.pts (τ 0)) (T.pts (τ 1)) =
        Real.sin (Real.pi - θQ - θB) * dist (T.pts (τ 2)) (T.pts (τ 0)) := by
  have hsum := cornerAngle_sum (T.relabel τ)
  simp only [Tri.relabel_pts] at hsum
  have c1 : cornerAngle (T.pts (τ 1)) (T.pts (τ 0)) (T.pts (τ 2)) = θQ := by
    unfold cornerAngle at hQ ⊢
    rw [EuclideanGeometry.angle_comm]; exact hQ
  have c2 : cornerAngle (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0)) = θB := by
    unfold cornerAngle at hB ⊢
    rw [EuclideanGeometry.angle_comm]; exact hB
  have hA : cornerAngle (T.pts (τ 0)) (T.pts (τ 2)) (T.pts (τ 1)) = Real.pi - θQ - θB := by linarith
  have hA' : EuclideanGeometry.angle (T.pts (τ 0)) (T.pts (τ 2)) (T.pts (τ 1)) = Real.pi - θQ - θB := hA
  have hQ' : EuclideanGeometry.angle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) = θQ := hQ
  have c2' : EuclideanGeometry.angle (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0)) = θB := c2
  have l1 := EuclideanGeometry.law_sin (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1))
  have l2 := EuclideanGeometry.law_sin (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0))
  constructor
  · rw [hQ', EuclideanGeometry.angle_comm (T.pts (τ 1)) (T.pts (τ 2)) (T.pts (τ 0)), hA'] at l1
    exact l1
  · rw [c2', hA', dist_comm (T.pts (τ 1)) (T.pts (τ 0)), dist_comm (T.pts (τ 0)) (T.pts (τ 2))] at l2
    exact l2

/-! ## 2. The sides from the corners -/

/-- **The sides of the triangle with corners `β, β`** (`T_s(e, f)`): `|BA| = |AQ| = s f³`, `|QB| = s e (3f² − e²)`, `s > 0`. -/
theorem corners_sides_T (T : Erdos634.Geometry.Tri) (τ : Equiv.Perm (Fin 3)) {e f : ℕ} (he : 1 ≤ e)
    (hef : e < f)
    (hQ : cornerAngle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) = modelBeta (e : ℝ) (f : ℝ))
    (hB : cornerAngle (T.pts (τ 0)) (T.pts (τ 1)) (T.pts (τ 2)) = modelBeta (e : ℝ) (f : ℝ)) :
    ∃ s : ℝ, 0 < s ∧ dist (T.pts (τ 1)) (T.pts (τ 2)) = s * (f : ℝ) ^ 3 ∧
      dist (T.pts (τ 2)) (T.pts (τ 0)) = s * (f : ℝ) ^ 3 ∧
      dist (T.pts (τ 0)) (T.pts (τ 1)) = s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨l1, l2⟩ := law_sines_corners T τ hQ hB
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have hK : (0 : ℝ) < e * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have := sq_nonneg (f : ℝ)
    exact mul_pos he0 (by linarith)
  have hcosβ := cos_modelBeta he0 hefR
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  generalize modelBeta (e : ℝ) (f : ℝ) = β at hQ hB hcosβ hb0 hb2 l1 l2
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith [Real.pi_pos])
  have hpi : Real.pi - β - β = Real.pi - 2 * β := by ring
  rw [hpi, Real.sin_pi_sub, Real.sin_two_mul] at l1 l2
  have hc2 : Real.cos β * (2 * (f : ℝ) ^ 3) = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have h := hcosβ
    rw [eq_div_iff (by positivity)] at h
    unfold baseLen Nq at h
    linarith
  have hcpos : 0 < Real.cos β := by
    by_contra hcon
    push Not at hcon
    nlinarith [pow_pos hf0 3]
  have hXpos : 0 < dist (T.pts (τ 1)) (T.pts (τ 2)) :=
    dist_pos.mpr (fun h => absurd (T.indep.injective h) (τ.injective.ne (by decide)))
  set L := dist (T.pts (τ 0)) (T.pts (τ 1)) with hLdef
  set X := dist (T.pts (τ 1)) (T.pts (τ 2)) with hXdef
  set Y := dist (T.pts (τ 2)) (T.pts (τ 0)) with hYdef
  have eX : L = 2 * Real.cos β * X := by
    have h : Real.sin β * (L - 2 * Real.cos β * X) = 0 := by linear_combination l1
    have := (mul_eq_zero.mp h).resolve_left hsβ.ne'
    linarith
  have eY : L = 2 * Real.cos β * Y := by
    have h : Real.sin β * (L - 2 * Real.cos β * Y) = 0 := by linear_combination l2
    have := (mul_eq_zero.mp h).resolve_left hsβ.ne'
    linarith
  have h2c : 2 * Real.cos β ≠ 0 := by positivity
  have hXY : X = Y := mul_left_cancel₀ h2c (eX.symm.trans eY)
  have hLf : (f : ℝ) ^ 3 * L = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * X := by
    linear_combination ((f : ℝ) ^ 3) * eX + X * hc2
  have hf3 : (f : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hf0.ne'
  refine ⟨X / (f : ℝ) ^ 3, by positivity, (div_mul_cancel₀ X hf3).symm, ?_, ?_⟩
  · rw [← hXY]; exact (div_mul_cancel₀ X hf3).symm
  · rw [div_mul_eq_mul_div, eq_div_iff hf3]
    linarith

/-- **The sides of the triangle with corners `α + β, β`** (`W_s(e, f)`), given a triangle `R` with sides `ef, f² − e², f²` (for the
ratios of the sines): `|BA| = s f³`, `|AQ| = s f (f² − e²)`, `|QB| = s e (2f² − e²)`, `s > 0`. -/
theorem corners_sides_W (T R : Erdos634.Geometry.Tri) (τ : Equiv.Perm (Fin 3)) {e f : ℕ} (he : 1 ≤ e)
    (hef : e < f) (hs0 : sideOpp R 0 = (e : ℝ) * f) (hs1 : sideOpp R 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp R 2 = (f : ℝ) ^ 2)
    (hQ : cornerAngle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) =
      modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
    (hB : cornerAngle (T.pts (τ 0)) (T.pts (τ 1)) (T.pts (τ 2)) = modelBeta (e : ℝ) (f : ℝ)) :
    ∃ s : ℝ, 0 < s ∧ dist (T.pts (τ 1)) (T.pts (τ 2)) = s * (f : ℝ) ^ 3 ∧
      dist (T.pts (τ 2)) (T.pts (τ 0)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      dist (T.pts (τ 0)) (T.pts (τ 1)) = s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨l1, l2⟩ := law_sines_corners T τ hQ hB
  obtain ⟨hRa, hRb, hRc⟩ := modelAngles_of_sidesG R he hef hs0 hs1 hs2
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have d12 : dist (R.pts 1) (R.pts 2) = (e : ℝ) * f := hs0
  have d20 : dist (R.pts 2) (R.pts 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := hs1
  have d01 : dist (R.pts 0) (R.pts 1) = (f : ℝ) ^ 2 := hs2
  have r1 := EuclideanGeometry.law_sin (R.pts 0) (R.pts 1) (R.pts 2)
  have r2 := EuclideanGeometry.law_sin (R.pts 1) (R.pts 2) (R.pts 0)
  have hRa' : EuclideanGeometry.angle (R.pts 1) (R.pts 0) (R.pts 2) = modelAlpha (e : ℝ) (f : ℝ) := hRa
  have hRb' : EuclideanGeometry.angle (R.pts 2) (R.pts 1) (R.pts 0) = modelBeta (e : ℝ) (f : ℝ) := hRb
  have hRc' : EuclideanGeometry.angle (R.pts 0) (R.pts 2) (R.pts 1) =
      2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := hRc
  rw [EuclideanGeometry.angle_comm (R.pts 0) (R.pts 1) (R.pts 2), hRb',
    EuclideanGeometry.angle_comm (R.pts 2) (R.pts 0) (R.pts 1), hRa', d12, d20] at r1
  rw [EuclideanGeometry.angle_comm (R.pts 1) (R.pts 2) (R.pts 0), hRc',
    EuclideanGeometry.angle_comm (R.pts 0) (R.pts 1) (R.pts 2), hRb', d20, d01] at r2
  have hcosα := cos_modelAlpha he0 hefR
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith
  generalize modelAlpha (e : ℝ) (f : ℝ) = α at hQ hcosα hrel hα0 l1 l2 r1 r2
  generalize modelBeta (e : ℝ) (f : ℝ) = β at hQ hB hrel hb0 hb2 l1 l2 r1 r2
  have hpi := Real.pi_pos
  have hαπ : α < Real.pi := by linarith
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have h2a : Real.pi - (α + β) - β = 2 * α := by linarith
  have hγ : 2 * α + β = Real.pi - (α + β) := by linarith
  rw [h2a, Real.sin_two_mul] at l1 l2
  rw [hγ, Real.sin_pi_sub] at r2
  have hca : Real.cos α * (2 * (f : ℝ) ^ 2) = 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hcosα]; field_simp
  have hXpos : 0 < dist (T.pts (τ 1)) (T.pts (τ 2)) :=
    dist_pos.mpr (fun h => absurd (T.indep.injective h) (τ.injective.ne (by decide)))
  set L := dist (T.pts (τ 0)) (T.pts (τ 1)) with hLdef
  set X := dist (T.pts (τ 1)) (T.pts (τ 2)) with hXdef
  set Y := dist (T.pts (τ 2)) (T.pts (τ 0)) with hYdef
  -- `sin γ · a = sin α · c`
  have hGa : Real.sin (α + β) * ((e : ℝ) * f) = Real.sin α * (f : ℝ) ^ 2 := by
    have h : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        (Real.sin (α + β) * ((e : ℝ) * f) - Real.sin α * (f : ℝ) ^ 2) = 0 := by
      linear_combination ((e : ℝ) * f) * r2 + ((f : ℝ) ^ 2) * r1
    have := (mul_eq_zero.mp h).resolve_left hb.ne'
    linarith
  have hE1 : (f : ℝ) ^ 2 * L = 2 * Real.cos α * ((e : ℝ) * f) * X := by
    have h : Real.sin α * ((f : ℝ) ^ 2 * L - 2 * Real.cos α * ((e : ℝ) * f) * X) = 0 := by
      linear_combination ((e : ℝ) * f) * l1 - L * hGa
    have := (mul_eq_zero.mp h).resolve_left hsα.ne'
    linarith
  have hE2 : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * L = 2 * Real.cos α * ((e : ℝ) * f) * Y := by
    have h : Real.sin α * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * L - 2 * Real.cos α * ((e : ℝ) * f) * Y) = 0 := by
      linear_combination ((e : ℝ) * f) * l2 - L * r1
    have := (mul_eq_zero.mp h).resolve_left hsα.ne'
    linarith
  have hX : (f : ℝ) ^ 3 * L = (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * X := by
    have h : (f : ℝ) * ((f : ℝ) ^ 3 * L - (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * X) = 0 := by
      linear_combination ((f : ℝ) ^ 2) * hE1 + (((e : ℝ) * f) * X) * hca
    have := (mul_eq_zero.mp h).resolve_left hf0.ne'
    linarith
  have hY : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * L = (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * Y := by
    have h : (f : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * L
        - (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * Y) = 0 := by
      linear_combination ((f : ℝ) ^ 2) * hE2 + (((e : ℝ) * f) * Y) * hca
    have := (mul_eq_zero.mp h).resolve_left hf0.ne'
    linarith
  have hK2 : (0 : ℝ) < (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have := sq_nonneg (f : ℝ)
    exact mul_pos he0 (by linarith)
  have hf3 : (f : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hf0.ne'
  have hYX : Y * (f : ℝ) ^ 3 = (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * X := by
    have h : ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) *
        (Y * (f : ℝ) ^ 3 - (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * X) = 0 := by
      linear_combination (-((f : ℝ) ^ 3)) * hY + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hX
    have := (mul_eq_zero.mp h).resolve_left hK2.ne'
    linarith
  refine ⟨X / (f : ℝ) ^ 3, by positivity, (div_mul_cancel₀ X hf3).symm, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff hf3]
    linarith
  · rw [div_mul_eq_mul_div, eq_div_iff hf3]
    linarith

/-! ## 3. `thm:siderunall` with the corner angles -/

/-- **THEOREM `thm:siderunall`, corners `β, β`, as the paper states it.**  Let the target of the congruent dissection `D₀` (model with
the sides `ef, f² − e², f²`) have the side `[Q, B]`, `Q = target.pts (τ 0)`, `B = target.pts (τ 1)`, with the corner angles `β` at `Q` and
`β` at `B` (the angle at the third vertex `A = target.pts (τ 2)`).  Then `[Q, B]` carries `f` consecutive tiles of `D₀` that lay their
side `c` on it and show `α` at the same end of it, and `|QB| ≥ f³`. -/
theorem thm_siderunall_angles_T (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hQ : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      modelBeta (e : ℝ) (f : ℝ))
    (hB : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (e : ℝ) (f : ℝ)) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨s, hs, h1, h2, h3⟩ := corners_sides_T D₀.target τ he hef hQ hB
  obtain ⟨x₀, t, h0, hend, hrun, h3'⟩ :=
    thm_siderunall_T_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  rw [← h3] at hend h3'
  exact ⟨x₀, t, h0, hend, hrun, h3'⟩

/-- **THEOREM `thm:siderunall`, corners `α + β, β`, as the paper states it.**  Let the target of the congruent dissection `D₀` (model
with the sides `ef, f² − e², f²`) have the side `[Q, B]`, `Q = target.pts (τ 0)`, `B = target.pts (τ 1)`, with the corner angles `α + β`
at `Q` and `β` at `B`.  Then `[Q, B]` carries `f` consecutive tiles of `D₀` that lay their side `c` on it and show `α` at the same end
of it, and `|QB| ≥ f³`. -/
theorem thm_siderunall_angles_W (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hQ : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
    (hB : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (e : ℝ) (f : ℝ)) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨σm, m0, m1, m2⟩ := sideOpp_relabel_of_hasSides hMod
  obtain ⟨s, hs, h1, h2, h3⟩ := corners_sides_W D₀.target (D₀.model.relabel σm) τ he hef m0 m1 m2 hQ hB
  obtain ⟨x₀, t, h0, hend, hrun, h3'⟩ :=
    thm_siderunall_W_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  rw [← h3] at hend h3'
  exact ⟨x₀, t, h0, hend, hrun, h3'⟩

/-! ## 4. The hypotheses of the angle theorems are satisfied (no vacuity) -/

/-- the angle at the middle vertex is symmetric in the outer two -/
theorem cornerAngle_comm_G (p q r : Plane) : cornerAngle p q r = cornerAngle r q p := by
  unfold cornerAngle; exact EuclideanGeometry.angle_comm _ _ _

/-- **A real dissection satisfies the hypotheses of `thm_siderunall_angles_T`**, for every coprime member (and `e = 1`): the seed
tiling of `T_f(e, f)` (`UniformThreshold.betaTilable_self`; `WSeedG.beta_seed`) has the corner angles `β, β` at the ends of its base. -/
theorem angles_witness_T (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        modelBeta (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) := by
  obtain ⟨N, D₀, hT, hMod⟩ := Erdos634.Draft.UniformThreshold.betaTilable_self he hef
  obtain ⟨τ, h1, h2, h3⟩ := hT
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have hK3 : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hcosβ := cos_modelBeta he0 hefR
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  have hA0 : 0 < (f : ℝ) * (f : ℝ) ^ 3 := by positivity
  have hL0 : 0 < (f : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hf0 (mul_pos he0 hK3)
  have hfne : (f : ℝ) ≠ 0 := hf0.ne'
  have hene : (e : ℝ) ≠ 0 := he0.ne'
  have hK3ne : 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ 0 := hK3.ne'
  have hcos : Real.cos (modelBeta (e : ℝ) (f : ℝ)) =
      (((f : ℝ) * (f : ℝ) ^ 3) ^ 2 + ((f : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ^ 2
        - ((f : ℝ) * (f : ℝ) ^ 3) ^ 2) /
      (2 * ((f : ℝ) * (f : ℝ) ^ 3) * ((f : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))) := by
    rw [hcosβ]; unfold baseLen Nq; field_simp; try ring
  refine ⟨N, D₀, τ, hMod, ?_, ?_⟩
  · refine cornerAngle_eq_of_cosG (a := (f : ℝ) * (f : ℝ) ^ 3)
      (b := (f : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (d := (f : ℝ) * (f : ℝ) ^ 3)
      h2 (by rw [dist_comm]; exact h3) (by rw [dist_comm]; exact h1) hA0 hL0 hb0.le
      (by linarith [Real.pi_pos]) hcos
  · refine cornerAngle_eq_of_cosG (a := (f : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (b := (f : ℝ) * (f : ℝ) ^ 3) (d := (f : ℝ) * (f : ℝ) ^ 3)
      h3 (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h2) hL0 hA0 hb0.le
      (by linarith [Real.pi_pos]) ?_
    rw [hcosβ]; unfold baseLen Nq; field_simp; try ring

/-- **A real dissection satisfies the hypotheses of `thm_siderunall_angles_W`**, for every coprime member: the seed tiling of `W_f(e, f)`
(`CollarG.wTilable_seed`) has the corner angles `α + β` at `Q` and `β` at `B`. -/
theorem angles_witness_W (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) := by
  obtain ⟨D₀, hT, hMod⟩ := Erdos634.Draft.CollarG.wTilable_seed e f he hef
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have hK2 : (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hK3 : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hcosβ := cos_modelBeta he0 hefR
  have hcosα := cos_modelAlpha he0 hefR
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith
  have hpi := Real.pi_pos
  have hfne : (f : ℝ) ≠ 0 := hf0.ne'
  have hene : (e : ℝ) ≠ 0 := he0.ne'
  have hbne : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ 0 := hb.ne'
  have hK2ne : 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ 0 := hK2.ne'
  have hQB : 0 < (f : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hf0 (mul_pos he0 hK2)
  have hBA : 0 < (f : ℝ) * (f : ℝ) ^ 3 := by positivity
  have hAQ : 0 < (f : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hf0 (mul_pos hf0 hb)
  -- the angle at `B` is `β`
  have hB : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (e : ℝ) (f : ℝ) := by
    refine cornerAngle_eq_of_cosG (a := (f : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (b := (f : ℝ) * (f : ℝ) ^ 3) (d := (f : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      h3 (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h2) hQB hBA hb0.le
      (by linarith [Real.pi_pos]) ?_
    rw [hcosβ]; unfold baseLen Nq
    rw [div_eq_div_iff (by positivity) (mul_pos (mul_pos two_pos hQB) hBA).ne']
    ring
  -- the angle at `A` is `2 α`
  have hA : cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) =
      2 * modelAlpha (e : ℝ) (f : ℝ) := by
    refine cornerAngle_eq_of_cosG (a := (f : ℝ) * (f : ℝ) ^ 3)
      (b := (f : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (d := (f : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      h1 (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h3) hBA hAQ (by linarith)
      (by linarith) ?_
    rw [Real.cos_two_mul, hcosα]; field_simp; try ring
  have hsum := cornerAngle_sum (D₀.target.relabel τ)
  simp only [Tri.relabel_pts] at hsum
  have c1 := cornerAngle_comm_G (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2))
  have c2 := cornerAngle_comm_G (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
  have c3 := cornerAngle_comm_G (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
  refine ⟨_, D₀, τ, hMod, ?_, hB⟩
  rw [c3]
  linarith

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.law_sines_corners
#print axioms Erdos634.Draft.SideRunG.corners_sides_T
#print axioms Erdos634.Draft.SideRunG.corners_sides_W
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_angles_T
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_angles_W
#print axioms Erdos634.Draft.SideRunG.angles_witness_T
#print axioms Erdos634.Draft.SideRunG.angles_witness_W
