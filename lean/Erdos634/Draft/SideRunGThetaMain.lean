/-
Draft/SideRunGThetaMain.lean  Part of `AllThreshold`.  The statement for an arbitrary dissection.

**The side theorem for a side with the angle `α + β` at both ends, for an arbitrary `CongruentDissection`**, with the triangle given by its
side lengths (`thm_side_theta`, `thm_side_theta_pinned`) and by its corner angles (`thm_side_theta_angles`, as `SideRunGAngles.thm_siderunall_angles_*`).

Statement.  `1 ≤ e < f` coprime, `(a, b, c) = (ef, f² − e², f²)`, angles `α, β, γ` opposite `a, b, c`.  Let `Δ` be a triangle with a side `s` that has the angle `α + β` at both
corners, cut into congruent triangles with sides `(a, b, c)`.  Then `s` carries `f` consecutive tiles of type `C_1` or `f` of type `C_2` (tiles that lay their side `c` on `s` and show `α` at the same end); in particular `|s| ≥ f³`.

THE LEAN STATEMENTS.  `Δ` is the target of a `CongruentDissection D₀` whose model has the sides `ef, f² − e², f²` (`HasSides`); the vertices of `Δ` are named by a permutation `τ` of `Fin 3`: `τ 0 = Q`, `τ 1 = B` (the ends of `s`), `τ 2 = A`.
* `thm_side_theta_angles`: hypotheses `cornerAngle A Q B = α + β` and `cornerAngle Q B A = α + β` (with `α = modelAlpha e f`, `β = modelBeta e f`); conclusion: the run of `f` tiles of `D₀` on `[Q, B]` (`LaysBaseOn`) with `f³ ≤ |QB|`.
* `thm_side_theta_pinned`: the triangle `θ_s(e, f)` (legs `s f (f² − e²)`, base `s e (f² − e²)`, real `s > 0`) given by its side lengths, vertices named; `thm_side_theta`: the sides in any vertex order (`HasSides`).
* `theta_word_pinned`, `theta_word_hasSides`: the counts on the side: naturals `x, y, z` with `x (e f) + y (f² − e²) + z f² = s e (f² − e²)` and `f ≤ z`.
* `corners_sides_theta`: the sides of `Δ` from its corners, by the law of sines (the model triangle supplies the ratio `sin (α + β) : sin α = f : e`): `|BA| = |AQ| = s f b`, `|QB| = s e b`.
* `setup_of_sides_apex_pinned`, `setup_theta_pinned`: the normal form `SetupG` on `Q = (0,0)`, `B = (L, 0)`, `A = (s b e / 2, s b rt / 2)`, `L = s e b` (`setup_of_sidesG_pinned` with a general apex), with `CornersT`.
* `theta_pullback`: the run for the original dissection (`SideRunGMain.siderunall_pullback` with `CornersT`).
* Witnesses: `Draft/ThetaKill.lean` (the kernel-checked tilings of `θ_4(1,2)` and `θ_8(2,3)` satisfy every hypothesis of `thm_side_theta`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGThetaRules
import Erdos634.Draft.SideRunGAngles

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGT

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.TilePlacement Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.W2E1 Erdos634.Draft.SideRun
  Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA Set

variable {N : ℕ}

/-! ## 1. The normal form with a general apex -/

/-- **THE NORMAL FORM, general apex, vertices named** (`setup_of_sidesG_pinned` with an arbitrary apex `(ax, ay)`): a congruent dissection `D₀` whose target has `dist (τ 1, τ 2) = d₁`, `dist (τ 2, τ 0) = d₂`, `dist (τ 0, τ 1) = L`, the sides of the triangle
`Q = (0, 0)`, `B = (L, 0)`, `A = (ax, ay)`, and whose model has the sides `ef`, `f² − e²`, `f²` gives, after an isometry `g`, a `SetupG` on that triangle, with `g (τ 0) = Q`, `g (τ 1) = B`. -/
theorem setup_of_sides_apex_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    {L ax ay d₁ d₂ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d₁)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d₂)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧ g (D₀.target.pts (τ 1)) = mkPt L 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L ax ay := by
  have h12 : dist ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 2) = d₁ := hd₁
  have h20 : dist ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 0) = d₂ := hd₂
  have h01 : dist ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 1) = L := by
    show dist (mkPt 0 0) (mkPt L 0) = L
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  obtain ⟨g, hg0⟩ := exists_iso_of_dist3 (T := D₀.target.relabel τ) (U := Tg L ax ay hL hay)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h3.trans h01.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h1.trans h12.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h2.trans h20.symm)
  have hg : ∀ k, g (D₀.target.pts k) = (Tg L ax ay hL hay).pts (τ.symm k) := by
    intro k
    have := hg0 (τ.symm k)
    rwa [Tri.relabel_pts, Equiv.apply_symm_apply] at this
  obtain ⟨σm, m0, m1, m2⟩ := sideOpp_relabel_of_hasSides hMod
  have hmod : D₀.model.Congruent (D₀.model.relabel σm) := Tri.congruent_relabel D₀.model σm
  have hMD := modelDataG_of_sides (Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod) he hef m0 m1 m2
  exact ⟨Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod, g, fun _ _ => rfl, hg0 0, hg0 1,
    ⟨he, hef, hco, hMD, angleData_model e f he hef, hL, hay,
      fun _ _ => Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod⟩⟩

/-- **The normal form of a dissection of `θ_s(e, f)`**, vertices named (`τ 0` is `Q`, `τ 1` is `B`, `τ 2` the apex `A`): legs `s f (f² − e²)`, base `s e (f² − e²)`, any real `s > 0`.  The apex is `(s b e / 2, s b rt / 2)` and the corners are `α + β`, `α + β`. -/
theorem setup_theta_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (ax ay : ℝ),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧
      g (D₀.target.pts (τ 1)) = mkPt (s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
        (s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay ∧
      CornersT e f (s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have hr := rtG_sq he0 hefR
  have hrp := rtG_pos he0 hefR
  have ht' : 0 < s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2 := by have := mul_pos hs hb; linarith
  have hL : 0 < s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hb)
  have hay : 0 < (s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2) * rtG (e : ℝ) (f : ℝ) := mul_pos ht' hrp
  have hd₁ : dist (mkPt (s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))  0)
      (mkPt ((s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2) * (e : ℝ))
        ((s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2) * rtG (e : ℝ) (f : ℝ)))
      = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt]
    linear_combination (s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2) ^ 2 * hr
  have hd₂ : dist (mkPt ((s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2) * (e : ℝ))
        ((s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2) * rtG (e : ℝ) (f : ℝ))) (mkPt 0 0)
      = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt]
    linear_combination (s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2) ^ 2 * hr
  obtain ⟨D, g, hD, hP, hB, S⟩ := setup_of_sides_apex_pinned e f he hef hco hL hay hd₁ hd₂ D₀ τ h1 h2 h3 hMod
  exact ⟨D, g, _, _, hD, hP, hB, S,
    ⟨⟨s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2, ht', rfl, rfl⟩,
     ⟨s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2, ht', by ring, rfl⟩⟩⟩

/-! ## 2. The run for the original dissection -/

/-- **THE RUN, for the original dissection** (`SideRunGMain.siderunall_pullback` with `CornersT`): from a `SetupG` with `CornersT` that is the normal form of `D₀`, the side `[P, B]` of the target of `D₀` carries `f` consecutive tiles of `D₀` that lay a base `c` on it and show `α` at
the same end, and `f³ ≤ |PB|`. -/
theorem theta_pullback {e f : ℕ} {D₀ D : CongruentDissection N} {g : Plane ≃ᵢ Plane} {k₀ k₁ : Fin 3}
    {α β γ L ax ay : ℝ} (hL : 0 < L) (hD : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m))
    (hP : g (D₀.target.pts k₀) = mkPt 0 0) (hB : g (D₀.target.pts k₁) = mkPt L 0)
    (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ L ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ L := by
  obtain ⟨x₀, t, h0, hend, hrun, h3⟩ := side_theorem_paperT S Co
  refine ⟨x₀, t, h0, hend, ?_, h3⟩
  rcases hrun with hr | hr
  · exact Or.inl (fun j hj => laysOn_of_baseTile hL hD hP hB (hr j hj))
  · exact Or.inr (fun j hj => laysOn_of_baseTile hL hD hP hB (hr j hj))

/-! ## 3. S7 for an arbitrary congruent dissection -/

/-- **S7 (SIDE-θ), the triangle `θ_s(e, f)` given by its side lengths, vertices named** (`τ 0 = Q`, `τ 1 = B`, `τ 2` the apex; legs `s f (f² − e²)`, base `s e (f² − e²)`, any real `s > 0`): in every congruent dissection of it into copies of `(ef, f² − e², f²)` (any number of tiles,
reflections allowed) the base carries `f` consecutive tiles that lay their side `c` on it and show `α` at the same end of it, and the base has length at least `f³`. -/
theorem thm_side_theta_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_theta_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hb := b_posG he0 hefR
  have hL : 0 < s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hb)
  exact theta_pullback hL hD hP hB S Co

/-- **S7, the counts** (what S8 consumes): in every congruent dissection of `θ_s(e, f)` (vertices named) there are naturals `x, y, z` with `x (e f) + y (f² − e²) + z f² = s e (f² − e²)` and `f ≤ z`. -/
theorem theta_word_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 =
      s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧ f ≤ z := by
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_theta_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  exact theta_counts S Co

/-- **S7, the triangle `θ_s(e, f)` given by its side lengths**, in any vertex order: the base (the side of length `s e (f² − e²)`) carries `f` consecutive tiles that lay their side `c` on it and show `α` at the same end, and has length at least `f³`. -/
theorem thm_side_theta (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target (s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (k₀ k₁ : Fin 3) (x₀ : ℝ) (t : ℕ → Fin N), k₀ ≠ k₁ ∧
      dist (D₀.target.pts k₀) (D₀.target.pts k₁) = s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨τ, h1, h2, h3⟩ := hT
  obtain ⟨x₀, t, h0, hend, hrun, h3'⟩ := thm_side_theta_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  exact ⟨τ 0, τ 1, x₀, t, τ.injective.ne (by decide), h3, h0, hend, hrun, h3'⟩

/-- **S7, the counts, in any vertex order** -/
theorem theta_word_hasSides (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target (s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 =
      s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧ f ≤ z := by
  obtain ⟨τ, h1, h2, h3⟩ := hT
  exact theta_word_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod

/-! ## 4. S7 with the corner angles -/

/-- **The sides of the triangle with corners `α + β, α + β`** (`θ_s(e, f)`), given a triangle `R` with sides `ef, f² − e², f²` (for the ratio of the sines `sin (α + β) : sin α = f : e`): `|BA| = |AQ| = s f (f² − e²)`, `|QB| = s e (f² − e²)`, `s > 0`. -/
theorem corners_sides_theta (T R : Erdos634.Geometry.Tri) (τ : Equiv.Perm (Fin 3)) {e f : ℕ} (he : 1 ≤ e)
    (hef : e < f) (hs0 : sideOpp R 0 = (e : ℝ) * f) (hs1 : sideOpp R 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp R 2 = (f : ℝ) ^ 2)
    (hQ : cornerAngle (T.pts (τ 2)) (T.pts (τ 0)) (T.pts (τ 1)) =
      modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
    (hB : cornerAngle (T.pts (τ 0)) (T.pts (τ 1)) (T.pts (τ 2)) =
      modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    ∃ s : ℝ, 0 < s ∧ dist (T.pts (τ 1)) (T.pts (τ 2)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      dist (T.pts (τ 2)) (T.pts (τ 0)) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      dist (T.pts (τ 0)) (T.pts (τ 1)) = s * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
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
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith
  generalize modelAlpha (e : ℝ) (f : ℝ) = α at hQ hB hrel hα0 l1 l2 r1 r2
  generalize modelBeta (e : ℝ) (f : ℝ) = β at hQ hB hrel hb0 hb2 l1 l2 r1 r2
  have hpi := Real.pi_pos
  have hαπ : α < Real.pi := by linarith
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have h2a : Real.pi - (α + β) - (α + β) = α := by linarith
  have hγ : 2 * α + β = Real.pi - (α + β) := by linarith
  rw [h2a] at l1 l2
  rw [hγ, Real.sin_pi_sub] at r2
  have hLpos : 0 < dist (T.pts (τ 0)) (T.pts (τ 1)) :=
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
  -- `f L = e X`, `f L = e Y`
  have hX : (f : ℝ) * L = (e : ℝ) * X := by
    have h : Real.sin α * ((f : ℝ) * ((f : ℝ) * L - (e : ℝ) * X)) = 0 := by
      linear_combination ((e : ℝ) * f) * l1 - L * hGa
    have h' := (mul_eq_zero.mp h).resolve_left hsα.ne'
    have h'' := (mul_eq_zero.mp h').resolve_left hf0.ne'
    linarith
  have hY : (f : ℝ) * L = (e : ℝ) * Y := by
    have h : Real.sin α * ((f : ℝ) * ((f : ℝ) * L - (e : ℝ) * Y)) = 0 := by
      linear_combination ((e : ℝ) * f) * l2 - L * hGa
    have h' := (mul_eq_zero.mp h).resolve_left hsα.ne'
    have h'' := (mul_eq_zero.mp h').resolve_left hf0.ne'
    linarith
  have heb : (e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ≠ 0 := (mul_pos he0 hb).ne'
  refine ⟨L / ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)), div_pos hLpos (mul_pos he0 hb), ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_comm, div_eq_iff heb]
    linear_combination ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * hX
  · rw [div_mul_eq_mul_div, eq_comm, div_eq_iff heb]
    linear_combination ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * hY
  · exact (div_mul_cancel₀ L heb).symm

/-- **S7 (SIDE-θ) as the paper states it.**  Let the target of the congruent dissection `D₀` (model with the sides `ef, f² − e², f²`) have the side `[Q, B]`, `Q = target.pts (τ 0)`, `B = target.pts (τ 1)`, with the corner angles `α + β` at `Q` and `α + β` at `B`.  Then `[Q, B]`
carries `f` consecutive tiles of `D₀` that lay their side `c` on it and show `α` at the same end of it, and `|QB| ≥ f³`. -/
theorem thm_side_theta_angles (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hQ : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
    (hB : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨σm, m0, m1, m2⟩ := sideOpp_relabel_of_hasSides hMod
  obtain ⟨s, hs, h1, h2, h3⟩ := corners_sides_theta D₀.target (D₀.model.relabel σm) τ he hef m0 m1 m2 hQ hB
  obtain ⟨x₀, t, h0, hend, hrun, h3'⟩ :=
    thm_side_theta_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  rw [← h3] at hend h3'
  exact ⟨x₀, t, h0, hend, hrun, h3'⟩

end Erdos634.Draft.SideRunGT

#print axioms Erdos634.Draft.SideRunGT.setup_of_sides_apex_pinned
#print axioms Erdos634.Draft.SideRunGT.setup_theta_pinned
#print axioms Erdos634.Draft.SideRunGT.theta_pullback
#print axioms Erdos634.Draft.SideRunGT.thm_side_theta_pinned
#print axioms Erdos634.Draft.SideRunGT.theta_word_pinned
#print axioms Erdos634.Draft.SideRunGT.thm_side_theta
#print axioms Erdos634.Draft.SideRunGT.theta_word_hasSides
#print axioms Erdos634.Draft.SideRunGT.corners_sides_theta
#print axioms Erdos634.Draft.SideRunGT.thm_side_theta_angles
