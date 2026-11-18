/-
Draft/WGapLat.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.2 sign facts, P5).
Not imported by any aggregate.  Module W3e: lattice utilities for the wedge API, all in MIRROR coordinates (`mpG ξ η` at REAL `ξ η`).

* `dist_mpG_sq`   : `dist (mpG ξ η) (mpG ξ' η')² = QfG (ξ-ξ') (η-η')`  (the mirror preserves the Gram form).
* `cross_mpG`     : `cross (p'(a) - p'(b)) (p'(c) - p'(d)) = - κ ((a1-b1)(c2-d2) - (a2-b2)(c1-d1))`,  `κ = f² h > 0` (the mirror REVERSES orientation).
* `lineMap_mpG`   : `lineMap (p'(ξ,η)) (p'(ξ',η')) t = p'(ξ + t (ξ'-ξ), η + t (η'-η))`.
* `mpG_inj`       : `p'` is injective on `(ξ, η)`.
* `no_straddle`   : if the tiles of `K` (all with angle `< π` at `X`) carry the total `Ω - θ`, `θ < π`, no tile edge on a line through `X` straddles `X`
  (the "clamp" hypothesis of `ray_filler`, discharged by the angle count).
* `openSeg_interior`: `X ∈ int Δ`, `Y ∈ Δ` ⟹ the open segment is interior (the `hint` hypothesis of `ray_filler`).
* `interior_of_sum`: a point of `Δ` at which known tiles carry total angle `> π` is interior.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapFill
import Erdos634.Draft.WGapMirrorLat
import Erdos634.Draft.W2E1Tools

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

/-- the orientation constant `κ = f² h` of the lattice -/
noncomputable def kapG (e f : ℝ) : ℝ := f ^ 2 * hhG e f

theorem kapG_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < kapG e f := by
  have hf : 0 < f := he.trans hef
  exact mul_pos (by positivity) (hhG_pos he hef)

theorem dist_mpG_sq {e f : ℝ} (he : 0 < e) (hef : e < f) (x ξ η ξ' η' : ℝ) :
    dist (mpG e f 1 x ξ η) (mpG e f 1 x ξ' η') ^ 2 = QfG e f (ξ - ξ') (η - η') := by
  rw [dist_mp]; exact dist_lpG_sq he hef (by norm_num) _ _ _ _

theorem dist_mpG {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) {ξ η ξ' η' d : ℝ} (hd0 : 0 ≤ d)
    (hd : QfG e f (ξ - ξ') (η - η') = d ^ 2) : dist (mpG e f 1 x ξ η) (mpG e f 1 x ξ' η') = d :=
  dist_eq_of_sq_eq (by rw [dist_mpG_sq he hef, hd]) dist_nonneg hd0

theorem cross_lpG (e f x : ℝ) (a1 a2 b1 b2 c1 c2 d1 d2 : ℝ) :
    cross (lpG e f 1 x a1 a2 - lpG e f 1 x b1 b2) (lpG e f 1 x c1 c2 - lpG e f 1 x d1 d2) =
      kapG e f * ((a1 - b1) * (c2 - d2) - (a2 - b2) * (c1 - d1)) := by
  unfold lpG kapG cross
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]
  ring

theorem cross_mpG {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (a1 a2 b1 b2 c1 c2 d1 d2 : ℝ) :
    cross (mpG e f 1 x a1 a2 - mpG e f 1 x b1 b2) (mpG e f 1 x c1 c2 - mpG e f 1 x d1 d2) =
      -(kapG e f * ((a1 - b1) * (c2 - d2) - (a2 - b2) * (c1 - d1))) := by
  rw [mpG_eq he hef, mpG_eq he hef, mpG_eq he hef, mpG_eq he hef, cross_lpG]
  ring

theorem lineMap_mpG {e f : ℝ} (he : 0 < e) (hef : e < f) (x ξ η ξ' η' t : ℝ) :
    AffineMap.lineMap (mpG e f 1 x ξ η) (mpG e f 1 x ξ' η') t =
      mpG e f 1 x (ξ + t * (ξ' - ξ)) (η + t * (η' - η)) := by
  rw [mpG_eq he hef, mpG_eq he hef, mpG_eq he hef, lineMap_lpG]
  exact lpG_congr (by ring) (by ring)

theorem mpG_inj {e f : ℝ} (he : 0 < e) (hef : e < f) {x ξ η ξ' η' : ℝ}
    (h : mpG e f 1 x ξ η = mpG e f 1 x ξ' η') : ξ = ξ' ∧ η = η' := by
  rw [mpG_eq he hef, mpG_eq he hef] at h
  have h1 := lpG_xi_eq he hef (by norm_num) h
  have h2 := lpG_eta_eq he hef h
  refine ⟨by linarith, ?_⟩
  have : ξ = ξ' := by linarith
  subst this
  linarith

/-- a point of a convex target that is the endpoint of an open segment with interior endpoint -/
theorem openSeg_interior (D : Dissection N) {X Y : Plane} (hX : X ∈ interior D.target.carrier)
    (hY : Y ∈ D.target.carrier) : openSegment ℝ X Y ⊆ interior D.target.carrier := by
  have hc : Convex ℝ D.target.carrier := D.target.convex
  intro z hz
  exact hc.openSegment_interior_self_subset_interior hX hY hz

/-- **interior from a known angle total**: tiles in `K` with total local angle `> π` at a point of `Δ` force it into the interior -/
theorem interior_of_sum (D : Dissection N) {p : Plane} (hp : p ∈ D.target.carrier) (K : Finset (Fin N))
    (h : Real.pi < ∑ i ∈ K, (D.tile i).localAngle p) : p ∈ interior D.target.carrier := by
  by_contra hnot
  have hle := sum_angles_le_pi D hp hnot
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
    (f := fun i => (D.tile i).localAngle p) (fun i _ _ => Tri.localAngle_nonneg _ _)
  linarith

/-- **the clamp from the angle count** (`hclamp` of `ray_filler`).  `K` carries `Ω - θ` with `θ < π`, all members of `K` have angle `< π` at `X`. -/
theorem no_straddle (D : Dissection N) {X Y P' : Plane} (hXY : X ≠ Y)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    {Ω θ : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - θ) (hθ : θ < Real.pi)
    (hKlt : ∀ k ∈ K, (D.tile k).localAngle X < Real.pi) :
    ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y := by
  intro ed hed hs
  have hu : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
  have hF := crossL_ne_zero hu
  have hfX : crossL (Y - X) X = cross (Y - X) X := crossL_apply _ _
  have hfY : crossL (Y - X) Y = cross (Y - X) X := by
    rw [crossL_apply]
    have : cross (Y - X) Y = cross (Y - X) (Y - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this]; simp [cross]; ring
  have hfP' : crossL (Y - X) P' = cross (Y - X) X := by
    rw [crossL_apply]
    have : cross (Y - X) P' = cross (Y - X) (P' - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this, hP']; ring
  obtain ⟨-, hang, -⟩ := straddle_data D (crossL (Y - X)) hF (cross (Y - X) X) hXY hfX hfY hfP' hXP hed hs
  have hnot : ed.1 ∉ K := fun hm => absurd (hKlt _ hm) (by rw [hang]; exact lt_irrefl _)
  have hsd := Finset.sum_sdiff (Finset.subset_univ K) (f := fun i => (D.tile i).localAngle X)
  have hle : (D.tile ed.1).localAngle X ≤ ∑ i ∈ Finset.univ \ K, (D.tile i).localAngle X :=
    Finset.single_le_sum (f := fun i => (D.tile i).localAngle X) (fun j _ => Tri.localAngle_nonneg _ _)
      (by simp [hnot])
  rw [hang] at hle
  have h1 : ∑ i, (D.tile i).localAngle X = Ω := hΩ
  have h2 : ∑ i ∈ K, (D.tile i).localAngle X = Ω - θ := hK
  simp only at hsd
  linarith

/-- negative control: a point with `θ = π` is not excluded (the hypothesis `θ < π` is used) -/
example : ¬ (Real.pi < Real.pi) := lt_irrefl _

#print axioms mpG_inj
#print axioms no_straddle

end Erdos634.Draft.WGapStmt
