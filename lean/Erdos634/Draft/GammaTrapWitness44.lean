import Erdos634.Draft.ApexWitness44
import Erdos634.GammaTrap
import Erdos634.WallThird
import Erdos634.WallDir

/-!
# `congruentDissection_gammatrap` applied to the real 44-tiling

Every hypothesis of `GammaTrap.congruentDissection_gammatrap` is discharged on `D44 := Tiling44Bridge.dissection.relabelModel τ` at `k = 1`,
and the conclusion is extracted.

**What it says.** The side `[pts 1, pts 2]` of the 44-target (length `128`, a LEG; `β` at `pts 1`,
the apex `3α` at `pts 2`) carries a tile edge of length `sideOpp D44.model 2 = 32` (the model's
`c`-side), with both endpoints on that side.

**Scope.** The hypotheses are `hcornerbase : β at pts k` and
`hcornerapex : 3α at pts (k+1)`.  So the theorem applies to the β-to-apex leg only.  Counterexample
checks: for the base side `k = 0` (β at both ends) `hcornerapex` is FALSE
(`base_side_hcornerapex_false`); for the apex-to-β leg `k = 2`, `hcornerbase` is FALSE
(`apex_to_beta_leg_hcornerbase_false`).  Both reduce to `β ≠ 3α` (`5α = π` would be rational).

This is a satisfiability and scope check for an existing theorem.
-/

namespace Erdos634.Draft.GammaTrapWitness44

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.Z15Real Erdos634.Tiling44Bridge
  Erdos634.BaseBetaTargetCoord Erdos634.SideWall Erdos634.TilePlacement
open Erdos634.Draft.ApexWitness44

/-- `hdirab` is automatic for `dirFun`: it increases from `pts k` to `pts (k+1)` (by `sideOpp > 0`). -/
theorem dirFun_mono (T : Tri) (k : Fin 3) :
    (dirFun T k).linear (T.pts k) ≤ (dirFun T k).linear (T.pts (k + 1)) := by
  have h := AffineMap.linearMap_vsub (dirFun T k) (T.pts (k + 1)) (T.pts k)
  simp only [vsub_eq_sub, map_sub] at h
  have hS : 0 < sideOpp T (k + 2) := by
    unfold sideOpp
    exact dist_pos.mpr
      (Erdos634.TilePlacement.pts_ne T (show (k+2+1:Fin 3) ≠ k+2+2 from by fin_cases k <;> decide))
  have hne : k + 1 ≠ k := by fin_cases k <;> decide
  have e1 : T.basis.coord (k+1) (T.pts (k+1)) = 1 := T.basis.coord_apply_eq (k+1)
  have e0 : T.basis.coord (k+1) (T.pts k) = 0 := T.basis.coord_apply_ne hne
  have h2 : dirFun T k (T.pts (k + 1)) - dirFun T k (T.pts k) = sideOpp T (k + 2) := by
    show sideOpp T (k+2) * T.basis.coord (k+1) (T.pts (k+1))
      - sideOpp T (k+2) * T.basis.coord (k+1) (T.pts k) = _
    rw [e1, e0]; ring
  linarith

theorem model_s0 : sideOpp D44.model 0 = 16 := by
  show dist ((pieceTri headI_mem_tiles).pts (τ 1)) ((pieceTri headI_mem_tiles).pts (τ 2)) = 16
  rw [τ1, τ2]; exact piece_d01

theorem model_s1 : sideOpp D44.model 1 = 24 := by
  show dist ((pieceTri headI_mem_tiles).pts (τ 2)) ((pieceTri headI_mem_tiles).pts (τ 0)) = 24
  rw [τ2, τ0]; exact piece_d12

theorem model_s2 : sideOpp D44.model 2 = 32 := by
  show dist ((pieceTri headI_mem_tiles).pts (τ 0)) ((pieceTri headI_mem_tiles).pts (τ 1)) = 32
  rw [τ0, τ1]; exact piece_d20

theorem D44_scalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D44.model m ≠ sideOpp D44.model m' := by
  intro m m' h
  fin_cases m <;> fin_cases m' <;> simp_all [model_s0, model_s1, model_s2]

/-- β at target vertex `1` (the inner `hb1` of `D44_hcorner`, re-proved since it is not exported). -/
theorem tgt_hb1 : cornerAngle (targetTri.pts 2) (targetTri.pts 1) (targetTri.pts 0)
    = modelBeta 1 ((2 : ℕ) : ℝ) := by
  have h1 : dist (targetTri.pts 2) (targetTri.pts 1) = 128 := by rw [dist_comm]; exact tgt_d12
  refine cornerAngle_eq_of_cos (a := 128) (b := 176) (d := 128) h1 tgt_d01 tgt_d20
    (by norm_num) (by norm_num) beta_bounds.1 beta_bounds.2 ?_
  rw [cos_beta12]
  norm_num

/-- β at target vertex `0`. -/
theorem tgt_hb0 : cornerAngle (targetTri.pts 1) (targetTri.pts 0) (targetTri.pts 2)
    = modelBeta 1 ((2 : ℕ) : ℝ) := by
  have h1 : dist (targetTri.pts 1) (targetTri.pts 0) = 176 := by rw [dist_comm]; exact tgt_d01
  refine cornerAngle_eq_of_cos (a := 176) (b := 128) (d := 128) h1 tgt_d20 tgt_d12
    (by norm_num) (by norm_num) beta_bounds.1 beta_bounds.2 ?_
  rw [cos_beta12]; norm_num

theorem angle_bundle : MarchSlots.AngleData (modelAlpha 1 ((2 : ℕ) : ℝ))
    (modelBeta 1 ((2 : ℕ) : ℝ)) (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) := by
  -- same statement as `angleData_member 1 2` (there with `((1:ℕ):ℝ)`); `D44_angleData` is the
  -- `E1NormalForm.angleData_model` form with the literal `1`, syntactically matching `D44_hα`.
  exact D44_angleData

theorem beta_ne_three_alpha : modelBeta 1 ((2 : ℕ) : ℝ) ≠ 3 * modelAlpha 1 ((2 : ℕ) : ℝ) := by
  intro h
  have hrel := angle_bundle.hrel
  exact angle_bundle.hirr ⟨1 / 9, by
    have hq : (((1 / 9 : ℚ)) : ℝ) = 1 / 9 := by norm_num
    rw [hq]
    have h9 : Real.pi = 9 * modelAlpha 1 ((2 : ℕ) : ℝ) := by rw [← hrel, h]; ring
    rw [h9]; ring⟩

/-- **Base side.** For the base side `k = 0` (β at both ends) the hypothesis
`hcornerapex` (3α at `pts (k+1)`) is FALSE. -/
theorem base_side_hcornerapex_false :
    ¬ cornerAngle (D44.target.pts (0 + 1 + 1)) (D44.target.pts (0 + 1)) (D44.target.pts (0 + 1 + 2))
        = 3 * modelAlpha 1 ((2 : ℕ) : ℝ) := by
  intro h
  have hb : cornerAngle (D44.target.pts (0 + 1 + 1)) (D44.target.pts (0 + 1))
      (D44.target.pts (0 + 1 + 2)) = modelBeta 1 ((2 : ℕ) : ℝ) := tgt_hb1
  exact beta_ne_three_alpha (hb.symm.trans h)

/-- ... while the other hypothesis `hcornerbase` (β at `pts 0`) does hold at `k = 0`: the base
fails only at the apex end. -/
theorem base_side_hcornerbase_true :
    cornerAngle (D44.target.pts (0 + 1)) (D44.target.pts 0) (D44.target.pts (0 + 2))
      = modelBeta 1 ((2 : ℕ) : ℝ) := tgt_hb0

/-- **Apex-to-β leg, `k = 2`.** `hcornerbase` (β at `pts 2`) is FALSE: `pts 2`
is the apex, with `3α`. -/
theorem apex_to_beta_leg_hcornerbase_false :
    ¬ cornerAngle (D44.target.pts (2 + 1)) (D44.target.pts 2) (D44.target.pts (2 + 2))
        = modelBeta 1 ((2 : ℕ) : ℝ) := by
  intro h
  exact beta_ne_three_alpha (h.symm.trans D44_hcorner)

theorem hN44 : 0 < Tiling44.tiles.length := by decide

/-- **`congruentDissection_gammatrap` on the real 44-tiling, `k = 1`** (β at `pts 1`, apex `3α` at
`pts 2`): some wall edge of a tile has the model's `c`-length. -/
theorem D44_gammatrap :
    ∃ p ∈ Erdos634.BaseChain.wallList D44.toDissection (wallFun D44.target 1) 0,
      dist ((D44.tile p.1).pts p.2) ((D44.tile p.1).pts (p.2 + 1)) = sideOpp D44.model 2 := by
  have hA := angle_bundle
  have h1 := hA.hα
  have h2 := hA.hβ
  have h3 := hA.hγdef
  have h4 := hA.hrel
  have h5 := Real.pi_pos
  exact congruentDissection_gammatrap hN44 D44 _ _ _
    hA.hαβ (by intro h; linarith) (by intro h; linarith) h1.ne'
    (by intro h; linarith) (by intro h; linarith) h2.ne'
    (by intro h; linarith) (by intro h; linarith) Real.pi_ne_zero
    h3 h4 hA.hirr D44_scalene
    D44_hα D44_hβ D44_hγ 1 (dirFun D44.target 1).linear (hker_wallFun D44.target 1)
    (dirFun_mono D44.target 1)
    (hthird_general D44.toDissection (wallFun D44.target 1) 0 (wallFun_linear_ne_zero D44.target 1)
      (fun y hy => by simpa using wallFun_le D44.target 1 hy))
    tgt_hb1 D44_hcorner

/-- **The extracted conclusion.** The leg `[pts 1, pts 2]` of the 44-target (length 128, from the β
corner to the apex) carries a tile edge of length `32 = c`, whose two endpoints both lie on that
leg. -/
theorem D44_leg_has_c_edge :
    dist (D44.target.pts 1) (D44.target.pts 2) = 128 ∧
    ∃ i j, (D44.tile i).pts j ∈ segment ℝ (D44.target.pts 1) (D44.target.pts (1 + 1)) ∧
      (D44.tile i).pts (j + 1) ∈ segment ℝ (D44.target.pts 1) (D44.target.pts (1 + 1)) ∧
      dist ((D44.tile i).pts j) ((D44.tile i).pts (j + 1)) = 32 := by
  refine ⟨tgt_d12, ?_⟩
  obtain ⟨⟨i, j⟩, hp, hd⟩ := D44_gammatrap
  rw [Erdos634.BaseChain.mem_wallList] at hp
  obtain ⟨h0, h1⟩ := hp
  refine ⟨i, j, ?_, ?_, by rw [hd]; exact model_s2⟩
  · exact hface_wallFun D44.target 1 _
      (tile_subset_target D44.toDissection i (subset_convexHull ℝ _ (Set.mem_range_self j))) h0
  · exact hface_wallFun D44.target 1 _
      (tile_subset_target D44.toDissection i (subset_convexHull ℝ _ (Set.mem_range_self (j+1)))) h1

#print axioms D44_gammatrap
#print axioms D44_leg_has_c_edge
#print axioms base_side_hcornerapex_false
#print axioms apex_to_beta_leg_hcornerbase_false

end Erdos634.Draft.GammaTrapWitness44
