/-
Draft/OrientMonoSide.lean -- orientation monotonicity on a side of the target of a real dissection.

`AEdgeReading.side_word_monotone` proves that a whole side of the target consisting of `a`-edges has an orientation
word of the form `GB^j BG^k`, under the wall hypotheses of the side.  Here those hypotheses are discharged for the
side `k` of the target of ANY congruent dissection (`SideWall.wallFun`, `WallDir.dirFun`):

    theorem orient_mono_side : (every edge of side k is an a-edge) → the word of side k is GB^j BG^k'

The target is arbitrary; in particular it may be the tile inflated by `f` (a triangle similar to the tile), whose
`a`-side consists of `a`-edges at the members considered.  `AEdgeReading.a_edge_west_east` is the clause that
each tile presents `β` at one end of its `a`-edge and `γ` at the other.  No sorry, no native_decide.
-/
import Erdos634.AEdgeReading
import Erdos634.WallThird
import Erdos634.WallDir
import Erdos634.SideWall

namespace Erdos634.Draft.OrientMonoSide

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.Inflation Erdos634.TilePlacement Erdos634.SideWall
open Erdos634.BaseChain Erdos634.OrientWord Erdos634.Placement

variable {N : ℕ}

/-- the direction functional increases from `pts k` to `pts (k+1)` -/
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

/-- **`prop:orientmono`.**  In a congruent dissection by a tile with angles `α, β, γ` (`3α + 2β = π`,
`γ = 2α + β`, scalene), if every tile edge on side `k` of the target is an `a`-edge, the orientation word of that
side is `GB^j BG^k'`: no `BG` is followed by a `GB`, and there is at most one transition. -/
theorem orient_mono_side (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαpos : 0 < α) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hγeq : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi) (k : Fin 3)
    (hlen : ∀ p ∈ wallList D.toDissection (wallFun D.target k) 0,
      dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 0) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n j k' : ℕ,
      n = (wallList D.toDissection (wallFun D.target k) 0).length ∧ j + k' = n ∧
      (word n (fun m => Erdos634.OrientBridge.tileOrient D.toDissection β (E m).1
        (edgeWest D.toDissection (dirFun D.target k).linear (E m)))) =
        List.replicate j Orient.GB ++ List.replicate k' Orient.BG := by
  have hab : D.target.pts k ≠ D.target.pts (k + 1) := by
    have h : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact Erdos634.TilePlacement.pts_ne D.target (h k)
  have hwall : ∀ y ∈ D.target.carrier, wallFun D.target k y ≤ 0 :=
    fun y hy => wallFun_le D.target k hy
  have hbase : segment ℝ (D.target.pts k) (D.target.pts (k+1)) ⊆ frontier D.target.carrier := by
    intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  have hline : ∀ y ∈ segment ℝ (D.target.pts k) (D.target.pts (k+1)), wallFun D.target k y = 0 := by
    intro y hy
    exact wallFun_eq_zero D.target k (by rw [Tri.edge]; exact hy)
  have hvertt : ∀ j : Fin 3, D.target.pts j = D.target.pts k ∨ D.target.pts j = D.target.pts (k+1) ∨
      wallFun D.target k (D.target.pts j) < 0 := by
    intro j
    have hj : ∀ k j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by decide
    rcases hj k j with rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right
      have e1 : D.target.basis.coord (k+2) (D.target.pts (k+2)) = 1 :=
        D.target.basis.coord_apply_eq (k+2)
      show -(D.target.basis.coord (k + 2) (D.target.pts (k + 2))) < 0
      rw [e1]; norm_num
  exact Erdos634.AEdgeReading.side_word_monotone D (wallFun D.target k) 0 α β γ hα' hβ' hγ' hscalene
    hαpos hαβ hαγ hβγ hγeq hπ D.toDissection.pos (dirFun D.target k).linear
    (hker_wallFun D.target k) hwall _ _ hab (dirFun_mono D.target k) hbase hline
    (hface_wallFun D.target k)
    (hthird_general D.toDissection (wallFun D.target k) 0 (wallFun_linear_ne_zero D.target k) hwall)
    hvertt hlen

end Erdos634.Draft.OrientMonoSide

#print axioms Erdos634.Draft.OrientMonoSide.orient_mono_side
