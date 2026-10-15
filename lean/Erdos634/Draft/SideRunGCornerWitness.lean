/-
Draft/SideRunGCornerWitness.lean  In `AllThreshold`.  **WITNESSES** -- real dissections that satisfy the hypotheses of `thm_cornerrun` (`Draft/SideRunGCornerMainB.lean`), for every member `(e, f)`, `1 ≤ e < f`, and the theorem applied to them.

WHAT IS PROVED HERE.  The seed tilings of `W_f(e, f)` (`CollarG.wTilable_seed`, through `angles_witness_W`) and of `T_f(e, f)` (`UniformThreshold.betaTilable_self`, through `angles_witness_T`) are congruent dissections whose targets have
* `cornerrun_witness_W_AQ`: the side `A Q` of `W_f(e, f)`: the corner `2α` at `A` and `α + β` at `Q`;
* `cornerrun_witness_W_AB`: the side `A B` of `W_f(e, f)`: the corner `2α` at `A` and `β` at `B`;
* `cornerrun_witness_T`: a leg `A Q` of `T_f(e, f)`: the corner `3α` at the apex `A` and `β` at the base vertex `Q`.
The third angle of each seed target is computed from the angle sum of the triangle (`witness_angle_sum`: `π − (α + β) − β = 2α`, `π − 2β = 3α`, since `3α + 2β = π`); the other two angles are those of `angles_witness_W/T`.  The corner combination
`(3α, α + β)` has no witness among the seeds (the third angle of such a triangle is `β − α`).
`CornerRunConcl` is the conclusion (i) or (ii) of `thm_cornerrun` (the same text); `cornerrun_applied_W_AQ`, `cornerrun_applied_W_AB`, `cornerrun_applied_T` apply `thm_cornerrun` to the witnesses.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerMainB
import Erdos634.Draft.SideRunGAngles

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Set

variable {N : ℕ}

/-! ## 1. The conclusion of `thm_cornerrun` as a predicate -/

/-- **The conclusion of `thm:cornerrun`** for the side `[A', Q']` of the target of `D₀` (alternative (i) or (ii); the text of `thm_cornerrun`). -/
def CornerRunConcl (D₀ : CongruentDissection N) (e f : ℕ) (A' Q' : Plane) : Prop :=
  (∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist A' Q' ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) A' Q' (t j) Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) A' Q' (t j) Ty.C2 (x₀ + j * (f : ℝ) ^ 2)))) ∨
  (∃ (k : ℕ) (t : ℕ → Fin N), e + 1 ≤ k ∧ k ≤ f - 1 ∧
      (∀ j, j < k → LaysBaseOn D₀ (e : ℝ) (f : ℝ) A' Q' (t j) Ty.C1 ((j : ℝ) * (f : ℝ) ^ 2)) ∧
      ((k : ℝ) * (f : ℝ) ^ 2 = dist A' Q' ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) A' Q' i Ty.A2 ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) A' Q' i Ty.B2 ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) A' Q' i Ty.C2 ((k : ℝ) * (f : ℝ) ^ 2))) ∧
      (∃ T, MirrorBeside D₀ (e : ℝ) (f : ℝ) A' (t 0) T))

/-! ## 2. The third angle of a seed target -/

/-- the three corner angles of the target, at the vertices `τ 0`, `τ 1`, `τ 2`, sum to `π` -/
theorem witness_angle_sum (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) +
    cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) +
    cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = Real.pi := by
  have hsum := cornerAngle_sum (D₀.target.relabel τ)
  simp only [Erdos634.Geometry.Tri.relabel_pts] at hsum
  have c1 := cornerAngle_comm_G (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2))
  have c2 := cornerAngle_comm_G (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
  have c3 := cornerAngle_comm_G (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
  linarith

/-- the rotation `0 ↦ 2, 1 ↦ 0, 2 ↦ 1` (the side that starts at the vertex `2`, ends at the vertex `0`) -/
def rotA : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩

/-- the reflection `0 ↦ 2, 1 ↦ 1, 2 ↦ 0` (the side that starts at the vertex `2`, ends at the vertex `1`) -/
def swpA : Equiv.Perm (Fin 3) :=
  ⟨![2, 1, 0], ![2, 1, 0], fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩

/-! ## 3. The witnesses -/

/-- **WITNESS, side `A Q` of `W_f(e, f)`** (corners `2α` at `A`, `α + β` at `Q`): the seed tiling of `W_f(e, f)` (`CollarG.wTilable_seed`) satisfies the hypotheses of `thm_cornerrun`, with `A' = target.pts (τ 0)`, `Q' = target.pts (τ 1)`. -/
theorem cornerrun_witness_W_AQ (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := by
  obtain ⟨N, D₀, τ, hMod, hQ, hB⟩ := angles_witness_W e f he hef
  have hsum := witness_angle_sum D₀ τ
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  refine ⟨N, D₀, rotA.trans τ, hMod, ?_, ?_⟩
  · show cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) =
      2 * modelAlpha (e : ℝ) (f : ℝ)
    linarith
  · show cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)
    exact hQ

/-- **WITNESS, side `A B` of `W_f(e, f)`** (corners `2α` at `A`, `β` at `B`). -/
theorem cornerrun_witness_W_AB (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) := by
  obtain ⟨N, D₀, τ, hMod, hQ, hB⟩ := angles_witness_W e f he hef
  have hsum := witness_angle_sum D₀ τ
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  have c1 := cornerAngle_comm_G (D₀.target.pts (τ 0)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1))
  have c2 := cornerAngle_comm_G (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
  have c3 := cornerAngle_comm_G (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 0))
  refine ⟨N, D₀, swpA.trans τ, hMod, ?_, ?_⟩
  · show cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) =
      2 * modelAlpha (e : ℝ) (f : ℝ)
    linarith
  · show cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 0)) =
      modelBeta (e : ℝ) (f : ℝ)
    have c4 := cornerAngle_comm_G (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2))
    linarith

/-- **WITNESS, a leg `A Q` of `T_f(e, f)`** (corners `3α` at the apex `A`, `β` at the base vertex `Q`): the seed tiling of `T_f(e, f)` (`UniformThreshold.betaTilable_self`). -/
theorem cornerrun_witness_T (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) := by
  obtain ⟨N, D₀, τ, hMod, hQ, hB⟩ := angles_witness_T e f he hef
  have hsum := witness_angle_sum D₀ τ
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  refine ⟨N, D₀, rotA.trans τ, hMod, ?_, ?_⟩
  · show cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) =
      3 * modelAlpha (e : ℝ) (f : ℝ)
    linarith
  · show cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      modelBeta (e : ℝ) (f : ℝ)
    exact hQ

/-! ## 4. The theorem applied to the witnesses -/

/-- `thm_cornerrun` applied to the seed tiling of `W_f(e, f)`, side `A Q` (corners `2α`, `α + β`) -/
theorem cornerrun_applied_W_AQ (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) ∧
      CornerRunConcl D₀ e f (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨N, D₀, τ, hMod, hA, hQ⟩ := cornerrun_witness_W_AQ e f he hef
  exact ⟨N, D₀, τ, hMod, hA, hQ,
    thm_cornerrun e f he hef hco D₀ hMod τ (Or.inl hA) (Or.inr hQ)⟩

/-- `thm_cornerrun` applied to the seed tiling of `W_f(e, f)`, side `A B` (corners `2α`, `β`) -/
theorem cornerrun_applied_W_AB (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∧
      CornerRunConcl D₀ e f (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨N, D₀, τ, hMod, hA, hQ⟩ := cornerrun_witness_W_AB e f he hef
  exact ⟨N, D₀, τ, hMod, hA, hQ,
    thm_cornerrun e f he hef hco D₀ hMod τ (Or.inl hA) (Or.inl hQ)⟩

/-- `thm_cornerrun` applied to the seed tiling of `T_f(e, f)`, a leg from the apex (corners `3α`, `β`) -/
theorem cornerrun_applied_T (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
      HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ) ∧
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∧
      CornerRunConcl D₀ e f (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨N, D₀, τ, hMod, hA, hQ⟩ := cornerrun_witness_T e f he hef
  exact ⟨N, D₀, τ, hMod, hA, hQ,
    thm_cornerrun e f he hef hco D₀ hMod τ (Or.inr hA) (Or.inl hQ)⟩

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.witness_angle_sum
#print axioms Erdos634.Draft.SideRunGA.cornerrun_witness_W_AQ
#print axioms Erdos634.Draft.SideRunGA.cornerrun_witness_W_AB
#print axioms Erdos634.Draft.SideRunGA.cornerrun_witness_T
#print axioms Erdos634.Draft.SideRunGA.cornerrun_applied_W_AQ
#print axioms Erdos634.Draft.SideRunGA.cornerrun_applied_W_AB
#print axioms Erdos634.Draft.SideRunGA.cornerrun_applied_T
