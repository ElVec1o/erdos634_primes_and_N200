/-
Draft/WGapGen7.lean -- written 16 November 2026 (session 15).  UNAUDITED beyond internal checks.
Not imported by any aggregate.  No sorry, no native_decide.
CONTROLS for `rl_gen` (WGapGen6): `rl_one` (i = 1) and `rl_two` (i = 2) re-derived from `rl_gen` with their own hypothesis lists
(`rl_one_of_gen`, `rl_two_of_gen`): the hypothesis family of `rl_gen` at `t = 0` is exactly the earlier hand-instantiated one (no weaker, no stronger lattice data).
-/
import Erdos634.Draft.WGapGen6

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

section gen7

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem rl_one_of_gen (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 1 + 1 ≤ f - 1)
    {tUi tDL tUl tN tN2 : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 + 1) (j : ℝ))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x (0 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)))
    (hN2 : HasV D tN2 (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x (((1 : ℕ) : ℝ) + 1) j) < 0)
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))) : False := by
  refine rl_gen S x j 1 0 hi (by omega) ?_ ?_ ?_ hP4 hleft
  · intro t' _ ht'
    interval_cases t'
    · exact ⟨tN, hasV_congr hN (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · exact ⟨tN2, hasV_congr hN2 (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
  · intro t' _ ht'
    interval_cases t'
    · exact ⟨tUi, hasV_congr hUi (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · exact ⟨tUl, hasV_congr hUl (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
  · intro t' ht1 ht'
    obtain rfl : t' = 1 := by omega
    exact ⟨tDL, hasV_congr hDL (lpG_congr (by push_cast; ring) (by push_cast; ring))
      (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩

set_option maxHeartbeats 16000000 in
theorem rl_two_of_gen (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 2 + 1 ≤ f - 1)
    {tDa tUa tUb tNb tNa tDc tUc tNc : Fin N}
    (hDa : HasV D tDa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUa : HasV D tUa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)))
    (hUb : HasV D tUb (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1 + 1)))
    (hNb : HasV D tNb (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x (1 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)))
    (hNa : HasV D tNa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f)))
    (hDc : HasV D tDc (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1)))
    (hUc : HasV D tUc (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1)) (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1 + 1)))
    (hNc : HasV D tNc (lpG (e : ℝ) f 1 x ((0 : ℝ) + 1) ((j : ℝ) + 1 + 1)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1 + 1))
      (lpG (e : ℝ) f 1 x (0 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 1 + 2 + nuG (e : ℝ) f)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) < 0)
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 2 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))) : False := by
  refine rl_gen S x j 2 0 hi (by omega) ?_ ?_ ?_ hP4 hleft
  · intro t' _ ht'
    interval_cases t'
    · exact ⟨tNc, hasV_congr hNc (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · exact ⟨tNb, hasV_congr hNb (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · exact ⟨tNa, hasV_congr hNa (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
  · intro t' _ ht'
    interval_cases t'
    · exact ⟨tUc, hasV_congr hUc (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · exact ⟨tUb, hasV_congr hUb (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · exact ⟨tUa, hasV_congr hUa (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
  · intro t' ht1 ht'
    interval_cases t'
    · exact ⟨tDc, hasV_congr hDc (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · exact ⟨tDa, hasV_congr hDa (lpG_congr (by push_cast; ring) (by push_cast; ring))
        (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩

end gen7

#print axioms rl_one_of_gen
#print axioms rl_two_of_gen

end Erdos634.Draft.WGapStmt
