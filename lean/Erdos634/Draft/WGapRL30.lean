/-
Draft/WGapRL30.lean -- written 16 November 2026 (session 14).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 step (2) at `i = 2`, `lambda = 1`; RL(2,1) = `rl_one` at the column 1).
Not imported by any aggregate.  No sorry, no native_decide.
* `hasV_lp`: a lattice-coordinate rewriting of `HasV`.
* `noN_mirror2`: `N_i(j0)` and `N_{i+1}(j0)` tiles (with the lattice tiles at `X = p(i+1,j0+1)`) give the mirror tile at the origin `p(i+1,0)`.
* `rl_one_sh`: `rl_one` at the shifted origin `x + f^2`, with the hypotheses read at `x` (this is `RL(i=2,t=1)`).
* `lam1_N_false`: `S_0 = N_0(j+1)` is impossible (PROOF 9.4 (2), `i = 2`).
-/
import Erdos634.Draft.WGapRL29

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

theorem hasV_lp {x e f : ℝ} {t : Fin N} {a1 b1 a2 b2 a3 b3 a1' b1' a2' b2' a3' b3' : ℝ}
    (h : HasV D t (lpG e f 1 x a1 b1) (lpG e f 1 x a2 b2) (lpG e f 1 x a3 b3))
    (h1 : a1 = a1') (h2 : b1 = b1') (h3 : a2 = a2') (h4 : b2 = b2') (h5 : a3 = a3') (h6 : b3 = b3') :
    HasV D t (lpG e f 1 x a1' b1') (lpG e f 1 x a2' b2') (lpG e f 1 x a3' b3') :=
  hasV_congr h (lpG_congr h1 h2) (lpG_congr h3 h4) (lpG_congr h5 h6)

section rl30

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem noN_mirror2 (S : SetupG D e f α β γ L ax ay) (x : ℝ) {i : ℕ} {η : ℝ} (hη : 0 ≤ η)
    {tDL tUl tDl tUr tUi tN tN1 : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) η) (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) η) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) η)
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) η) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) (η + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
      (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1 + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f)))
    (hN1 : HasV D tN1 (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f))) :
    MirrorAt D (e : ℝ) f 1 (shiftX (f : ℝ) 1 x (i + 1)) (η + 1) := by
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hcl : ∃ P' : Plane, FXG (e : ℝ) f 1 P' = lvG (e : ℝ) f 1 x ((i : ℝ) + 1) ∧
      lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) f 1) (lvG (e : ℝ) f 1 x ((i : ℝ) + 1)),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
          (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) := by
    have hle : ∀ i', FXG (e : ℝ) f 1 ((D.tile tDL).pts i') ≤ lvG (e : ℝ) f 1 x ((i : ℝ) + 1) := by
      refine hDL.all (P := fun p => FXG (e : ℝ) f 1 p ≤ lvG (e : ℝ) f 1 x ((i : ℝ) + 1))
        (le_of_eq (FXG_lp hε1 _ _)) ?_ (le_of_eq (FXG_lp hε1 _ _))
      dsimp only
      rw [FXG_lp hε1]
      exact lvG_le he0 hef (by linarith)
    obtain ⟨k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hDL
    exact clamp_tile S hε1 hkj hk hj hle
  have hL : lpG (e : ℝ) f 1 x ((i : ℝ) + 1 - 1) (η + 1) ∈ D.target.carrier := by
    rw [show ((i : ℝ) + 1 - 1) = (i : ℝ) by ring]
    exact hUi.mem₁
  have hint := bedge_interior C (c := (i : ℝ) + 1) (η := η + 1) (by linarith) hUr hL
  have hE := col_next S hε1 hUr hint hcl
  rcases hE with ⟨iT, k, m, t, hkm, hk, hm, ht, hlen, hle⟩ | ⟨iT, k, m, hkm, hk, hm, hle⟩
  · exfalso
    exact colnext_first_false S x hDL hUl hDl hUr hUi hN hN1 hkm hk hm ht hlen hle
  · have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hnγ' : (D.tile iT).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) ≠ γ := by
      intro hγ0
      exact noN_gamma_int S hε1 hDL hUl hDl hUr hUi hN hle hγ0
    exact mirror_of_b_n S hε1 (n := i + 1) (η := η + 1) hkm (by rw [hcast]; exact hk) (by rw [hcast]; exact hm)
      (by rw [hcast]; exact hle) (by rw [hcast]; exact hnγ')

/-- `RL(i=2,t=1)` = `rl_one` at the origin shifted by one column -/
theorem rl_one_sh (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 2 + 1 ≤ f - 1)
    {tDa tUa tUb tNb tNa : Fin N}
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
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) < 0)
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f (xsh1 (f : ℝ) x) j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))
        (PIR (e : ℝ) f (xsh1 (f : ℝ) x) j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f (xsh1 (f : ℝ) x)) R ∧
      0 < cross (dcvec (e : ℝ) f (xsh1 (f : ℝ) x)) (R - PIR (e : ℝ) f (xsh1 (f : ℝ) x) j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))) :
    False := by
  have he0 := S.e0
  have hef := S.hef'
  have hDL : HasV D tDa (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) 0 ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1) ((j : ℝ) + 1)) :=
    hasV_congr hDa (toSh (by ring) rfl) (toSh (by ring) rfl) (toSh (by ring) rfl)
  have hUl : HasV D tUa (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1 + 1) (j : ℝ))
      (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1) ((j : ℝ) + 1)) :=
    hasV_congr hUa (toSh (by ring) rfl) (toSh (by ring) rfl) (toSh (by ring) rfl)
  have hUi : HasV D tUb (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) 0 ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) 0 ((j : ℝ) + 1 + 1)) :=
    hasV_congr hUb (toSh (by ring) rfl) (toSh (by ring) rfl) (toSh (by ring) rfl)
  have hN : HasV D tNb (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) 0 ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (0 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)) :=
    hasV_congr hNb (toSh (by ring) rfl) (toSh (by ring) rfl) (toSh (by ring) rfl)
  have hN2 : HasV D tNa (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) ((0 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f)) :=
    hasV_congr hNa (toSh (by ring) rfl) (toSh (by ring) rfl) (toSh (by ring) rfl)
  obtain ⟨F4, R4, hF4, hc4⟩ := hP4
  have hP4' : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) -
            lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) -
          lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) + 1) j) < 0 := by
    have q1 : lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) + 1) j = lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j := by
      rw [lpG_sh1]; exact lpG_congr (by push_cast; ring) rfl
    have q2 : lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (((1 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) =
        lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) := by
      rw [lpG_sh1]; exact lpG_congr (by push_cast; ring) rfl
    rw [q1, q2]
    exact ⟨F4, R4, hF4, hc4⟩
  exact rl_one S (xsh1 (f : ℝ) x) j (by omega) hDL hUl hUi hN hN2 hP4' hleft

set_option maxHeartbeats 16000000 in
/-- `S_0 = N_0(j+1)` is impossible (PROOF 9.4 (2) at `i = 2`, `lambda = 1`) -/
theorem lam1_N_false (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 2 + 1 ≤ f - 1)
    {tDL tUl tDl tUr tUi tN tN1 tUa tNa : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((0 : ℕ) : ℝ) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1 + 1) (j : ℝ))
      (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1 + 1) ((j : ℝ) + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1 + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x ((0 : ℕ) : ℝ) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((0 : ℕ) : ℝ) ((j : ℝ) + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((0 : ℕ) : ℝ) ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)))
    (hN1 : HasV D tN1 (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1 + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1) ((j : ℝ) + 1 + 1))
      (lpG (e : ℝ) f 1 x (((0 : ℕ) : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)))
    (hUa : HasV D tUa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)))
    (hNa : HasV D tNa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) < 0) :
    False := by
  have he0 := S.e0
  have hef := S.hef'
  have hmir := noN_mirror2 S x (i := 0) (η := (j : ℝ)) (Nat.cast_nonneg j) hDL hUl hDl hUr hUi hN hN1
  have hshx : shiftX (f : ℝ) 1 x (0 + 1) = xsh1 (f : ℝ) x := by
    unfold shiftX xsh1; push_cast; ring
  rw [hshx] at hmir
  obtain ⟨tE, hE⟩ := (mirrorAt_iff_UTM_gen S _ _).1 hmir
  -- the pieces at the shifted origin
  have hUi' : HasV D tUr (p0j1 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA1 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA0 (e : ℝ) f (xsh1 (f : ℝ) x) j) :=
    hasV_congr hUr (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl)
  have hN0' : HasV D tN1 (pA1 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA0 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pC0 (e : ℝ) f (xsh1 (f : ℝ) x) j) :=
    hasV_congr hN1 (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl)
  obtain ⟨F, R, lamc, hl, hF, hR⟩ := rl_A0_fill S (xsh1 (f : ℝ) x) j hE hUi' hN0'
  refine rl_one_sh S x j hi (tDa := tDl) (tUa := tUa) (tUb := tUr) (tNb := tN1) (tNa := tNa) ?_ hUa ?_ ?_ hNa hP4
    ⟨F, R, lamc, hl, hF, hR⟩
  · exact hasV_lp hDl (by push_cast; ring) rfl (by push_cast; ring) rfl (by push_cast; ring) rfl
  · exact hasV_lp hUr (by push_cast; ring) rfl (by push_cast; ring) rfl (by push_cast; ring) rfl
  · exact hasV_lp hN1 (by push_cast; ring) rfl (by push_cast; ring) rfl (by push_cast; ring) rfl

end rl30

#print axioms noN_mirror2
#print axioms rl_one_sh
#print axioms lam1_N_false

end Erdos634.Draft.WGapStmt
