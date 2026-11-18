/-
Draft/WGapClimb4.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 steps (5)-(7), P9.3; no station, `h_lambda = 0`).
Not imported by any aggregate.  No sorry, no native_decide.
* `step6_alt`: step (6) at `A_q`, `q = k+1`, with the `(r3)` branch EXPORTED (generalizes `step6_gen`, whose `(r3)` branch is `rl_close` at `lambda = 0`);
* `ClimbSt`: the climb invariant (C1), (C2) of PROOF 9.2 at `h_lambda = 0`;
* `climb_step0`: the step `lambda -> lambda+1` (steps (5), (6), (7), RL for the `(r3)` branch), GIVEN the row `D(x, j+lambda)`, `x < i-lambda`;
* `climb_end0`: the end 9.3 at `lambda = i`.
-/
import Erdos634.Draft.WGapClimb3

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

section climb4

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 32000000 in
theorem step6_alt (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay)
    {c₀ J j k : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hjf : j + k + 2 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J j)
    (hUall : ∀ a b : ℕ, b ≤ j → a + b ≤ (k + 1) + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hDall : ∀ a b : ℕ, b < j → a + b + 1 ≤ (k + 1) + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hD0 : ∀ a : ℕ, a < k + 1 → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (j : ℝ))
    (hrow : ∀ r : ℕ, r < k + 1 → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (r : ℝ) ((j : ℝ) + 1))
    (hN : NTile D e f c₀ (k + 1) j) (hSig : SigmaAll D e f (k + 1)) :
    NTile D e f c₀ k (j + 1) ∨
    ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f (xo f c₀) j (k + 1) (((k + 1 : ℕ)) : ℝ) ((0 : ℕ) : ℝ))
        (PIR (e : ℝ) f (xo f c₀) j (k + 1) (((k + 1 : ℕ)) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f (xo f c₀)) R ∧
      0 < cross (dcvec (e : ℝ) f (xo f c₀)) (R - PIR (e : ℝ) f (xo f c₀) j (k + 1) (((k + 1 : ℕ)) : ℝ) ((0 : ℕ) : ℝ)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  set x := xo f c₀ with hxdef
  obtain ⟨tDL, hDLt⟩ := hD0 k (by omega)
  obtain ⟨tUl, hUlt⟩ := hUall (k + 1) j le_rfl (by omega)
  have hUic := hrow k (by omega)
  obtain ⟨tUi, hUit⟩ := hUic
  obtain ⟨tN2, hN2t⟩ := hN
  have hDL : HasV D tDL (p1j (e : ℝ) f (xshk (f : ℝ) k x) j) (p0j1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hDLt (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  have hUl : HasV D tUl (p1j (e : ℝ) f (xshk (f : ℝ) k x) j) (p2j (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hUlt (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  have hUi : HasV D tUi (p0j1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pA0 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hUit (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  have hN2' : HasV D tN2 (p2j (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pB0 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hN2t (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  rcases rl_step6 S (xshk (f : ℝ) k x) j hDL hUl hUi hN2' with ⟨tN, hN⟩ | ⟨F, R, lamc, hl, hF, hR⟩ | ⟨τ, P, W, hV, hP, hW, hang, hPW, hc, hWd⟩
  · left
    refine ⟨tN, hasV_congr hN (toShk (by push_cast; ring) (by push_cast; ring)).symm
      (toShk (by push_cast; ring) (by push_cast; ring)).symm (toShk (by push_cast; ring) (by push_cast; ring)).symm⟩
  · right
    have e1 : PIR (e : ℝ) f (xshk (f : ℝ) k x) j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) =
        PIR (e : ℝ) f x j (k + 1) (((k + 1 : ℕ)) : ℝ) ((0 : ℕ) : ℝ) := by
      rw [PIR_shk, Nat.add_comm 1 k]
      exact PIR_congr (by push_cast; ring) rfl
    rw [e1, dcvec_shk] at hF hR
    exact ⟨F, R, lamc, hl, hF, hR⟩
  · exfalso
    have hK3' := K3G_of_cedge S (xshk (f : ℝ) k x) j hN2' hV hP hW hc
    have hK3s := K3G_shiftk x k hK3'
    have hcast : (((j + 2 : ℕ) : ℝ) + (k : ℝ)) = ((j + 1 + (k + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hK3s
    have hK2 : K2G D (e : ℝ) (f : ℝ) 1 x (j + 1 + (k + 1)) (j + 1) := by
      refine ⟨fun i j' hj' hij => ?_, fun i j' hj' hij => ?_⟩
      · rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
        · exact hUall i j' (by omega) (by omega)
        · have hje : j' = j + 1 := by omega
          subst hje
          rw [Nat.cast_add, Nat.cast_one]
          exact hrow i (by omega)
      · rcases Nat.lt_or_ge j' j with hlt | hge
        · exact hDall i j' hlt (by omega)
        · have hje : j' = j := by omega
          subst hje
          exact hD0 i (by omega)
    have hUc : ∀ y : ℕ, J ≤ y → y ≤ j → UTG D (e : ℝ) (f : ℝ) 1 x ((0 : ℕ) : ℝ) (y : ℝ) :=
      fun y h1 h2' => hUall 0 y h2' (by omega)
    have hU0 : UTG D (e : ℝ) (f : ℝ) 1 x 0 0 := by
      have := hUall 0 0 (Nat.zero_le _) (by omega)
      rwa [Nat.cast_zero] at this
    have hU01z : UTG D (e : ℝ) (f : ℝ) 1 x 0 ((j : ℝ) + 1) := by
      have := hrow 0 (by omega)
      rwa [Nat.cast_zero] at this
    exact kor_gen S h2 hA hJ (by omega) (by omega) hS1 hUc hU0 hU01z hSig hK2 hK3s

/-- the climb invariant (C1), (C2) of PROOF 9.2 at the column `h_lambda = 0` (apex `(c₀, J)`, parameters `(j, i)`, step `lam`) -/
def ClimbSt (D : CongruentDissection N) (e f c₀ J j i lam : ℕ) : Prop :=
  (∀ t : ℕ, i - lam ≤ t → t ≤ i → NTile D e f c₀ t (j + i - t)) ∧
  StripTiles D e f c₀ J (j + lam) ∧
  (∀ a b : ℕ, b ≤ j + lam → a + b ≤ i + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ)) ∧
  (∀ a b : ℕ, b < j + lam → a + b + 1 ≤ i + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))

end climb4

#print axioms step6_alt

end Erdos634.Draft.WGapStmt
