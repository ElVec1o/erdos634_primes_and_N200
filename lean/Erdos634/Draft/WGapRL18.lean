/-
Draft/WGapRL18.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 at `i = 1`, `lambda = 0`; P9.3 at `lambda = 1`).
Not imported by any aggregate.  No sorry, no native_decide.
`prop_B_one`: **Proposition B at `i = 1`**: given `Sigma[1]`, `Pi_b^a(j, 1)` does not occur.  Steps: (5) `row_up_one` (`U(0,j+1)`); (6) `rl_step6`: `N_0(j+1)` | `(r3)` at `t = 1` (`rl_close`) | `c`-edge (`step6_c_false`);
(7) `Tplus_core` + `N_at_origin` (Lemma N with `i_N = 0`): `T+` is the strip tile; `rl_A0_fill` gives `(r3)` at `t = 0`; `rl_one`.
-/
import Erdos634.Draft.WGapRL17

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

section rl18

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 8000000 in
theorem prop_B_one (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J : ℕ} (hA : IsApex D e f c₀ J) {j : ℕ} (hJ : J ≤ j) (hij : 1 + j + 1 ≤ f - 1)
    (hSig : SigmaAll D e f 1) : ¬ PiBCfg D e f c₀ J j 1 := by
  rintro ⟨hS1, hUall, hDall, hD0, hN1, hP4⟩
  have he0 := S.e0
  have hef := S.hef'
  have hi : 1 + 1 ≤ f - 1 := by omega
  have hD0' : DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (j : ℝ) := hD0 0 (by omega)
  have hUy : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (j : ℝ) := hUall 0 j (le_refl _) (by omega)
  have hU0' : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0 := by
    have := hUall 0 0 (Nat.zero_le _) (by omega)
    rwa [Nat.cast_zero] at this
  have hU01 := row_up_one S h2 hH4 hA hJ (by omega) hS1
    (fun y h1 h2' => hUall 0 y h2' (by omega)) hD0' hN1
  -- the tiles in the form of `rl_step6`
  obtain ⟨tDL, hDLt⟩ := hD0'
  obtain ⟨tUl, hUlt⟩ := hUall 1 j (by omega) (by omega)
  obtain ⟨tUi, hUi⟩ := hU01
  obtain ⟨tN2, hN2t⟩ := hN1
  have hDL : HasV D tDL (p1j (e : ℝ) f (xo f c₀) j) (p0j1 (e : ℝ) f (xo f c₀) j) (pA1 (e : ℝ) f (xo f c₀) j) := by
    rw [Nat.cast_zero] at hDLt; exact hDLt
  have hUl : HasV D tUl (p1j (e : ℝ) f (xo f c₀) j) (p2j (e : ℝ) f (xo f c₀) j) (pA1 (e : ℝ) f (xo f c₀) j) :=
    hasV_congr hUlt (lpG_congr (by norm_num) rfl) (lpG_congr (by norm_num) rfl) (lpG_congr (by norm_num) rfl)
  have hN2 : HasV D tN2 (p2j (e : ℝ) f (xo f c₀) j) (pA1 (e : ℝ) f (xo f c₀) j) (pB0 (e : ℝ) f (xo f c₀) j) :=
    hasV_congr hN2t (lpG_congr (by norm_num) rfl) (lpG_congr (by norm_num) rfl) (lpG_congr (by norm_num) rfl)
  have hD0'' : DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (j : ℝ) := ⟨tDL, hDLt⟩
  have hU01' : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((j : ℝ) + 1) := ⟨tUi, hUi⟩
  have hN1PIR : ∃ T : Fin N, HasV D T (PIR (e : ℝ) f (xo f c₀) j 1 (1 + 1) 0) (PIR (e : ℝ) f (xo f c₀) j 1 1 0)
      (PIR (e : ℝ) f (xo f c₀) j 1 1 1) :=
    ⟨tN2, hasV_PIR he0 hef hN2 (by ring) (by push_cast; ring) (by ring) (by push_cast; ring) (by ring) (by push_cast; ring)⟩
  rcases rl_step6 S (xo f c₀) j hDL hUl hUi hN2 with ⟨tN0, hN0⟩ | hleft1 | ⟨τ, P, W, hV, hP, hW, hang, hPW, hc, hWd⟩
  · -- `N_0(j+1)` is a tile: `T+` is the strip tile (Lemma N), then `rl_A0_fill` and `rl_one`
    rcases Tplus_core S hJ hS1 hUy hU01' with hK1 | hE1
    · exfalso
      refine N_at_origin S c₀ (j + 1) (fun _ => h2) hU0' hK1 0 (j + 1) le_rfl (by omega) ?_ ?_ ?_ ?_
      · intro i' j'' hj'' hij''
        rcases Nat.lt_or_ge j'' (j + 1) with hlt | hge
        · exact hUall i' j'' (by omega) (by omega)
        · have hje : j'' = j + 1 := by omega
          subst hje
          have hi0 : i' = 0 := by omega
          subst hi0
          rw [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
          exact hU01'
      · intro i' j'' hj'' hij''
        rcases Nat.lt_or_ge j'' j with hlt | hge
        · exact hDall i' j'' hlt (by omega)
        · have hje : j'' = j := by omega
          subst hje
          have hi0 : i' = 0 := by omega
          subst hi0
          exact ⟨tDL, hDLt⟩
      · intro m' hm1 hm2
        omega
      · exact ⟨tN0, hasV_congr hN0 (lpG_congr (by push_cast; ring) (by push_cast; ring))
          (lpG_congr (by push_cast; ring) (by push_cast; ring)) (lpG_congr (by push_cast; ring) (by push_cast; ring))⟩
    · obtain ⟨tE, hE0⟩ := hE1
      obtain ⟨F, R, lamc, hl, hF, hR⟩ := rl_A0_fill S (xo f c₀) j hE0 hUi hN0
      exact rl_one S (xo f c₀) j hi hDL hUl hUi hN0 hN2 hP4 ⟨F, R, lamc, hl, hF, hR⟩
  · -- (r3) at `t = 1`: `rl_close` with `tau = 1`, `m = 0`
    obtain ⟨T1, hT1⟩ := hN1PIR
    have hnuA : ∀ m' : ℕ, m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f (xo f c₀) j 1 (((1 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f (xo f c₀) j 1 (((1 : ℕ) : ℝ) - m') m')
          (PIR (e : ℝ) f (xo f c₀) j 1 (((1 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
      intro m' hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    have hnuB : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f (xo f c₀) j 1 (((1 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f (xo f c₀) j 1 ((1 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f (xo f c₀) j 1 ((1 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    exact rl_close S (xo f c₀) j 1 1 0 0 (by omega) (by omega) hi (by omega) hnuA hP4 hnuB hleft1
  · -- the `c`-edge: `K` or `Sigma`
    exact step6_c_false S h2 hA hJ (by omega) hS1 hUall hDall ⟨tDL, hDLt⟩ hN2 hU01' hSig hV hP hW hc

end rl18

#print axioms prop_B_one

end Erdos634.Draft.WGapStmt
