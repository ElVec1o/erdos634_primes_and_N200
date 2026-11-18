/-
Draft/WGapClimb5.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 steps (5)-(7), P9.3; no station).
Not imported by any aggregate.  No sorry, no native_decide.
* `climb_step0`: `ClimbSt lam` and the row `D(x, j+lam)`, `x < i-lam`, give `ClimbSt (lam+1)` (steps (5), (6), (7); the `(r3)` branch of (6) is `rl_nat` at `t = i - lam`; the `c`-edge branch is `kor_gen`);
* `climb_end0`: `ClimbSt i` (with `j + i >= 1`) and `Pi4` give `False` (PROOF 9.3 at `h = 0 = i - lambda`: `rl_A0_fill` and `rl_nat` at `t = 0`).
-/
import Erdos634.Draft.WGapClimb4

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

section climb5

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 32000000 in
theorem climb_step0 (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J j i lam : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j + lam) (hij : i + j + 1 ≤ f - 1) (hlam : lam < i)
    (hSt : ClimbSt D e f c₀ J j i lam)
    (hrowD : ∀ x : ℕ, x < i - lam → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) ((j + lam : ℕ) : ℝ))
    (hP4 : Pi4 D e f c₀ i j) (hSig : SigmaAll D e f i) :
    ClimbSt D e f c₀ J j i (lam + 1) := by
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hSt
  obtain ⟨k, hk⟩ : ∃ k, i = lam + k + 1 := ⟨i - lam - 1, by omega⟩
  have hUall' : ∀ a b : ℕ, b ≤ j + lam → a + b ≤ (k + 1) + (j + lam) →
      UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ) := fun a b hb hab => hUa a b hb (by omega)
  have hDall' : ∀ a b : ℕ, b < j + lam → a + b + 1 ≤ (k + 1) + (j + lam) →
      DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ) := fun a b hb hab => hDa a b hb (by omega)
  have hD0' : ∀ a : ℕ, a < k + 1 → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) ((j + lam : ℕ) : ℝ) :=
    fun a ha => hrowD a (by omega)
  have hN' : NTile D e f c₀ (k + 1) (j + lam) := by
    have := hC1 (k + 1) (by omega) (by omega)
    have e1 : j + i - (k + 1) = j + lam := by omega
    rw [e1] at this
    exact this
  have hSigk : SigmaAll D e f k := fun c J' hA' s y hJ' hy hsf hs hσ => hSig c J' hA' s y hJ' hy hsf (by omega) hσ
  have hSigk1 : SigmaAll D e f (k + 1) := fun c J' hA' s y hJ' hy hsf hs hσ => hSig c J' hA' s y hJ' hy hsf (by omega) hσ
  have hrow := row_gen S h2 hH4 hA (by omega : J ≤ j + lam) (by omega) hS1 hUall' hDall' hD0' hN' hSigk
  rcases step6_alt S h2 hA (by omega : J ≤ j + lam) (by omega) hS1 hUall' hDall' hD0' hrow hN' hSigk1 with hN1 | ⟨F, R, lamc, hl, hF, hR⟩
  swap
  · -- `(r3)` at `t = k + 1 = i - lam`: Lemma RL
    exfalso
    rw [PIR_lvlk] at hF hR
    have hik : k + 1 + lam = i := by omega
    rw [hik] at hF hR
    refine rl_nat S c₀ j i (k + 1) (by omega) (by omega) ?_ ?_ ?_ hP4 ⟨F, R, lamc, hl, hF, hR⟩
    · intro t' h1 h2'
      exact hC1 t' (by omega) h2'
    · intro t' h1 h2'
      exact hUa t' (j + i - t') (by omega) (by omega)
    · intro t' h1 h2'
      exact hDa (t' - 1) (j + i - t') (by omega) (by omega)
  · -- step (7): `T⁺` is the strip tile
    have hUc : ∀ y : ℕ, J ≤ y → y ≤ j + lam → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y : ℝ) :=
      fun y h1 h2' => hUa 0 y h2' (by omega)
    have hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0 := by
      have := hUa 0 0 (Nat.zero_le _) (by omega)
      rwa [Nat.cast_zero] at this
    have hU01z : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 (((j + lam : ℕ) : ℝ) + 1) := by
      have := hrow 0 (by omega)
      rwa [Nat.cast_zero] at this
    have hE1 : UTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 (((j + lam : ℕ) : ℝ) + 1) := by
      rcases Tplus_core S (by omega : J ≤ j + lam) hS1 (hUc (j + lam) (by omega) le_rfl) hU01z with hK1 | hE
      · exfalso
        refine N_at_origin S c₀ (j + lam + 1) (fun _ => h2) hU0 hK1 k (j + lam + 1) le_rfl (by omega) ?_ ?_ ?_ hN1
        · intro i' j'' hj'' hij''
          rcases Nat.lt_or_ge j'' (j + lam + 1) with hlt | hge
          · exact hUa i' j'' (by omega) (by omega)
          · have hje : j'' = j + lam + 1 := by omega
            subst hje
            have := hrow i' (by omega)
            rw [show (((j + lam + 1 : ℕ)) : ℝ) = ((j + lam : ℕ) : ℝ) + 1 by push_cast; ring]
            exact this
        · intro i' j'' hj'' hij''
          rcases Nat.lt_or_ge j'' (j + lam) with hlt | hge
          · exact hDa i' j'' hlt (by omega)
          · have hje : j'' = j + lam := by omega
            subst hje
            exact hD0' i' (by omega)
        · intro m' hm1 hm2
          exact K_at_origin S c₀ (j + lam + 1) (fun _ => h2) hU0 hK1 m' hm1
      · exact hE
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t h1 h2'
      rcases Nat.lt_or_ge t (i - lam) with hlt | hge
      · have htk : t = k := by omega
        subst htk
        have e1 : j + i - t = j + lam + 1 := by omega
        rw [e1]
        exact hN1
      · exact hC1 t hge h2'
    · intro y hy1 hy2
      rcases Nat.lt_or_ge y (j + lam + 1) with hlt | hge
      · exact hS1 y hy1 (by omega)
      · have hye : y = j + lam + 1 := by omega
        subst hye
        rw [Nat.cast_add (j + lam) 1, Nat.cast_one]
        exact hE1
    · intro a b hb hab
      rcases Nat.lt_or_ge b (j + lam + 1) with hlt | hge
      · exact hUa a b (by omega) hab
      · have hbe : b = j + lam + 1 := by omega
        subst hbe
        have := hrow a (by omega)
        rw [show (((j + lam + 1 : ℕ)) : ℝ) = ((j + lam : ℕ) : ℝ) + 1 by push_cast; ring]
        exact this
    · intro a b hb hab
      rcases Nat.lt_or_ge b (j + lam) with hlt | hge
      · exact hDa a b hlt hab
      · have hbe : b = j + lam := by omega
        subst hbe
        exact hD0' a (by omega)

end climb5

#print axioms climb_step0

end Erdos634.Draft.WGapStmt
