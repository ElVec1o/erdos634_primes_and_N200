/-
Draft/WGapRL16.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 step (6), "W1 lays c", THE ALTERNATIVE "K or Sigma").
Not imported by any aggregate.  No sorry, no native_decide.
`step6_c_false`: the `beta`-tile at `A_1` beside the ray `A_1 -> A_0` laying its `c`-edge there gives `K3G` for `(j+2, j+1)`; with `K2G` from the `Pi_b` data, `T+` (`Tplus_core`): `K1J` => Theorem K at the origin
(`K_at_origin`), strip tile => `SigmaCfg` of size 1 against `SigmaAll D e f 1`.
-/
import Erdos634.Draft.WGapRL15
import Erdos634.Draft.WGapKN

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

section rl16

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 8000000 in
theorem step6_c_false (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {c₀ J j : ℕ}
    (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hjf : j + 2 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J j)
    (hUall : ∀ a b : ℕ, b ≤ j → a + b ≤ 1 + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hDall : ∀ a b : ℕ, b < j → a + b + 1 ≤ 1 + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hD0 : DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (j : ℝ))
    {tN : Fin N} (hN2 : HasV D tN (p2j (e : ℝ) f (xo f c₀) j) (pA1 (e : ℝ) f (xo f c₀) j) (pB0 (e : ℝ) f (xo f c₀) j))
    (hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((j : ℝ) + 1))
    (hIH : SigmaAll D e f 1)
    {τ : Fin N} {P W : Plane} (hV : HasV D τ (pA1 (e : ℝ) f (xo f c₀) j) P W)
    (hP : ∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap (pA1 (e : ℝ) f (xo f c₀) j) (pA0 (e : ℝ) f (xo f c₀) j) s)
    (hW : cross (pA0 (e : ℝ) f (xo f c₀) j - pA1 (e : ℝ) f (xo f c₀) j) (W - pA1 (e : ℝ) f (xo f c₀) j) < 0)
    (hc : dist (pA1 (e : ℝ) f (xo f c₀) j) P = (f : ℝ) ^ 2) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  have hUy : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (j : ℝ) := hUall 0 j (le_refl _) (by omega)
  have hU0' : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0 := by
    have := hUall 0 0 (Nat.zero_le _) (by omega)
    rwa [Nat.cast_zero] at this
  have hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (j + 2) (j + 1) := by
    refine ⟨fun i j' hj' hij => ?_, fun i j' hj' hij => ?_⟩
    · rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
      · exact hUall i j' (by omega) (by omega)
      · have hje : j' = j + 1 := by omega
        subst hje
        have hi0 : i = 0 := by omega
        subst hi0
        rw [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
        exact hU01
    · rcases Nat.lt_or_ge j' j with hlt | hge
      · exact hDall i j' hlt (by omega)
      · have hje : j' = j := by omega
        subst hje
        have hi0 : i = 0 := by omega
        subst hi0
        exact hD0
  obtain ⟨s2, hs2, hP2⟩ := hP
  have hs2' : s2 * ((e : ℝ) * f) = (f : ℝ) ^ 2 := by
    have := hc
    rw [hP2, dist_left_lineMap, Real.norm_of_nonneg hs2.le, s6_dAA he0 hef _ j] at this
    exact this
  have hP2lp : P = lpG (e : ℝ) f 1 (xo f c₀) (1 - s2) ((j : ℝ) + 1 + s2) := by
    rw [hP2]
    unfold pA1 pA0
    rw [lineMap_lpG]
    exact lpG_congr (by ring) (by ring)
  obtain ⟨k, m, j3, hkm, hkj, hmj, hk, hm, hj⟩ := hV
  obtain ⟨kk, mm, jj, hkm', hkj', hmj', hk', hm', hj'⟩ := hN2
  have hsum : ((0 : ℝ) + 1 + ((j : ℝ) + 1)) = ((j + 2 : ℕ) : ℝ) := by push_cast; ring
  have hK3 : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((j + 2 : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ) := by
    right
    refine ⟨τ, k, m, j + 1, (j : ℝ) + 1 + s2, hkm, le_refl _, ?_, ?_, ?_, Or.inr ?_, ?_, ?_⟩
    · push_cast; linarith
    · rw [hk]
      exact lpG_congr (by push_cast; ring) (by push_cast; ring)
    · rw [hm, hP2lp]
      exact lpG_congr (by push_cast; ring) rfl
    · push_cast
      linear_combination hs2'
    · intro i
      rcases fin3_cover k m j3 hkm hkj hmj i with rfl | rfl | rfl
      · rw [hk]
        exact GSG_le he0 hef hε (by push_cast; linarith)
      · rw [hm, hP2lp]
        exact GSG_le he0 hef hε (by push_cast; linarith)
      · rw [hj]
        have hG := cross_mG (e := (e : ℝ)) (f := (f : ℝ)) (x := xo f c₀) hε 0 ((j : ℝ) + 1) (W - pA1 (e : ℝ) f (xo f c₀) j)
        have hlin : GSG (e : ℝ) (f : ℝ) 1 (W - pA1 (e : ℝ) f (xo f c₀) j) =
            GSG (e : ℝ) (f : ℝ) 1 W - GSG (e : ℝ) (f : ℝ) 1 (pA1 (e : ℝ) f (xo f c₀) j) := map_sub _ _ _
        have hA1 : GSG (e : ℝ) (f : ℝ) 1 (pA1 (e : ℝ) f (xo f c₀) j) = -lvG (e : ℝ) f 1 (xo f c₀) ((j + 2 : ℕ) : ℝ) := by
          unfold pA1
          rw [GSG_lp hε, hsum]
        have h1 : cross (pA0 (e : ℝ) f (xo f c₀) j - pA1 (e : ℝ) f (xo f c₀) j) (W - pA1 (e : ℝ) f (xo f c₀) j) =
            GSG (e : ℝ) (f : ℝ) 1 (W - pA1 (e : ℝ) f (xo f c₀) j) := by
          have := hG
          rw [one_mul] at this
          exact this
        linarith
    · refine clampedBelowG_of_edge he0 hef hε (η' := (j : ℝ)) (t := tN) (by push_cast; linarith) hkm' ?_ ?_ ?_
      · rw [hk']
        exact lpG_congr (by push_cast; ring) rfl
      · rw [hm']
        exact lpG_congr (by push_cast; ring) (by push_cast; ring)
      · intro i
        rcases fin3_cover kk mm jj hkm' hkj' hmj' i with rfl | rfl | rfl
        · rw [hk']; exact GSG_le he0 hef hε (by push_cast; linarith)
        · rw [hm']; exact GSG_le he0 hef hε (by push_cast; linarith)
        · rw [hj']
          exact GSG_le he0 hef hε (by have := nuG_pos he0 hef; push_cast; linarith)
  have hT := Tplus_core S hJ hS1 hUy hU01
  rcases hT with hK1 | hE1
  · exact K_at_origin S c₀ (j + 1) (fun _ => h2) hU0' hK1 1 le_rfl (j + 2) (j + 1) le_rfl (by omega) (by omega)
      (by omega) hK2 hK3
  · refine hIH c₀ J hA (j + 2) (j + 1) (by omega) (by omega) (by omega) (by omega) ⟨?_, hK2, hK3⟩
    intro y hy1 hy2
    rcases Nat.lt_or_ge y (j + 1) with hlt | hge
    · exact hS1 y hy1 (by omega)
    · have hye : y = j + 1 := by omega
      subst hye
      rw [Nat.cast_add, Nat.cast_one]
      exact hE1

end rl16

#print axioms step6_c_false

end Erdos634.Draft.WGapStmt
