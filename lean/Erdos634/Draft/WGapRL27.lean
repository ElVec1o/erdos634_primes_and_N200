/-
Draft/WGapRL27.lean -- written 16 November 2026 (session 14).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 step (6) at `i = 2`).
Not imported by any aggregate.  No sorry, no native_decide.
Infrastructure for the column shift `x1 = x + f^2` (`lpG x1 ξ η = lpG x (ξ+1) η`), so that the `i = 1` lemmas (`rl_step6`, `rl_one`, ...) can be used at the column `1`:
`lpG_sh1`, `lvG_sh1`, `dcvec_sh1`, `PIR_sh1`, `hasV_toSh`, `hasV_ofSh`, `K3G_of_cedge` (the `K3G` construction of `step6_c_false` for an arbitrary lattice origin),
`K3G_shift1` (`K3G` at `x1` for `s` is `K3G` at `x` for `s+1`), `kor_two` (K or Sigma of size 2).
-/
import Erdos634.Draft.WGapRL26

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

/-- the origin shifted by one column -/
noncomputable def xsh1 (f x : ℝ) : ℝ := x + 1 * 1 * f ^ 2

theorem lpG_sh1 (e f x ξ η : ℝ) : lpG e f 1 (xsh1 f x) ξ η = lpG e f 1 x (ξ + 1) η :=
  Erdos634.Draft.WGapStmt.lpG_shift e f 1 x 1 ξ η

theorem lvG_sh1 {e f : ℝ} (x r : ℝ) : lvG e f 1 (xsh1 f x) r = lvG e f 1 x (1 + r) := by
  unfold xsh1 lvG
  ring

theorem dcvec_sh1 (e f x : ℝ) : dcvec e f (xsh1 f x) = dcvec e f x := by
  unfold dcvec
  rw [lpG_sh1, lpG_sh1]
  unfold lpG
  ext i
  fin_cases i <;> simp [mkPt_zero, mkPt_one] <;> ring

theorem PIR_sh1 (e f x : ℝ) (j i : ℕ) (t m : ℝ) :
    PIR e f (xsh1 f x) j i t m = PIR e f x j (i + 1) (t + 1) m := by
  unfold PIR
  rw [lpG_sh1]
  exact lpG_congr (by ring) (by push_cast; ring)

theorem hasV_toSh {e f x : ℝ} {t : Fin N} {a1 b1 a2 b2 a3 b3 a1' a2' a3' : ℝ}
    (h : HasV D t (lpG e f 1 x a1 b1) (lpG e f 1 x a2 b2) (lpG e f 1 x a3 b3))
    (h1 : a1 = a1' + 1) (h2 : a2 = a2' + 1) (h3 : a3 = a3' + 1) :
    HasV D t (lpG e f 1 (xsh1 f x) a1' b1) (lpG e f 1 (xsh1 f x) a2' b2) (lpG e f 1 (xsh1 f x) a3' b3) := by
  rw [lpG_sh1, lpG_sh1, lpG_sh1]
  rw [h1, h2, h3] at h
  exact h

theorem hasV_ofSh {e f x : ℝ} {t : Fin N} {a1 b1 a2 b2 a3 b3 a1' a2' a3' : ℝ}
    (h : HasV D t (lpG e f 1 (xsh1 f x) a1' b1) (lpG e f 1 (xsh1 f x) a2' b2) (lpG e f 1 (xsh1 f x) a3' b3))
    (h1 : a1 = a1' + 1) (h2 : a2 = a2' + 1) (h3 : a3 = a3' + 1) :
    HasV D t (lpG e f 1 x a1 b1) (lpG e f 1 x a2 b2) (lpG e f 1 x a3 b3) := by
  rw [lpG_sh1, lpG_sh1, lpG_sh1] at h
  rw [h1, h2, h3]
  exact h

section rl27

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem clampedBelowG_sh1 {s η₁ : ℝ} (x : ℝ) (h : ClampedBelowG D (e : ℝ) (f : ℝ) 1 (xsh1 (f : ℝ) x) s η₁) :
    ClampedBelowG D (e : ℝ) (f : ℝ) 1 x (s + 1) η₁ := by
  obtain ⟨η', hη, hc⟩ := h
  refine ⟨η', hη, fun Q hQ hmem ed hed => ?_⟩
  have e1 : lvG (e : ℝ) f 1 (xsh1 (f : ℝ) x) s = lvG (e : ℝ) f 1 x (s + 1) := by
    rw [lvG_sh1, add_comm]
  have p1 : lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (s - η₁) η₁ = lpG (e : ℝ) f 1 x (s + 1 - η₁) η₁ :=
    by rw [lpG_sh1]; exact lpG_congr (by ring) rfl
  have p2 : lpG (e : ℝ) f 1 (xsh1 (f : ℝ) x) (s - η') η' = lpG (e : ℝ) f 1 x (s + 1 - η') η' :=
    by rw [lpG_sh1]; exact lpG_congr (by ring) rfl
  rw [e1, p1, p2] at hc
  exact hc Q hQ hmem ed hed

theorem K3G_shift1 {s j0 : ℝ} (x : ℝ) (h : K3G D (e : ℝ) (f : ℝ) 1 (xsh1 (f : ℝ) x) s j0) :
    K3G D (e : ℝ) (f : ℝ) 1 x (s + 1) j0 := by
  have e1 : lvG (e : ℝ) f 1 (xsh1 (f : ℝ) x) s = lvG (e : ℝ) f 1 x (s + 1) := by
    rw [lvG_sh1, add_comm]
  rcases h with h | ⟨w, k, m, η₁, η₂, hkm, h1, h2, hk, hm, hl, hle, hc⟩
  · left
    rw [e1] at h
    exact h
  · right
    refine ⟨w, k, m, η₁, η₂, hkm, h1, h2, ?_, ?_, hl, ?_, clampedBelowG_sh1 x hc⟩
    · rw [hk, lpG_sh1]; exact lpG_congr (by ring) rfl
    · rw [hm, lpG_sh1]; exact lpG_congr (by ring) rfl
    · intro i
      have := hle i
      rw [e1] at this
      exact this

set_option maxHeartbeats 8000000 in
/-- the `K3G` construction of `step6_c_false` for an arbitrary lattice origin `x` -/
theorem K3G_of_cedge (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ)
    {tN : Fin N} (hN2 : HasV D tN (p2j (e : ℝ) f x j) (pA1 (e : ℝ) f x j) (pB0 (e : ℝ) f x j))
    {τ : Fin N} {P W : Plane} (hV : HasV D τ (pA1 (e : ℝ) f x j) P W)
    (hP : ∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap (pA1 (e : ℝ) f x j) (pA0 (e : ℝ) f x j) s)
    (hW : cross (pA0 (e : ℝ) f x j - pA1 (e : ℝ) f x j) (W - pA1 (e : ℝ) f x j) < 0)
    (hc : dist (pA1 (e : ℝ) f x j) P = (f : ℝ) ^ 2) :
    K3G D (e : ℝ) (f : ℝ) 1 x ((j + 2 : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  obtain ⟨s2, hs2, hP2⟩ := hP
  have hs2' : s2 * ((e : ℝ) * f) = (f : ℝ) ^ 2 := by
    have := hc
    rw [hP2, dist_left_lineMap, Real.norm_of_nonneg hs2.le, s6_dAA he0 hef _ j] at this
    exact this
  have hP2lp : P = lpG (e : ℝ) f 1 x (1 - s2) ((j : ℝ) + 1 + s2) := by
    rw [hP2]
    unfold pA1 pA0
    rw [lineMap_lpG]
    exact lpG_congr (by ring) (by ring)
  obtain ⟨k, m, j3, hkm, hkj, hmj, hk, hm, hj⟩ := hV
  obtain ⟨kk, mm, jj, hkm', hkj', hmj', hk', hm', hj'⟩ := hN2
  have hsum : ((0 : ℝ) + 1 + ((j : ℝ) + 1)) = ((j + 2 : ℕ) : ℝ) := by push_cast; ring
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
      have hG := cross_mG (e := (e : ℝ)) (f := (f : ℝ)) (x := x) hε 0 ((j : ℝ) + 1) (W - pA1 (e : ℝ) f x j)
      have hlin : GSG (e : ℝ) (f : ℝ) 1 (W - pA1 (e : ℝ) f x j) =
          GSG (e : ℝ) (f : ℝ) 1 W - GSG (e : ℝ) (f : ℝ) 1 (pA1 (e : ℝ) f x j) := map_sub _ _ _
      have hA1 : GSG (e : ℝ) (f : ℝ) 1 (pA1 (e : ℝ) f x j) = -lvG (e : ℝ) f 1 x ((j + 2 : ℕ) : ℝ) := by
        unfold pA1
        rw [GSG_lp hε, hsum]
      have h1 : cross (pA0 (e : ℝ) f x j - pA1 (e : ℝ) f x j) (W - pA1 (e : ℝ) f x j) =
          GSG (e : ℝ) (f : ℝ) 1 (W - pA1 (e : ℝ) f x j) := by
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

/-- "K or Sigma" of size 2 at the row `y₀+1`: the pair `(y₀+3, y₀+1)` with `(K2)`, `(K3)` cannot occur (`T⁺`: `K1J` or the strip tile). -/
theorem kor_two (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {c₀ J y₀ : ℕ}
    (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hjf : y₀ + 3 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J y₀)
    (hUc : ∀ y : ℕ, J ≤ y → y ≤ y₀ → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y : ℝ))
    (hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0)
    (hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
    (hIH : SigmaAll D e f 2)
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (y₀ + 3) (y₀ + 1))
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((y₀ + 3 : ℕ) : ℝ) ((y₀ + 1 : ℕ) : ℝ)) : False := by
  have hUy := hUc y₀ hJ le_rfl
  rcases Tplus_core S hJ hS1 hUy hU01 with hK1 | hE1
  · exact K_at_origin S c₀ (y₀ + 1) (fun _ => h2) hU0 hK1 2 (by norm_num) (y₀ + 3) (y₀ + 1) le_rfl (by omega) (by omega)
      (by omega) hK2 hK3
  · refine hIH c₀ J hA (y₀ + 3) (y₀ + 1) (by omega) (by omega) (by omega) (by omega) ⟨?_, hK2, hK3⟩
    intro y hy1 hy2
    rcases Nat.lt_or_ge y (y₀ + 1) with hlt | hge
    · exact hS1 y hy1 (by omega)
    · have hye : y = y₀ + 1 := by omega
      subst hye
      rw [Nat.cast_add, Nat.cast_one]
      exact hE1

end rl27

#print axioms lpG_sh1
#print axioms dcvec_sh1
#print axioms PIR_sh1
#print axioms hasV_toSh
#print axioms K3G_shift1
#print axioms K3G_of_cedge
#print axioms kor_two

end Erdos634.Draft.WGapStmt
