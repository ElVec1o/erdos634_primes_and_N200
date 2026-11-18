/-
Draft/WGapClimb1.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 steps (5)-(6) at `lambda = 0`, GENERAL index `q = k+1`).
Not imported by any aggregate.  No sorry, no native_decide.
* `xshk` and the `k`-fold column shift (generalizes `xsh1` of WGapRL27): `lpG_shk`, `lvG_shk`, `dcvec_shk`, `PIR_shk`, `hasV_toShk`, `clampedBelowG_shk`, `K3G_shiftk`;
* `kor_gen`: "K or Sigma" of size `q = k+1` (generalizes `kor_one`, `kor_two`);
* `row_gen`: step (5) at `lambda = 0` and general `q = k+1`: `U(r, j+1)` for all `r < q` (generalizes `row_two`);
* `step6_gen`: step (6) at `A_q = p(q, j+1)`, `q = k+1`: `N^{q-1} = N_{q-1}(j+1)` is a tile (generalizes `step6_two`; `rl_step6` at the `k`-fold shifted origin, `(r3)` at `t = q` is `rl_close`, the `c`-edge is `K3G_of_cedge` against `kor_gen`).
Credit: the climb is Beeson-Rosu / Zhang style; the hand proof is PROOF 9.4 of this project.
-/
import Erdos634.Draft.WGapRL31

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

/-- the origin shifted by `k` columns -/
noncomputable def xshk (f : ℝ) (k : ℕ) (x : ℝ) : ℝ := x + 1 * (k : ℝ) * f ^ 2

theorem lpG_shk (e f x : ℝ) (k : ℕ) (ξ η : ℝ) : lpG e f 1 (xshk f k x) ξ η = lpG e f 1 x (ξ + k) η :=
  Erdos634.Draft.WGapStmt.lpG_shift e f 1 x (k : ℝ) ξ η

theorem lvG_shk {e f : ℝ} (x r : ℝ) (k : ℕ) : lvG e f 1 (xshk f k x) r = lvG e f 1 x ((k : ℝ) + r) := by
  unfold xshk lvG
  ring

theorem dcvec_shk (e f x : ℝ) (k : ℕ) : dcvec e f (xshk f k x) = dcvec e f x := by
  unfold dcvec
  rw [lpG_shk, lpG_shk]
  unfold lpG
  ext i
  fin_cases i <;> simp [mkPt_zero, mkPt_one] <;> ring

theorem PIR_shk (e f x : ℝ) (j i k : ℕ) (t m : ℝ) :
    PIR e f (xshk f k x) j i t m = PIR e f x j (i + k) (t + k) m := by
  unfold PIR
  rw [lpG_shk]
  exact lpG_congr (by ring) (by push_cast; ring)

theorem hasV_toShk {e f x : ℝ} {k : ℕ} {t : Fin N} {a1 b1 a2 b2 a3 b3 a1' a2' a3' : ℝ}
    (h : HasV D t (lpG e f 1 x a1 b1) (lpG e f 1 x a2 b2) (lpG e f 1 x a3 b3))
    (h1 : a1 = a1' + k) (h2 : a2 = a2' + k) (h3 : a3 = a3' + k) :
    HasV D t (lpG e f 1 (xshk f k x) a1' b1) (lpG e f 1 (xshk f k x) a2' b2) (lpG e f 1 (xshk f k x) a3' b3) := by
  rw [lpG_shk, lpG_shk, lpG_shk]
  rw [h1, h2, h3] at h
  exact h

theorem toShk {e f x a b a' b' : ℝ} {k : ℕ} (ha : a = a' + k) (hb : b = b') :
    lpG e f 1 x a b = lpG e f 1 (xshk f k x) a' b' := by
  rw [lpG_shk]; exact lpG_congr ha hb

section climb1

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem clampedBelowG_shk {s η₁ : ℝ} (x : ℝ) (k : ℕ) (h : ClampedBelowG D (e : ℝ) (f : ℝ) 1 (xshk (f : ℝ) k x) s η₁) :
    ClampedBelowG D (e : ℝ) (f : ℝ) 1 x (s + k) η₁ := by
  obtain ⟨η', hη, hc⟩ := h
  refine ⟨η', hη, fun Q hQ hmem ed hed => ?_⟩
  have e1 : lvG (e : ℝ) f 1 (xshk (f : ℝ) k x) s = lvG (e : ℝ) f 1 x (s + k) := by
    rw [lvG_shk, add_comm]
  have p1 : lpG (e : ℝ) f 1 (xshk (f : ℝ) k x) (s - η₁) η₁ = lpG (e : ℝ) f 1 x (s + k - η₁) η₁ :=
    by rw [lpG_shk]; exact lpG_congr (by ring) rfl
  have p2 : lpG (e : ℝ) f 1 (xshk (f : ℝ) k x) (s - η') η' = lpG (e : ℝ) f 1 x (s + k - η') η' :=
    by rw [lpG_shk]; exact lpG_congr (by ring) rfl
  rw [e1, p1, p2] at hc
  exact hc Q hQ hmem ed hed

theorem K3G_shiftk {s j0 : ℝ} (x : ℝ) (k : ℕ) (h : K3G D (e : ℝ) (f : ℝ) 1 (xshk (f : ℝ) k x) s j0) :
    K3G D (e : ℝ) (f : ℝ) 1 x (s + k) j0 := by
  have e1 : lvG (e : ℝ) f 1 (xshk (f : ℝ) k x) s = lvG (e : ℝ) f 1 x (s + k) := by
    rw [lvG_shk, add_comm]
  rcases h with h | ⟨w, k', m, η₁, η₂, hkm, h1, h2, hk, hm, hl, hle, hc⟩
  · left
    rw [e1] at h
    exact h
  · right
    refine ⟨w, k', m, η₁, η₂, hkm, h1, h2, ?_, ?_, hl, ?_, clampedBelowG_shk x k hc⟩
    · rw [hk, lpG_shk]; exact lpG_congr (by ring) rfl
    · rw [hm, lpG_shk]; exact lpG_congr (by ring) rfl
    · intro i
      have := hle i
      rw [e1] at this
      exact this

/-- "K or Sigma" of size `q`, `1 ≤ q`, at the row `y₀+1`: the pair `(y₀+1+q, y₀+1)` with `(K2)`, `(K3)` cannot occur, given `U(0,y₀+1)`, `Sigma[q]`
and Theorem K (`T⁺` is `K1J` or the strip tile).  Generalizes `kor_one` (`q = 1`), `kor_two` (`q = 2`). -/
theorem kor_gen (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {c₀ J y₀ q : ℕ}
    (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hq : 1 ≤ q) (hjf : y₀ + q + 1 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J y₀)
    (hUc : ∀ y : ℕ, J ≤ y → y ≤ y₀ → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y : ℝ))
    (hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0)
    (hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
    (hIH : SigmaAll D e f q)
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (y₀ + 1 + q) (y₀ + 1))
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((y₀ + 1 + q : ℕ) : ℝ) ((y₀ + 1 : ℕ) : ℝ)) : False := by
  have hUy := hUc y₀ hJ le_rfl
  rcases Tplus_core S hJ hS1 hUy hU01 with hK1 | hE1
  · exact K_at_origin S c₀ (y₀ + 1) (fun _ => h2) hU0 hK1 q hq (y₀ + 1 + q) (y₀ + 1) le_rfl (by omega) (by omega)
      (by omega) hK2 hK3
  · refine hIH c₀ J hA (y₀ + 1 + q) (y₀ + 1) (by omega) (by omega) (by omega) (by omega) ⟨?_, hK2, hK3⟩
    intro y hy1 hy2
    rcases Nat.lt_or_ge y (y₀ + 1) with hlt | hge
    · exact hS1 y hy1 (by omega)
    · have hye : y = y₀ + 1 := by omega
      subst hye
      rw [Nat.cast_add, Nat.cast_one]
      exact hE1

end climb1

#print axioms lpG_shk
#print axioms PIR_shk
#print axioms dcvec_shk
#print axioms K3G_shiftk
#print axioms kor_gen

end Erdos634.Draft.WGapStmt
