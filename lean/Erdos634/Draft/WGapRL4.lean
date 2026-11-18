/-
Draft/WGapRL4.lean -- written 16 November 2026 (session 9).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2 step (beta)).
Not imported by any aggregate.  `wvec` = `w = nu (p(-1,s) - p(0,0))` (the reflected-lattice step, length `b`), `PIR_aff : pi(t,m) = pi(t,0) + m w`.
`rl_beta` (RL step (beta)): on the line `L^(tau)` (direction `w`), the tiles `nu(tau,m')` (`mu0 <= m' <= m`, `b`-edges on `L^(tau)` on its RIGHT) and a tile on the LEFT with an
edge of length `a` (`lamc = e/f`) or `c` (`lamc = 1`) from `X0 = pi(tau,mu0)` along `w` give a tile covering the open half-disk on the left of `L^(tau)` at `C_m = pi(tau, m+1)`
(`fault_cover` with `(A1)`: `q b - a`, `q b - c`, `q = m+1-mu0 <= f-1`).  `rl_cross_ne`: `cross (Y - O) w = -kapG` (the two directions of the final overlap are not parallel).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapRL3

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

/-- `d_c = p(-1,s) - p(0,0)` (`= p'(1,0) - p'(0,0)`, length `c`) -/
noncomputable def dcvec (e f x : ℝ) : Plane := lpG e f 1 x (-1) (sMir e f) - lpG e f 1 x 0 0

/-- `w = nu d_c` (length `b`) -/
noncomputable def wvec (e f x : ℝ) : Plane := lpG e f 1 x (-(nuG e f)) (nuG e f * sMir e f) - lpG e f 1 x 0 0

theorem lpG_add (e f x ξ η a b : ℝ) :
    lpG e f 1 x (ξ + a) (η + b) = lpG e f 1 x ξ η + (lpG e f 1 x a b - lpG e f 1 x 0 0) := by
  unfold lpG
  ext i
  fin_cases i <;> simp [mkPt_zero, mkPt_one] <;> ring

theorem lpG_smul (e f x r a b : ℝ) :
    r • (lpG e f 1 x a b - lpG e f 1 x 0 0) = lpG e f 1 x (r * a) (r * b) - lpG e f 1 x 0 0 := by
  unfold lpG
  ext i
  fin_cases i <;> simp [mkPt_zero, mkPt_one] <;> ring

theorem wvec_eq (e f x : ℝ) : wvec e f x = nuG e f • dcvec e f x := by
  unfold wvec dcvec
  rw [lpG_smul]
  have h1 : lpG e f 1 x (-(nuG e f)) (nuG e f * sMir e f) = lpG e f 1 x (nuG e f * -1) (nuG e f * sMir e f) := lpG_congr (by ring) rfl
  rw [h1]

theorem PIR_aff (e f x : ℝ) (j i : ℕ) (t m : ℝ) :
    PIR e f x j i t m = PIR e f x j i t 0 + m • wvec e f x := by
  have hw : m • wvec e f x = lpG e f 1 x (m * -(nuG e f)) (m * (nuG e f * sMir e f)) - lpG e f 1 x 0 0 := by
    unfold wvec; rw [lpG_smul]
  have e1 : PIR e f x j i t m = lpG e f 1 x (t + m * -(nuG e f)) (((j : ℝ) + i + 1 - t) + m * (nuG e f * sMir e f)) :=
    lpG_congr (by ring) (by ring)
  have e2 : PIR e f x j i t 0 = lpG e f 1 x t ((j : ℝ) + i + 1 - t) := lpG_congr (by ring) (by ring)
  rw [e1, e2, hw, lpG_add]

theorem PIR_shift (e f x : ℝ) (j i : ℕ) (t m r : ℝ) :
    PIR e f x j i t (m + r) = PIR e f x j i t m + r • wvec e f x := by
  rw [PIR_aff e f x j i t (m + r), PIR_aff e f x j i t m, add_smul]; abel

theorem dist_dc {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) : ‖dcvec e f x‖ = f ^ 2 := by
  have hf : 0 < f := he.trans hef
  have hs := sMir_mul he hef
  have h := dist_lpG (ε := 1) (x := x) he hef (by norm_num) (ξ := -1) (η := sMir e f) (ξ' := 0) (η' := 0) (d := f ^ 2) (by positivity) ?_
  · rw [dist_eq_norm] at h
    exact h
  · unfold QfG
    linear_combination (sMir e f * (f ^ 2 - e ^ 2)) * hs

theorem norm_wvec {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) : ‖wvec e f x‖ = f ^ 2 - e ^ 2 := by
  rw [wvec_eq, norm_smul, dist_dc he hef, Real.norm_eq_abs, abs_of_pos (nuG_pos he hef)]
  have := nuG_spec he hef
  linarith

/-- the directions of `Lambda_3` (`Y - O`) and of `L^(tau)` (`w`) are not parallel: `cross (Y - O) w = -kapG` -/
theorem rl_cross_ne {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (ξ η : ℝ) :
    cross (lpG e f 1 x (ξ - nuG e f) (η + 2 + nuG e f) - lpG e f 1 x (ξ + 1) η) (wvec e f x) = -(kapG e f) := by
  have hns := nu_s he hef
  unfold wvec
  rw [cross_lpG]
  linear_combination (-(kapG e f) * (nuG e f + 1)) * hns

theorem cross_wvec_step {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t m : ℝ) :
    cross (wvec e f x) (PIR e f x j i (t + 1) m - PIR e f x j i t m) = -(kapG e f) := by
  have hns := nu_s he hef
  unfold wvec PIR
  rw [cross_lpG]
  linear_combination (-(kapG e f)) * hns

theorem cross_smul_left (c : ℝ) (v w : Plane) : cross (c • v) w = c * cross v w := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

section rl4

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
/-- **RL step (beta)** (PROOF 8.2 (beta)) -/
theorem rl_beta (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i τ μ0 m : ℕ) (hμ : μ0 ≤ m) (hm : m ≤ i) (hi : i + 1 ≤ f - 1)
    (hnu : ∀ m' : ℕ, μ0 ≤ m' → m' ≤ m → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((τ : ℝ) + 1) m') (PIR (e : ℝ) f x j i τ m') (PIR (e : ℝ) f x j i τ ((m' : ℝ) + 1)))
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j i τ μ0) (PIR (e : ℝ) f x j i τ μ0 + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i τ μ0)) :
    EdgeCoverS D (PIR (e : ℝ) f x j i τ ((m : ℝ) + 1)) (wvec (e : ℝ) f x) 1 := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hν0 := nuG_pos he0 hef
  have hνb := nuG_spec he0 hef
  have hκ := kapG_pos he0 hef
  set P0 : Plane := PIR (e : ℝ) f x j i τ μ0 with hP0
  set d : Plane := wvec (e : ℝ) f x with hd
  have hdn : ‖d‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := norm_wvec he0 hef x
  have hu : 0 < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  set q : ℕ := m + 1 - μ0 with hq
  have hq1 : 1 ≤ q := by omega
  have hqcast : ((q : ℕ) : ℝ) = (m : ℝ) + 1 - μ0 := by
    rw [hq, Nat.cast_sub (by omega)]; push_cast; ring
  have hWall : ∀ t : ℕ, t < q → ∃ (T : Fin N) (A : Plane),
      HasV D T (P0 + (t : ℝ) • d) (P0 + ((t : ℝ) + 1) • d) A ∧ (1 : ℝ) * cross d (A - (P0 + (t : ℝ) • d)) < 0 := by
    intro t ht
    obtain ⟨T, hT⟩ := hnu (μ0 + t) (by omega) (by omega)
    have h1 : PIR (e : ℝ) f x j i τ (((μ0 + t : ℕ) : ℝ)) = P0 + (t : ℝ) • d := by
      rw [hP0, hd, Nat.cast_add, PIR_shift]
    have h2 : PIR (e : ℝ) f x j i τ ((((μ0 + t : ℕ) : ℝ)) + 1) = P0 + ((t : ℝ) + 1) • d := by
      rw [hP0, hd, show (((μ0 + t : ℕ) : ℝ)) + 1 = (μ0 : ℝ) + ((t : ℝ) + 1) by push_cast; ring, PIR_shift]
    refine ⟨T, PIR (e : ℝ) f x j i ((τ : ℝ) + 1) ((μ0 + t : ℕ) : ℝ), hasV_congr hT.rot h1 h2 rfl, ?_⟩
    have key : cross d (PIR (e : ℝ) f x j i ((τ : ℝ) + 1) ((μ0 + t : ℕ) : ℝ) - PIR (e : ℝ) f x j i τ ((μ0 + t : ℕ) : ℝ)) = -(kapG (e : ℝ) f) :=
      cross_wvec_step he0 hef x j i (τ : ℝ) _
    rw [← h1, one_mul, key]
    linarith
  obtain ⟨E, A0, hE', hA0'⟩ := hWall 0 (by omega)
  have hE : HasV D E P0 (P0 + d) A0 := hasV_congr hE' (by simp) (by simp) rfl
  have hA0 : (1 : ℝ) * cross d (A0 - P0) < 0 := by simpa using hA0'
  obtain ⟨F, R, lamc, hlc, hF, hR⟩ := hleft
  have hlpos : 0 < lamc := by
    rcases hlc with h | h
    · rw [h]; positivity
    · rw [h]; norm_num
  have hFo : HasV D F P0 (P0 + (lamc / nuG (e : ℝ) f) • d) R :=
    hasV_congr hF rfl (by rw [hd, wvec_eq, smul_smul, div_mul_cancel₀ _ hν0.ne']) rfl
  have hRpos : 0 < (1 : ℝ) * cross d (R - P0) := by
    rw [one_mul, hd, wvec_eq, cross_smul_left]; exact mul_pos hν0 hR
  have hlu : (lamc / nuG (e : ℝ) f) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = lamc * (f : ℝ) ^ 2 := by
    have : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 = (f : ℝ) ^ 2 * nuG (e : ℝ) f := hνb.symm
    rw [this]; field_simp
  have hqf : q ≤ f - 1 := by omega
  have hnon : ∀ x' y' z' : ℕ, (lamc / nuG (e : ℝ) f) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) +
      ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) ≠ (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    intro x' y' z' h
    rw [hlu] at h
    rcases hlc with h1 | h1
    · rw [h1, show (e : ℝ) / f * (f : ℝ) ^ 2 = (e : ℝ) * f by field_simp] at h
      have hZR : ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) =
          (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - (e : ℝ) * f := by linarith
      have hZI : (x' : ℤ) * ((e : ℤ) * f) + (y' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z' : ℤ) * (f : ℤ) ^ 2 =
          (q : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) - (e : ℤ) * f := by exact_mod_cast hZR
      exact Erdos634.Draft.WGapArith.nonmem_mb_sub_a S.he S.hef S.hco (m := q) hq1 hqf ⟨x', y', z', hZI⟩
    · rw [h1, one_mul] at h
      have hZR : ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) =
          (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - (f : ℝ) ^ 2 := by linarith
      have hZI : (x' : ℤ) * ((e : ℤ) * f) + (y' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z' : ℤ) * (f : ℤ) ^ 2 =
          (q : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) - (f : ℤ) ^ 2 := by exact_mod_cast hZR
      exact Erdos634.Draft.WGapArith.nonmem_mb_sub_c S.he S.hef S.hco (m := q) hq1 hqf ⟨x', y', z', hZI⟩
  have key := fault_cover S (q := q) hq1 P0 d ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) (lamc / nuG (e : ℝ) f) 1 (Or.inl rfl) hdn hu
    (div_pos hlpos hν0) hnon E A0 hE hA0 F R hFo hRpos hWall
  have e0 : ((m : ℝ) + 1) = (μ0 : ℝ) + (q : ℝ) := by rw [hqcast]; ring
  rw [e0, PIR_shift]
  exact key

end rl4

end Erdos634.Draft.WGapStmt
