/-
Draft/WGapRL21.lean -- written 16 November 2026 (session 13).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, chord step with a TWO-edge chord, `i = 2`, `m = 0`, `tau' = 0`).
Not imported by any aggregate.  No sorry, no native_decide.
* `chord_first`: abstract first step of a chord: the beta tile at the bottom point of the chord lays its `a`-edge (the `c`-edge case is delegated to the hypothesis `hnoC`).
* `PIR_lin`: `pi(t,m) + k (pi(t-1,m) - pi(t,m)) = pi(t-k,m)`.
* `chord2_first`: the chord `[B_0, C_0] = [pi(2,1), pi(0,1)]` (two `a`-edges of `gamma(2,0)`, `gamma(1,0)`): the first tile above is `nu(1,1)`; the `c`-edge case is killed by `fault_cover` (q = 2, `2a - c` not in `S`, `nonmem_ma_sub_c`) against the cover at `C_0`.
-/
import Erdos634.Draft.WGapRL20

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

theorem PIR_lin {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t m k : ℝ) :
    PIR e f x j i t m + k • (PIR e f x j i (t - 1) m - PIR e f x j i t m) = PIR e f x j i (t - k) m := by
  rw [PIR_lp he hef, PIR_lp he hef, PIR_lp he hef, lp_add_smul]
  exact lpG_congr (by ring) (by ring)

section rl21

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem chord_first (S : SetupG D e f α β γ L ax ay) {X Y Z W0 d : Plane} {tG tN : Fin N}
    (hXY : X ≠ Y) (hG : HasV D tG X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (aG : (D.tile tG).localAngle X = γ) (aN : (D.tile tN).localAngle X = α)
    (hΞ : EdgeCoverS D X d (-1)) (hcr : 0 < cross d (Y - X))
    (hNray : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tN).pts j ≠ AffineMap.lineMap X Y s)
    (hnoC : ∀ (τ' : Fin N) (P W : Plane), HasV D τ' X P W → (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) →
      cross (Y - X) (W - X) < 0 → dist X P = (f : ℝ) ^ 2 → False)
    (hdXY : dist X Y = (e : ℝ) * f) (hd1 : dist W0 X = (f : ℝ) ^ 2)
    (hd2 : dist W0 Y = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (hW0 : cross (Y - X) (W0 - X) < 0) :
    ∃ τ : Fin N, HasV D τ X Y W0 := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  obtain ⟨τ', P, W, hV, ⟨s, hs0, hPs⟩, hW, hang, hPW, hsides⟩ :=
    rl_beta_fill_abs S hXY hG hZ aG aN hΞ hcr hNray
  have hdXP : dist X P = s * ((e : ℝ) * f) := by
    rw [hPs, dist_left_lineMap, Real.norm_of_nonneg hs0.le, hdXY]
  rcases hsides with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hs1 : s = 1 := by
      rw [h1] at hdXP
      have : (s - 1) * ((e : ℝ) * f) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hef0.ne'
    have hP : P = Y := by rw [hPs, hs1, AffineMap.lineMap_apply_one]
    have hWeq : W0 = W := by
      refine same_third hXY ?_ ?_ hW0 hW
      · rw [hd1, dist_comm W, h2]
      · rw [hd2, ← hP, dist_comm W, hPW]
    exact ⟨τ', hasV_congr hV rfl hP hWeq.symm⟩
  · exact (hnoC τ' P W hV ⟨s, hs0, hPs⟩ hW h1).elim

set_option maxHeartbeats 16000000 in
theorem chord2_first (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ) (hi : 2 + 1 ≤ f - 1)
    {τ2 τ1 tNa : Fin N}
    (hΓ2 : HasV D τ2 (PIR (e : ℝ) f x j 2 2 0) (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 1))
    (hΓ1 : HasV D τ1 (PIR (e : ℝ) f x j 2 1 0) (PIR (e : ℝ) f x j 2 1 1) (PIR (e : ℝ) f x j 2 0 1))
    (hNa' : HasV D tNa (PIR (e : ℝ) f x j 2 3 0) (PIR (e : ℝ) f x j 2 2 0) (PIR (e : ℝ) f x j 2 2 1))
    (hΞ : EdgeCoverS D (PIR (e : ℝ) f x j 2 2 1)
      (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j) (-1))
    (hZc : EdgeCoverS D (PIR (e : ℝ) f x j 2 0 1) (wvec (e : ℝ) f x) 1) :
    ∃ τν : Fin N, HasV D τν (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 1) (PIR (e : ℝ) f x j 2 1 2) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hκ := kapG_pos he0 hef
  have hν0 := nuG_pos he0 hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  -- distances and crosses
  have d1 : dist (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 1) = (e : ℝ) * f := by
    have := dPIR_a he0 hef x j 2 1 1
    rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this
  have d2 : dist (PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 2 1) = (f : ℝ) ^ 2 := by
    have := dPIR_c he0 hef x j 2 1 1
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
    rw [dist_comm]; exact this
  have d3 : dist (PIR (e : ℝ) f x j 2 1 2) (PIR (e : ℝ) f x j 2 1 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := dPIR_b he0 hef x j 2 1 1
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
    rw [dist_comm]; exact this
  have dNa : dist (PIR (e : ℝ) f x j 2 3 0) (PIR (e : ℝ) f x j 2 2 0) = (e : ℝ) * f := by
    have := dPIR_a he0 hef x j 2 2 0
    rwa [show (2 : ℝ) + 1 = 3 by norm_num] at this
  have dCO : dist (PIR (e : ℝ) f x j 2 1 1) (PIR (e : ℝ) f x j 2 2 0) = (f : ℝ) ^ 2 := by
    have := dPIR_c he0 hef x j 2 1 0
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at this
    rw [dist_comm]; exact this
  have hXY : PIR (e : ℝ) f x j 2 2 1 ≠ PIR (e : ℝ) f x j 2 1 1 := by
    intro h
    have h1 := d1
    rw [h, dist_self] at h1
    linarith
  have hz : 0 < cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 0 - PIR (e : ℝ) f x j 2 2 1) := by
    have : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 0 - PIR (e : ℝ) f x j 2 2 1) = kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; push_cast; ring
    rw [this]; exact hκ
  have hW0 : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 2 - PIR (e : ℝ) f x j 2 2 1) < 0 := by
    have : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 2 - PIR (e : ℝ) f x j 2 2 1) = -kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; push_cast; ring
    rw [this]; linarith
  have aG : (D.tile τ2).localAngle (PIR (e : ℝ) f x j 2 2 1) = γ :=
    (hΓ2.rot.anglesG S.tile S.hM).2.2 dCO
  have aN : (D.tile tNa).localAngle (PIR (e : ℝ) f x j 2 2 1) = α :=
    (hNa'.rot.rot.anglesG S.tile S.hM).1 dNa
  have hcr : 0 < cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
      (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) := by
    have : cross (lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x (((2 : ℕ) : ℝ) + 1) j)
        (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) = kapG (e : ℝ) f := by
      rw [PIR_lp he0 hef, PIR_lp he0 hef, cross_lpG]; push_cast; ring
    rw [this]; exact hκ
  have hNray := known_off_ray hXY hNa'.rot.rot
    (off_PIRg he0 hef x j 2 2 1 1 1 3 0 (by intro h; nlinarith [h]))
    (off_PIRg he0 hef x j 2 2 1 1 1 2 0 (by intro h; nlinarith [h]))
  -- the line `P0 + k d`
  have hk : ∀ k : ℝ, PIR (e : ℝ) f x j 2 2 1 + k • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) =
      PIR (e : ℝ) f x j 2 (2 - k) 1 := by
    intro k
    have := PIR_lin he0 hef x j 2 2 1 k
    rwa [show (2 : ℝ) - 1 = 1 by norm_num] at this
  have hwcr : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (wvec (e : ℝ) f x) ≠ 0 := by
    have h := cross_wvec_step he0 hef x j 2 1 1
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
    have e1 : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (wvec (e : ℝ) f x) =
        cross (wvec (e : ℝ) f x) (PIR (e : ℝ) f x j 2 2 1 - PIR (e : ℝ) f x j 2 1 1) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [e1, h]; linarith
  refine chord_first S (Z := PIR (e : ℝ) f x j 2 2 0) (W0 := PIR (e : ℝ) f x j 2 1 2) (tG := τ2) (tN := tNa)
    hXY hΓ2.rot hz aG aN hΞ hcr hNray ?_ d1 d2 d3 hW0
  -- the `c`-edge case: `fault_cover` against the cover at `C_0`
  intro τ' P W hV ⟨s, hs0, hPs⟩ hWcr hdc
  have hdXP : dist (PIR (e : ℝ) f x j 2 2 1) P = s * ((e : ℝ) * f) := by
    rw [hPs, dist_left_lineMap, Real.norm_of_nonneg hs0.le, d1]
  have hlu : s * ((e : ℝ) * f) = (f : ℝ) ^ 2 := by rw [← hdXP, hdc]
  have hdn : ‖PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1‖ = (e : ℝ) * f := by
    rw [← dist_eq_norm, dist_comm]; exact d1
  have hnon : ∀ x' y' z' : ℕ, s * ((e : ℝ) * f) + ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) ≠
      ((2 : ℕ) : ℝ) * ((e : ℝ) * f) := by
    intro x' y' z' h
    rw [hlu] at h
    have hZR : ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) =
        ((2 : ℕ) : ℝ) * ((e : ℝ) * f) - (f : ℝ) ^ 2 := by linarith
    have hZI : (x' : ℤ) * ((e : ℤ) * f) + (y' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z' : ℤ) * (f : ℤ) ^ 2 =
        ((2 : ℕ) : ℤ) * ((e : ℤ) * f) - (f : ℤ) ^ 2 := by exact_mod_cast hZR
    exact Erdos634.Draft.WGapArith.nonmem_ma_sub_c S.he S.hef S.hco (m := 2) (by norm_num) (by omega) ⟨x', y', z', hZI⟩
  have hE : HasV D τ2 (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 1 + (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1))
      (PIR (e : ℝ) f x j 2 2 0) := hasV_congr hΓ2.rot rfl (by abel) rfl
  have hA0 : (-1 : ℝ) * cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 0 - PIR (e : ℝ) f x j 2 2 1) < 0 := by
    have : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 0 - PIR (e : ℝ) f x j 2 2 1) = kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; push_cast; ring
    rw [this]; linarith
  have hFo : HasV D τ' (PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 2 1 + s • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1)) W :=
    hasV_congr hV rfl (by rw [hPs, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]) rfl
  have hR : 0 < (-1 : ℝ) * cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (W - PIR (e : ℝ) f x j 2 2 1) := by
    linarith
  have hT : ∀ t : ℕ, t < 2 → ∃ (T : Fin N) (A : Plane),
      HasV D T (PIR (e : ℝ) f x j 2 2 1 + (t : ℝ) • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1))
        (PIR (e : ℝ) f x j 2 2 1 + ((t : ℝ) + 1) • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1)) A ∧
      (-1 : ℝ) * cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1)
        (A - (PIR (e : ℝ) f x j 2 2 1 + (t : ℝ) • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1))) < 0 := by
    intro t ht
    interval_cases t
    · refine ⟨τ2, PIR (e : ℝ) f x j 2 2 0, ?_, ?_⟩
      · refine hasV_congr hΓ2.rot ?_ ?_ rfl
        · rw [hk]; exact PIR_congr (by norm_num) rfl
        · rw [hk]; exact PIR_congr (by norm_num) rfl
      · have e0 : PIR (e : ℝ) f x j 2 2 1 + ((0 : ℕ) : ℝ) • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) =
            PIR (e : ℝ) f x j 2 2 1 := by simp
        rw [e0]; linarith
    · refine ⟨τ1, PIR (e : ℝ) f x j 2 1 0, ?_, ?_⟩
      · refine hasV_congr hΓ1.rot ?_ ?_ rfl
        · rw [hk]; exact PIR_congr (by norm_num) rfl
        · rw [hk]; exact PIR_congr (by norm_num) rfl
      · have e1 : PIR (e : ℝ) f x j 2 2 1 + ((1 : ℕ) : ℝ) • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) =
            PIR (e : ℝ) f x j 2 1 1 := by
          rw [hk]; exact PIR_congr (by norm_num) rfl
        rw [e1]
        have : cross (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) (PIR (e : ℝ) f x j 2 1 0 - PIR (e : ℝ) f x j 2 1 1) = kapG (e : ℝ) f := by
          rw [cross_PIRg he0 hef]; push_cast; ring
        rw [this]; linarith
  have hfc := fault_cover S (q := 2) (by norm_num) (PIR (e : ℝ) f x j 2 2 1)
    (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) ((e : ℝ) * f) s (-1) (Or.inr rfl) hdn hef0 hs0 hnon
    τ2 (PIR (e : ℝ) f x j 2 2 0) hE hA0 τ' W hFo hR hT
  have e2 : PIR (e : ℝ) f x j 2 2 1 + ((2 : ℕ) : ℝ) • (PIR (e : ℝ) f x j 2 1 1 - PIR (e : ℝ) f x j 2 2 1) =
      PIR (e : ℝ) f x j 2 0 1 := by
    rw [hk]; exact PIR_congr (by norm_num) rfl
  rw [e2] at hfc
  exact edgecover_clash (Or.inr rfl) (Or.inl rfl) hwcr hfc hZc

end rl21

#print axioms chord2_first

end Erdos634.Draft.WGapStmt
