/-
Draft/WGapGen2.lean -- written 16 November 2026 (session 15).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, inner chord points, GENERAL position).
Not imported by any aggregate.  No sorry, no native_decide.
`chord_gen_inner`: generalization of `chord2_second` (WGapRL24) to an arbitrary inner point `X = pi(u,m+1)` of the layer-`m` chord with `r` chord edges still to go (`1 <= r <= min u (f-1)`):
the four known tiles at `X` (`gamma(u,m)`, `gamma(u+1,m)`, `nu(u,m)` below, `nu(u,m+1)` already above) leave one tile beside the ray, and it is `nu(u-1,m+1)`
(`inner_fill_abs`, `clamp_prev_tile`; the `b`/`c`-edge alternatives are killed by `fault_cover` with `q = r` against the top cover, multiplier `r <= f-1`, `nonmem_ma_sub_b/c`).
-/
import Erdos634.Draft.WGapGen1

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

section gen2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem chord_gen_inner (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i u r : ℕ) (m : ℝ)
    (hr1 : 1 ≤ r) (hru : r ≤ u) (hrf : r ≤ f - 1) {τ2 tNb τν : Fin N}
    (hΓ : ∀ t : ℕ, t < r → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((u : ℝ) - t) m) (PIR (e : ℝ) f x j i ((u : ℝ) - t) (m + 1))
        (PIR (e : ℝ) f x j i ((u : ℝ) - t - 1) (m + 1)))
    (hΓ2 : HasV D τ2 (PIR (e : ℝ) f x j i ((u : ℝ) + 1) m) (PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1))
      (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)))
    (hNb : HasV D tNb (PIR (e : ℝ) f x j i ((u : ℝ) + 1) m) (PIR (e : ℝ) f x j i (u : ℝ) m)
      (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)))
    (hν11 : HasV D τν (PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1)) (PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i (u : ℝ) (m + 1 + 1)))
    (hZc : EdgeCoverS D (PIR (e : ℝ) f x j i ((u : ℝ) - r) (m + 1)) (wvec (e : ℝ) f x) 1) :
    ∃ τ : Fin N, HasV D τ (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1))
      (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1 + 1)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hκ := kapG_pos he0 hef
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  obtain ⟨τ1, hΓ1'⟩ := hΓ 0 (by omega)
  have hΓ1 : HasV D τ1 (PIR (e : ℝ) f x j i (u : ℝ) m) (PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1)) :=
    hasV_congr hΓ1' (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl)
  -- distances
  have d12 : dist (PIR (e : ℝ) f x j i (u : ℝ) (m + 1 + 1)) (PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1)) = (f : ℝ) ^ 2 := by
    have := dPIR_c he0 hef x j i (u : ℝ) (m + 1)
    rw [dist_comm]; exact this
  have dXY : dist (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1)) = (e : ℝ) * f := by
    have := dPIR_a he0 hef x j i ((u : ℝ) - 1) (m + 1)
    rwa [sub_add_cancel] at this
  have dc0 : dist (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1)) (PIR (e : ℝ) f x j i (u : ℝ) m) = (f : ℝ) ^ 2 := by
    have := dPIR_c he0 hef x j i ((u : ℝ) - 1) m
    rw [sub_add_cancel] at this
    rw [dist_comm]; exact this
  have da1 : dist (PIR (e : ℝ) f x j i ((u : ℝ) + 1) m) (PIR (e : ℝ) f x j i (u : ℝ) m) = (e : ℝ) * f :=
    dPIR_a he0 hef x j i (u : ℝ) m
  have db2 : dist (PIR (e : ℝ) f x j i ((u : ℝ) + 1) m) (PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
    dPIR_b he0 hef x j i ((u : ℝ) + 1) m
  have hXY : PIR (e : ℝ) f x j i (u : ℝ) (m + 1) ≠ PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) := by
    intro h
    have h1 := dXY
    rw [h, dist_self] at h1
    linarith
  have hP'eq : PIR (e : ℝ) f x j i (u : ℝ) (m + 1) - (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) =
      PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1) := by
    have h := PIR_lin he0 hef x j i (u : ℝ) (m + 1) (-1)
    rw [sub_neg_eq_add] at h
    rw [← h, neg_smul, one_smul]; abel
  have hZcr : 0 < cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i (u : ℝ) m - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) := by
    have : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (u : ℝ) m - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; ring
    rw [this]; exact hκ
  have hWc : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i (u : ℝ) (m + 1 + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) < 0 := by
    have : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (u : ℝ) (m + 1 + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = -kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; ring
    rw [this]; linarith
  have hν : HasV D τν (PIR (e : ℝ) f x j i (u : ℝ) (m + 1) -
      (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)))
      (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) (PIR (e : ℝ) f x j i (u : ℝ) (m + 1 + 1)) :=
    hasV_congr hν11 hP'eq.symm rfl rfl
  -- angles
  have a0 : (D.tile τ1).localAngle (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = γ := (hΓ1.rot.anglesG S.tile S.hM).2.2 dc0
  have aA : (D.tile tNb).localAngle (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = α := (hNb.rot.rot.anglesG S.tile S.hM).1 da1
  have aB : (D.tile τ2).localAngle (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = β := (hΓ2.rot.rot.anglesG S.tile S.hM).2.1 db2
  have aν : (D.tile τν).localAngle (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = γ := (hν11.rot.anglesG S.tile S.hM).2.2 d12
  have n0ν : τ1 ≠ τν := by
    obtain ⟨i3, hi3⟩ := hasV_third hΓ1
    refine HasV.ne_of_vertex hν11 hi3 ?_ ?_ ?_
    · intro h
      rw [PIR_lp he0 hef, PIR_lp he0 hef] at h
      have := lpG_xi_eq he0 hef hε h
      linarith
    · intro h
      rw [PIR_lp he0 hef, PIR_lp he0 hef] at h
      have := lpG_xi_eq he0 hef hε h
      linarith
    · intro h
      rw [PIR_lp he0 hef, PIR_lp he0 hef] at h
      have := lpG_xi_eq he0 hef hε h
      linarith
  have hneg21 : ∀ s : ℝ, 0 < s → PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1) ≠
      AffineMap.lineMap (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1)) s := by
    intro s hs h
    rw [PIR_lp he0 hef, PIR_lp he0 hef, PIR_lp he0 hef, lineMap_lpG] at h
    have := lpG_xi_eq he0 hef hε h
    nlinarith [this]
  have rA := known_off_ray hXY hNb.rot.rot
    (off_PIRg he0 hef x j i (u : ℝ) (m + 1) ((u : ℝ) - 1) (m + 1) ((u : ℝ) + 1) m (by intro h; nlinarith [h]))
    (off_PIRg he0 hef x j i (u : ℝ) (m + 1) ((u : ℝ) - 1) (m + 1) (u : ℝ) m (by intro h; nlinarith [h]))
  have rB := known_off_ray hXY hΓ2.rot.rot
    (off_PIRg he0 hef x j i (u : ℝ) (m + 1) ((u : ℝ) - 1) (m + 1) ((u : ℝ) + 1) m (by intro h; nlinarith [h])) hneg21
  have rν := known_off_ray hXY hν11.rot
    (off_PIRg he0 hef x j i (u : ℝ) (m + 1) ((u : ℝ) - 1) (m + 1) (u : ℝ) (m + 1 + 1) (by intro h; nlinarith [h])) hneg21
  rcases inner_fill_abs S (t0 := τ1) (tA := tNb) (tB := τ2) (tν := τν) hXY hΓ1.rot hZcr hν hWc a0 aA aB aν n0ν rA rB rν with
    ⟨τ', P, W', hV, ⟨s, hs0, hPs⟩, hcr, hPW, hXP, hXW⟩ | ⟨τ', P, W', hV, ⟨s, hs0, hPs⟩, hcr, hd⟩
  · -- beta tile with its `a`-edge on the ray
    have hdXP : dist (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) P = s * ((e : ℝ) * f) := by
      rw [hPs, dist_left_lineMap, Real.norm_of_nonneg hs0.le, dXY]
    have hs1 : s = 1 := by
      rw [hXP] at hdXP
      have : (s - 1) * ((e : ℝ) * f) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hef0.ne'
    have hP : P = PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) := by rw [hPs, hs1, AffineMap.lineMap_apply_one]
    have dd1 : dist (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1 + 1)) (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = (f : ℝ) ^ 2 := by
      have := dPIR_c he0 hef x j i ((u : ℝ) - 1) (m + 1)
      rw [sub_add_cancel] at this
      rw [dist_comm]; exact this
    have dd2 : dist (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1 + 1)) (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1)) =
        (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      have := dPIR_b he0 hef x j i ((u : ℝ) - 1) (m + 1)
      rw [dist_comm]; exact this
    have hzz : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1 + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) < 0 := by
      have : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
          (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1 + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) = -kapG (e : ℝ) f := by
        rw [cross_PIRg he0 hef]; ring
      rw [this]; linarith
    have hWeq : PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1 + 1) = W' := by
      refine same_third hXY ?_ ?_ hzz hcr
      · rw [dd1, dist_comm W', hXW]
      · rw [dd2, ← hP, dist_comm W', hPW]
    exact ⟨τ', hasV_congr hV rfl hP hWeq.symm⟩
  · -- a `b`- or `c`-edge on the ray: `fault_cover` against the top cover
    exfalso
    have hdXP : dist (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) P = s * ((e : ℝ) * f) := by
      rw [hPs, dist_left_lineMap, Real.norm_of_nonneg hs0.le, dXY]
    have hdn : ‖PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)‖ = (e : ℝ) * f := by
      rw [← dist_eq_norm, dist_comm]; exact dXY
    have hnon : ∀ x' y' z' : ℕ, s * ((e : ℝ) * f) + ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) ≠
        (r : ℝ) * ((e : ℝ) * f) := by
      intro x' y' z' h
      rw [← hdXP] at h
      rcases hd with hb | hc
      · rw [hb] at h
        have hZR : ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) =
            (r : ℝ) * ((e : ℝ) * f) - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by linarith
        have hZI : (x' : ℤ) * ((e : ℤ) * f) + (y' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z' : ℤ) * (f : ℤ) ^ 2 =
            (r : ℤ) * ((e : ℤ) * f) - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by exact_mod_cast hZR
        exact Erdos634.Draft.WGapArith.nonmem_ma_sub_b S.he S.hef S.hco (m := r) hr1 hrf ⟨x', y', z', hZI⟩
      · rw [hc] at h
        have hZR : ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) =
            (r : ℝ) * ((e : ℝ) * f) - (f : ℝ) ^ 2 := by linarith
        have hZI : (x' : ℤ) * ((e : ℤ) * f) + (y' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z' : ℤ) * (f : ℤ) ^ 2 =
            (r : ℤ) * ((e : ℤ) * f) - (f : ℤ) ^ 2 := by exact_mod_cast hZR
        exact Erdos634.Draft.WGapArith.nonmem_ma_sub_c S.he S.hef S.hco (m := r) hr1 hrf ⟨x', y', z', hZI⟩
    have hk : ∀ k' : ℝ, PIR (e : ℝ) f x j i (u : ℝ) (m + 1) +
        k' • (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) =
        PIR (e : ℝ) f x j i ((u : ℝ) - k') (m + 1) := fun k' => PIR_lin he0 hef x j i (u : ℝ) (m + 1) k'
    have hE : HasV D τ1 (PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (u : ℝ) (m + 1) + (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)))
        (PIR (e : ℝ) f x j i (u : ℝ) m) := hasV_congr hΓ1.rot rfl (by abel) rfl
    have hA0 : (-1 : ℝ) * cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (u : ℝ) m - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) < 0 := by linarith
    have hFo : HasV D τ' (PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (u : ℝ) (m + 1) + s • (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))) W' :=
      hasV_congr hV rfl (by rw [hPs, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]) rfl
    have hR : 0 < (-1 : ℝ) * cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (W' - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) := by linarith
    have hT : ∀ t : ℕ, t < r → ∃ (T : Fin N) (A : Plane),
        HasV D T (PIR (e : ℝ) f x j i (u : ℝ) (m + 1) + (t : ℝ) • (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)))
          (PIR (e : ℝ) f x j i (u : ℝ) (m + 1) + ((t : ℝ) + 1) • (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))) A ∧
        (-1 : ℝ) * cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
          (A - (PIR (e : ℝ) f x j i (u : ℝ) (m + 1) + (t : ℝ) • (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)))) < 0 := by
      intro t ht
      obtain ⟨T, hT'⟩ := hΓ t ht
      refine ⟨T, PIR (e : ℝ) f x j i ((u : ℝ) - t) m, ?_, ?_⟩
      · refine hasV_congr hT'.rot ?_ ?_ rfl
        · rw [hk]
        · rw [hk]; exact PIR_congr (by ring) rfl
      · rw [hk]
        have : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
            (PIR (e : ℝ) f x j i ((u : ℝ) - t) m - PIR (e : ℝ) f x j i ((u : ℝ) - t) (m + 1)) = kapG (e : ℝ) f := by
          rw [cross_PIRg he0 hef]; ring
        rw [this]; linarith
    have hfc := fault_cover S (q := r) hr1 (PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) ((e : ℝ) * f) s (-1) (Or.inr rfl) hdn hef0
      hs0 hnon τ1 (PIR (e : ℝ) f x j i (u : ℝ) m) hE hA0 τ' W' hFo hR hT
    rw [hk] at hfc
    have hwcr : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) (wvec (e : ℝ) f x) ≠ 0 := by
      have h := cross_wvec_step he0 hef x j i ((u : ℝ) - 1) (m + 1)
      rw [sub_add_cancel] at h
      have e2 : cross (PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) (wvec (e : ℝ) f x) =
          cross (wvec (e : ℝ) f x) (PIR (e : ℝ) f x j i (u : ℝ) (m + 1) - PIR (e : ℝ) f x j i ((u : ℝ) - 1) (m + 1)) := by
        simp only [cross, PiLp.sub_apply]; ring
      rw [e2, h]; exact neg_ne_zero.mpr hκ.ne'
    exact edgecover_clash (Or.inr rfl) (Or.inl rfl) hwcr hfc hZc

end gen2

#print axioms chord_gen_inner

end Erdos634.Draft.WGapStmt
