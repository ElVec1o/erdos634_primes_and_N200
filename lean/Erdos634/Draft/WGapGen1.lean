/-
Draft/WGapGen1.lean -- written 16 November 2026 (session 15).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, chord step, GENERAL chord length).
Not imported by any aggregate.  No sorry, no native_decide.
`chord_gen_first`: generalization of `chord2_first` (WGapRL21) from the two-edge chord at `i = 2, m = 0` to every chord of `k` lattice `a`-edges
`[pi(a,m+1), pi(a-k,m+1)]` of the tiles `gamma(a-t, m)`, `t < k`, at every layer `m` and every `i`: the first tile above the chord (beside the bottom end) is `nu(a-1,m+1)`;
the `c`-edge alternative is killed by `fault_cover` (q = k) against the cover at the top end (`nonmem_ma_sub_c`, multiplier `k <= f-1`).
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

section gen1

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem chord_gen_first (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i a k : ℕ) (m : ℝ)
    (hk1 : 1 ≤ k) (hka : k ≤ a) (hkf : k ≤ f - 1) {tNa : Fin N} {d : Plane}
    (hNa : HasV D tNa (PIR (e : ℝ) f x j i ((a : ℝ) + 1) m) (PIR (e : ℝ) f x j i (a : ℝ) m)
      (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)))
    (hΓ : ∀ t : ℕ, t < k → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((a : ℝ) - t) m) (PIR (e : ℝ) f x j i ((a : ℝ) - t) (m + 1))
        (PIR (e : ℝ) f x j i ((a : ℝ) - t - 1) (m + 1)))
    (hΞ : EdgeCoverS D (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) d (-1))
    (hcr : 0 < cross d (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)))
    (hZc : EdgeCoverS D (PIR (e : ℝ) f x j i ((a : ℝ) - k) (m + 1)) (wvec (e : ℝ) f x) 1) :
    ∃ τν : Fin N, HasV D τν (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1))
      (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1 + 1)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hκ := kapG_pos he0 hef
  have hν0 := nuG_pos he0 hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  obtain ⟨τ0, hΓ0'⟩ := hΓ 0 (by omega)
  have hΓ0 : HasV D τ0 (PIR (e : ℝ) f x j i (a : ℝ) m) (PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1)) :=
    hasV_congr hΓ0' (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl)
  have d1 : dist (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1)) = (e : ℝ) * f := by
    have := dPIR_a he0 hef x j i ((a : ℝ) - 1) (m + 1)
    rwa [sub_add_cancel] at this
  have d2 : dist (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1 + 1)) (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) = (f : ℝ) ^ 2 := by
    have := dPIR_c he0 hef x j i ((a : ℝ) - 1) (m + 1)
    rw [sub_add_cancel] at this
    rw [dist_comm]; exact this
  have d3 : dist (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1 + 1)) (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1)) =
      (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := dPIR_b he0 hef x j i ((a : ℝ) - 1) (m + 1)
    rw [dist_comm]; exact this
  have dNa : dist (PIR (e : ℝ) f x j i ((a : ℝ) + 1) m) (PIR (e : ℝ) f x j i (a : ℝ) m) = (e : ℝ) * f :=
    dPIR_a he0 hef x j i (a : ℝ) m
  have dCO : dist (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1)) (PIR (e : ℝ) f x j i (a : ℝ) m) = (f : ℝ) ^ 2 := by
    have := dPIR_c he0 hef x j i ((a : ℝ) - 1) m
    rw [sub_add_cancel] at this
    rw [dist_comm]; exact this
  have hXY : PIR (e : ℝ) f x j i (a : ℝ) (m + 1) ≠ PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) := by
    intro h
    have h1 := d1
    rw [h, dist_self] at h1
    linarith
  have hz : 0 < cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i (a : ℝ) m - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) := by
    have : cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (a : ℝ) m - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) = kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; ring
    rw [this]; exact hκ
  have hW0 : cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1 + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) < 0 := by
    have : cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1 + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) = -kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; ring
    rw [this]; linarith
  have aG : (D.tile τ0).localAngle (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) = γ :=
    (hΓ0.rot.anglesG S.tile S.hM).2.2 dCO
  have aN : (D.tile tNa).localAngle (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) = α :=
    (hNa.rot.rot.anglesG S.tile S.hM).1 dNa
  have hNray := known_off_ray hXY hNa.rot.rot
    (off_PIRg he0 hef x j i (a : ℝ) (m + 1) ((a : ℝ) - 1) (m + 1) ((a : ℝ) + 1) m (by intro h; nlinarith [h]))
    (off_PIRg he0 hef x j i (a : ℝ) (m + 1) ((a : ℝ) - 1) (m + 1) (a : ℝ) m (by intro h; nlinarith [h]))
  have hk : ∀ k' : ℝ, PIR (e : ℝ) f x j i (a : ℝ) (m + 1) +
      k' • (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) =
      PIR (e : ℝ) f x j i ((a : ℝ) - k') (m + 1) := fun k' => PIR_lin he0 hef x j i (a : ℝ) (m + 1) k'
  have hwcr : cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) (wvec (e : ℝ) f x) ≠ 0 := by
    have h := cross_wvec_step he0 hef x j i ((a : ℝ) - 1) (m + 1)
    rw [sub_add_cancel] at h
    have e1 : cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) (wvec (e : ℝ) f x) =
        cross (wvec (e : ℝ) f x) (PIR (e : ℝ) f x j i (a : ℝ) (m + 1) - PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1)) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [e1, h]; linarith
  refine chord_first S (Z := PIR (e : ℝ) f x j i (a : ℝ) m) (W0 := PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1 + 1))
    (tG := τ0) (tN := tNa) hXY hΓ0.rot hz aG aN hΞ hcr hNray ?_ d1 d2 d3 hW0
  -- the `c`-edge case: `fault_cover` against the cover at the top end
  intro τ' P W hV ⟨s, hs0, hPs⟩ hWcr hdc
  have hdXP : dist (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) P = s * ((e : ℝ) * f) := by
    rw [hPs, dist_left_lineMap, Real.norm_of_nonneg hs0.le, d1]
  have hlu : s * ((e : ℝ) * f) = (f : ℝ) ^ 2 := by rw [← hdXP, hdc]
  have hdn : ‖PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)‖ = (e : ℝ) * f := by
    rw [← dist_eq_norm, dist_comm]; exact d1
  have hnon : ∀ x' y' z' : ℕ, s * ((e : ℝ) * f) + ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) ≠
      (k : ℝ) * ((e : ℝ) * f) := by
    intro x' y' z' h
    rw [hlu] at h
    have hZR : ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) =
        (k : ℝ) * ((e : ℝ) * f) - (f : ℝ) ^ 2 := by linarith
    have hZI : (x' : ℤ) * ((e : ℤ) * f) + (y' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z' : ℤ) * (f : ℤ) ^ 2 =
        (k : ℤ) * ((e : ℤ) * f) - (f : ℤ) ^ 2 := by exact_mod_cast hZR
    exact Erdos634.Draft.WGapArith.nonmem_ma_sub_c S.he S.hef S.hco (m := k) hk1 hkf ⟨x', y', z', hZI⟩
  have hE : HasV D τ0 (PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i (a : ℝ) (m + 1) + (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)))
      (PIR (e : ℝ) f x j i (a : ℝ) m) := hasV_congr hΓ0.rot rfl (by abel) rfl
  have hA0 : (-1 : ℝ) * cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i (a : ℝ) m - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) < 0 := by
    have : cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (a : ℝ) m - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) = kapG (e : ℝ) f := by
      rw [cross_PIRg he0 hef]; ring
    rw [this]; linarith
  have hFo : HasV D τ' (PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
      (PIR (e : ℝ) f x j i (a : ℝ) (m + 1) + s • (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))) W :=
    hasV_congr hV rfl (by rw [hPs, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]) rfl
  have hR : 0 < (-1 : ℝ) * cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
      (W - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) := by linarith
  have hT : ∀ t : ℕ, t < k → ∃ (T : Fin N) (A : Plane),
      HasV D T (PIR (e : ℝ) f x j i (a : ℝ) (m + 1) + (t : ℝ) • (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)))
        (PIR (e : ℝ) f x j i (a : ℝ) (m + 1) + ((t : ℝ) + 1) • (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))) A ∧
      (-1 : ℝ) * cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
        (A - (PIR (e : ℝ) f x j i (a : ℝ) (m + 1) + (t : ℝ) • (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)))) < 0 := by
    intro t ht
    obtain ⟨T, hT'⟩ := hΓ t ht
    refine ⟨T, PIR (e : ℝ) f x j i ((a : ℝ) - t) m, ?_, ?_⟩
    · refine hasV_congr hT'.rot ?_ ?_ rfl
      · rw [hk]
      · rw [hk]; exact PIR_congr (by ring) rfl
    · rw [hk]
      have : cross (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
          (PIR (e : ℝ) f x j i ((a : ℝ) - t) m - PIR (e : ℝ) f x j i ((a : ℝ) - t) (m + 1)) = kapG (e : ℝ) f := by
        rw [cross_PIRg he0 hef]; ring
      rw [this]; linarith
  have hfc := fault_cover S (q := k) hk1 (PIR (e : ℝ) f x j i (a : ℝ) (m + 1))
    (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) ((e : ℝ) * f) s (-1) (Or.inr rfl) hdn hef0
    hs0 hnon τ0 (PIR (e : ℝ) f x j i (a : ℝ) m) hE hA0 τ' W hFo hR hT
  rw [hk] at hfc
  exact edgecover_clash (Or.inr rfl) (Or.inl rfl) hwcr hfc hZc

end gen1

#print axioms chord_gen_first

end Erdos634.Draft.WGapStmt
