/-
Draft/WGapSetupF2.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P11.3, FINDING F2).
Not imported by any aggregate.  A COPY of `SideRunGA.setup_of_corners` (SideRunGCornerMain.lean, not edited) whose output carries ONE MORE fact, the one the original hides in its
existential: **the length of the second side `s' = [Q, A]` of the normal form**, `dist (mkPt ax ay) (mkPt 0 0) = dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))` (in the proof it is `hdA`).
This gives (H4) for `W_M` from the side `|AB| = M f^3`.  The proof is the original one, line for line, with the extra conjunct.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerMain

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Set

variable {N : ℕ}

/-- **THE NORMAL FORM OF A SIDE FROM A CORNER `A'` OF ANGLE `2α` OR `3α` TO A CORNER `Q'` OF ANGLE `β` OR `α + β`** (corners given by `cornerAngle`; the vertices named by `τ`: `τ 0 = A'`, `τ 1 = Q'`, `τ 2` the third vertex). -/
theorem setup_of_corners_F2 (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (L ax ay : ℝ),
      0 < L ∧ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L ∧
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧ g (D₀.target.pts (τ 1)) = mkPt L 0 ∧
      ∃ S : SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
          (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L ax ay,
        CornersA e f L ax ay ∧
        (cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
            2 * modelAlpha (e : ℝ) (f : ℝ) →
          D.target.localAngle (mkPt 0 0) = 2 * modelAlpha (e : ℝ) (f : ℝ)) ∧
        dist (mkPt ax ay) (mkPt 0 0) = dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  obtain ⟨hβ0, hβ2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith
  have hpi := Real.pi_pos
  have hT := D₀.target.indep.injective
  have h01 : D₀.target.pts (τ 0) ≠ D₀.target.pts (τ 1) :=
    fun h => absurd (τ.injective (hT h)) (by decide)
  have h02 : D₀.target.pts (τ 0) ≠ D₀.target.pts (τ 2) :=
    fun h => absurd (τ.injective (hT h)) (by decide)
  have h12 : D₀.target.pts (τ 1) ≠ D₀.target.pts (τ 2) :=
    fun h => absurd (τ.injective (hT h)) (by decide)
  obtain ⟨L, hLdef⟩ : ∃ L, L = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := ⟨_, rfl⟩
  obtain ⟨d1, hd1def⟩ : ∃ d1, d1 = dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) := ⟨_, rfl⟩
  obtain ⟨d2, hd2def⟩ : ∃ d2, d2 = dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; exact dist_pos.mpr h01
  have hd1 : 0 < d1 := by rw [hd1def]; exact dist_pos.mpr h02.symm
  have hd2 : 0 < d2 := by rw [hd2def]; exact dist_pos.mpr h12.symm
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
    (D₀.target.pts (τ 1)) := ⟨_, rfl⟩
  obtain ⟨θQ, hθQdef⟩ : ∃ θQ, θQ = cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
    (D₀.target.pts (τ 2)) := ⟨_, rfl⟩
  have hA' : θ = 2 * modelAlpha (e : ℝ) (f : ℝ) ∨ θ = 3 * modelAlpha (e : ℝ) (f : ℝ) := by
    rw [hθdef]; exact hA
  have hQ' : θQ = modelBeta (e : ℝ) (f : ℝ) ∨ θQ = modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := by
    rw [hθQdef]; exact hQ
  have hθ0 : 0 < θ := by rcases hA' with h | h <;> rw [h] <;> linarith
  have hθπ : θ < Real.pi := by rcases hA' with h | h <;> rw [h] <;> linarith
  have hθQ0 : 0 < θQ := by rcases hQ' with h | h <;> rw [h] <;> linarith
  have hθQπ : θQ < Real.pi := by rcases hQ' with h | h <;> rw [h] <;> linarith
  -- the laws of cosines at `A'` and `Q'`
  have e_rp : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d1 := hd1def.symm
  have e_rq : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) = d2 := hd2def.symm
  have e_pq : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L := hLdef.symm
  have e_qp : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 0)) = L := by rw [dist_comm]; exact e_pq
  have e_pr : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 2)) = d1 := by rw [dist_comm]; exact e_rp
  have e_qr : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d2 := by rw [dist_comm]; exact e_rq
  have lawA : d2 ^ 2 = d1 ^ 2 + L ^ 2 - 2 * d1 * L * Real.cos θ := by
    have h := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
    rw [e_rq, e_rp, e_qp] at h
    have hc : Real.cos (EuclideanGeometry.angle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
        (D₀.target.pts (τ 1))) = Real.cos θ := by rw [hθdef]; rfl
    rw [hc] at h
    linear_combination h
  have lawQ : d1 ^ 2 = d2 ^ 2 + L ^ 2 - 2 * d2 * L * Real.cos θQ := by
    have h := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2))
    rw [e_pr, e_pq, e_rq] at h
    have hc : Real.cos (EuclideanGeometry.angle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
        (D₀.target.pts (τ 2))) = Real.cos θQ := by rw [hθQdef]; rfl
    rw [hc] at h
    linear_combination h
  -- the apex
  obtain ⟨hay, hdQ, hdA⟩ := apex_dists hd1 hd2.le hθ0 hθπ lawA
  obtain ⟨D, g, hD, hP, hB, S⟩ := setup_of_apex_pinned e f he hef hco (L := L)
    (ax := d1 * Real.cos θ) (ay := d1 * Real.sin θ) hL hay D₀ τ
    (by rw [hdQ, dist_comm, ← hd2def]) (by rw [hdA, ← hd1def]) hLdef.symm hMod
  -- the right corner: `L − ax = d₂ cos θ_Q`, `ay = d₂ sin θ_Q`
  have hLsum : L = d1 * Real.cos θ + d2 * Real.cos θQ := by
    have h : L * (L - d1 * Real.cos θ - d2 * Real.cos θQ) = 0 := by
      linear_combination (-1 / 2 : ℝ) * lawA + (-1 / 2 : ℝ) * lawQ
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hL.ne'
    · linarith
  have hsinQ : d1 * Real.sin θ = d2 * Real.sin θQ := by
    have hsθ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    have hsQ := Real.sin_pos_of_pos_of_lt_pi hθQ0 hθQπ
    have hidA := Real.cos_sq_add_sin_sq θ
    have hidQ := Real.cos_sq_add_sin_sq θQ
    refine eq_of_sq_pos (mul_pos hd1 hsθ) (mul_pos hd2 hsQ) ?_
    linear_combination d1 ^ 2 * hidA - d2 ^ 2 * hidQ - lawA
      - (d2 * Real.cos θQ + L - d1 * Real.cos θ) * hLsum
  have hCo : CornersA e f L (d1 * Real.cos θ) (d1 * Real.sin θ) :=
    cornersA_of_coords S hd1 hd2 rfl rfl hA' (by linarith) hsinQ hQ'
  refine ⟨D, g, L, d1 * Real.cos θ, d1 * Real.sin θ, hL, hLdef.symm, hD, hP, hB, S, hCo, ?_, ?_⟩
  swap
  · rw [hdA, ← hd1def]
  intro h2
  have h2' : θ = 2 * modelAlpha (e : ℝ) (f : ℝ) := by rw [hθdef]; exact h2
  obtain ⟨t, ht, hax2, hay2⟩ := leftForm_two S hd1 h2' rfl rfl
  exact corner_left_two S ht hax2 hay2

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.setup_of_corners_F2
