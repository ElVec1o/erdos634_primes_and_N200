/-
Draft/WGapStSide3.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapSide3c` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStSide

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}


open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv ub ClampB FlipAt Bst bst_self ub_norm ub_ne clampB_outside clampB_tile

section stside3

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

set_option maxHeartbeats 2000000 in
/-- **[SIDE-3] at a station**: the alpha-wedge at the wall point `q'(ξ,η0)` (`ξ = c`, `η0 = J0`): `U'(ξ,η0)` or the flipped tile.  The wall tile `φ` (angle `π`, in the closed
half-plane above `L_O`) replaces the cone of the side `s'`; the total angle at the (interior) point is `2π`. -/
theorem side3_fill_st (S : SetupG D e f α β γ L ax ay) (ξ η0 : ℝ)
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η0) (mpG (e : ℝ) f 1 x (ξ - 1) (η0 + 1)) (mpG (e : ℝ) f 1 x (ξ - 1) η0))
    (hD : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η0) (mpG (e : ℝ) f 1 x ξ (η0 + 1)) (mpG (e : ℝ) f 1 x (ξ - 1) (η0 + 1)))
    (hWt : EdgeCover D (mpG (e : ℝ) f 1 x ξ η0) (mpG (e : ℝ) f 1 x 1 η0 - mpG (e : ℝ) f 1 x 0 η0)) :
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x ξ η0) (mpG (e : ℝ) f 1 x (ξ + 1) η0) (mpG (e : ℝ) f 1 x ξ (η0 + 1))) ∨
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x ξ η0) (mpG (e : ℝ) f 1 x (ξ + nuG (e : ℝ) f) η0)
      (mpG (e : ℝ) f 1 x ξ (η0 + 1 / nuG (e : ℝ) f))) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hf0 : (0 : ℝ) < f := he0.trans hef
  obtain ⟨k1, h1⟩ := hU1
  obtain ⟨t0, h0⟩ := hD
  obtain ⟨φ, hφX, hφang, hφpush⟩ := hWt
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  obtain ⟨hαπ, hβπ, hγπ', -, -, -⟩ := angles_lt_pi S
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hmp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (mpG (e : ℝ) f 1 x ξ1 η1) (mpG (e : ℝ) f 1 x ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_mpG he0 hef x hd hq
  set X := mpG (e : ℝ) f 1 x ξ η0 with hX
  set Y := mpG (e : ℝ) f 1 x ξ (η0 + 1) with hY
  have a1 : (D.tile k1).localAngle X = β :=
    ((h1.anglesG S.tile S.hM).2.1) (hmp _ hb0.le _ _ _ _ (by unfold QfG; ring))
  have a0 : (D.tile t0).localAngle X = γ :=
    ((h0.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have hne : k1 ≠ t0 := ne_of_angle (by rw [a1, a0]; exact hβγ.ne)
  have hφk1 : φ ≠ k1 := ne_of_angle (by rw [hφang, a1]; exact (by linarith : Real.pi ≠ β))
  have hφt0 : φ ≠ t0 := ne_of_angle (by rw [hφang, a0]; exact (by linarith : Real.pi ≠ γ))
  set K : Finset (Fin N) := {t0, k1} with hKdef
  have hφK : φ ∉ K := by
    rw [hKdef]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hφt0, hφk1⟩
  have hXt : X ∈ D.target.carrier := h0.mem₁
  have hYt : Y ∈ D.target.carrier := h0.mem₂
  have hr := hA.hrel
  have hg := hA.hγdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = β + γ := by
    rw [hKdef, Finset.sum_pair hne.symm, a0, a1]; ring
  have hK3 : ∑ i ∈ insert φ K, (D.tile i).localAngle X = 2 * Real.pi - α := by
    rw [Finset.sum_insert hφK, hφang, hKsum]; linarith
  have hXint : X ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hXt (insert φ K) ?_
    rw [Finset.sum_insert hφK, hφang, hKsum]; linarith
  have hΩ : ∑ i, (D.tile i).localAngle X = 2 * Real.pi := (D.toDissection.hasAngleSums).1 X hXint
  have hXY : X ≠ Y := by
    intro h
    obtain ⟨-, h2'⟩ := mpG_inj he0 hef h
    linarith
  have hint : openSegment ℝ X Y ⊆ interior D.target.carrier := openSeg_interior D.toDissection hXint hYt
  have hP' : cross (Y - X) ((X - (Y - X)) - X) = 0 := by
    simp [cross]; ring
  have hXP : X ∈ openSegment ℝ (X - (Y - X)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle X < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rw [a0]; exact hγπ'
    · rw [a1]; exact hβπ
  have hκ := kapG_pos he0 hef
  have hWh := edgeCover_halfplane φ hφang hφpush
  have hdu : cross (mpG (e : ℝ) f 1 x 1 η0 - mpG (e : ℝ) f 1 x 0 η0) (Y - X) < 0 := by
    rw [hX, hY, cross_mpG he0 hef]
    have e1 : ((1 : ℝ) - 0) * ((η0 + 1) - η0) - (η0 - η0) * (ξ - ξ) = 1 := by ring
    rw [e1]; linarith
  have hclamp := no_straddle_wall D.toDissection hXY hP' hXP hΩ K φ hφK hφang
    (θ := α) (by rw [hKsum]; linarith) hαπ hKlt hWh hdu
  have hZ : cross (Y - X) (mpG (e : ℝ) f 1 x (ξ - 1) (η0 + 1) - X) < 0 := by
    rw [hX, hY, cross_mpG he0 hef]
    have e1 : (ξ - ξ) * ((η0 + 1) - η0) - ((η0 + 1) - η0) * ((ξ - 1) - ξ) = 1 := by ring
    rw [show (ξ - ξ) * (η0 + 1 - η0) - (η0 + 1 - η0) * (ξ - 1 - ξ) = 1 by ring]
    linarith
  have hV0 : HasV D t0 X Y (mpG (e : ℝ) f 1 x (ξ - 1) (η0 + 1)) := h0
  have hKray : ∀ k ∈ insert φ K, k ≠ t0 → ∀ (j : Fin 3) (s : ℝ), 0 < s →
      (D.tile k).pts j ≠ AffineMap.lineMap X Y s := by
    intro k hk hkt j s hs hv
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · have hmem : (D.tile k).pts j ∈ (D.tile k).carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
      have h0' := hWh _ hmem
      rw [hv] at h0'
      have e2 : cross (mpG (e : ℝ) f 1 x 1 η0 - mpG (e : ℝ) f 1 x 0 η0) (AffineMap.lineMap X Y s - X) =
          s * cross (mpG (e : ℝ) f 1 x 1 η0 - mpG (e : ℝ) f 1 x 0 η0) (Y - X) := by
        rw [AffineMap.lineMap_apply]; simp [cross]; ring
      rw [e2] at h0'
      nlinarith
    · rw [hKdef] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact absurd rfl hkt
      · exact known_off_ray hXY h1 (mp_off_ray2 he0 hef x ξ η0 ξ (η0 + 1) _ _ (by nlinarith) (Or.inl (by intro h; nlinarith [h])))
          (mp_off_ray2 he0 hef x ξ η0 ξ (η0 + 1) _ _ (by nlinarith) (Or.inl (by intro h; nlinarith [h]))) j s hs hv
  obtain ⟨τ, hτK, P, W, hV, ⟨s, hs, hPs⟩, hW, hang, hPW, hsides⟩ :=
    filler_alpha_left S hXY hV0 hZ hP' hXP hint hclamp hΩ (insert φ K) hK3 hKray
  have hP2 : P = mpG (e : ℝ) f 1 x ξ (η0 + s) := by
    rw [hPs, hX, hY, lineMap_mpG he0 hef]
    exact mpG_congr' (by ring) (by ring)
  have hdXP : dist X P ^ 2 = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 * s ^ 2 := by
    rw [hP2, hX, dist_mpG_sq he0 hef]
    unfold QfG; ring
  have hPX : P - X = s • (Y - X) := by
    rw [hPs, AffineMap.lineMap_apply]; simp
  have hz0 : 0 < cross (P - X) (W - X) := by
    rw [hPX, cross_smul_left']
    exact mul_pos hs hW
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := S.c_pos
  rcases hsides with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
  · -- c on the up-ray: the flipped tile
    have hbs : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s = (f : ℝ) ^ 2 := by
      have h := hdXP
      rw [hd1] at h
      have h' : (f : ℝ) ^ 2 = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s :=
        (sq_eq_sq₀ hf2.le (by positivity : (0 : ℝ) ≤ ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s)).mp (by rw [h]; ring)
      exact h'.symm
    have hν := nuG_spec he0 hef
    have hνpos := nuG_pos he0 hef
    have hs1 : s = 1 / nuG (e : ℝ) f := by
      field_simp
      nlinarith
    subst hs1
    have hXPne : X ≠ P := by
      intro h; rw [← h, dist_self] at hd1; exact hf2.ne hd1
    have hWc : mpG (e : ℝ) f 1 x (ξ + nuG (e : ℝ) f) η0 = W := by
      refine same_third_left hXPne ?_ ?_ ?_ hz0
      · rw [dist_comm W X, hd2, hX]
        exact hmp _ hb0.le _ _ _ _ (by unfold QfG nuG; field_simp; ring)
      · rw [dist_comm W P, hPW, hP2]
        have q := qf_flip2 he0 hef ξ η0
        exact hmp _ (by positivity) _ _ _ _ q
      · rw [hP2, hX, cross_mpG he0 hef]
        have e1 : (ξ - ξ) * (η0 - η0) - ((η0 + 1 / nuG (e : ℝ) f) - η0) * ((ξ + nuG (e : ℝ) f) - ξ) = -1 := by
          field_simp; ring
        rw [e1]; linarith
    right
    refine ⟨τ, ?_⟩
    have := hV.swap.rot
    rw [← hWc, hP2] at this
    exact this
  · -- b on the up-ray: U'(xi, eta0)
    have hs1 : s = 1 := by
      have h := hdXP
      rw [hd1] at h
      have h' : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s :=
        (sq_eq_sq₀ hb0.le (by positivity : (0 : ℝ) ≤ ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s)).mp (by rw [h]; ring)
      have := mul_left_cancel₀ hb0.ne' (h'.symm.trans (mul_one _).symm)
      exact this
    subst hs1
    have hXPne : X ≠ P := by
      intro h; rw [← h, dist_self] at hd1; exact hb0.ne hd1
    have hWc : mpG (e : ℝ) f 1 x (ξ + 1) η0 = W := by
      refine same_third_left hXPne ?_ ?_ ?_ hz0
      · rw [dist_comm W X, hd2, hX]
        exact hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring)
      · rw [dist_comm W P, hPW, hP2]
        exact hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring)
      · rw [hP2, hX, cross_mpG he0 hef]
        have e1 : (ξ - ξ) * (η0 - η0) - ((η0 + 1) - η0) * ((ξ + 1) - ξ) = -1 := by ring
        rw [e1]; linarith
    left
    refine ⟨τ, ?_⟩
    have := hV.swap.rot
    rw [← hWc, hP2] at this
    exact this

end stside3

end Erdos634.Draft.WGapSt
