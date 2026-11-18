/-
Draft/WGapSide3c.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 [SIDE-3]).
Not imported by any aggregate.  Module P-B3: `side3_fill`, the alpha-wedge at the BOUNDARY point `X = p'(xi, 0)`, `xi = j`, `1 <= j <= f-1` (hypotheses `Corner2`, `H4`):
known tiles `U'(xi-1,0)` [beta] and `D'(xi-1,0)` [gamma] (total `pi - alpha`, the total angle at `X` is `pi`, `bdry_total`); the wedge is filled by ONE alpha-tile adjacent to the UP-ray `X -> p'(xi,1)`
(`filler_alpha_left`: the known tile `D'(xi-1,0)` is on the RIGHT of the up-ray); it is `U'(xi,0)` or the flipped tile (`c`-edge on the up-ray).
`hint` of the ray is `interior_seg` (height and `gB` positive by `bdry_total`), the clamp is the angle count (`no_straddle_left`), not the boundary partition: the boundary ray (s') is never used.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapSide3b

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

/-- `same_third` for the LEFT side (both crosses positive): swap the roles of `X` and `P` -/
theorem same_third_left {X P Z W : Plane} (hXP : X ≠ P) (h1 : dist Z X = dist W X) (h2 : dist Z P = dist W P)
    (hz : 0 < cross (P - X) (Z - X)) (hw : 0 < cross (P - X) (W - X)) : Z = W := by
  refine same_third (X := P) (P := X) (Z := Z) (W := W) hXP.symm h2 h1 ?_ ?_
  · have : cross (X - P) (Z - P) = -cross (P - X) (Z - X) := by simp [cross]; ring
    rw [this]; linarith
  · have : cross (X - P) (W - P) = -cross (P - X) (W - X) := by simp [cross]; ring
    rw [this]; linarith

section side3

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
theorem side3_fill (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) {j : ℕ} (hj1 : 1 ≤ j)
    (hjf : j ≤ f - 1) (ξ : ℝ) (hξ : ξ = (j : ℝ))
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 0 ξ 0) (mpG (e : ℝ) f 1 0 (ξ - 1) 1) (mpG (e : ℝ) f 1 0 (ξ - 1) 0))
    (hD : ∃ t, HasV D t (mpG (e : ℝ) f 1 0 ξ 0) (mpG (e : ℝ) f 1 0 ξ 1) (mpG (e : ℝ) f 1 0 (ξ - 1) 1)) :
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 0 ξ 0) (mpG (e : ℝ) f 1 0 (ξ + 1) 0) (mpG (e : ℝ) f 1 0 ξ 1)) ∨
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 0 ξ 0) (mpG (e : ℝ) f 1 0 (ξ + nuG (e : ℝ) f) 0)
      (mpG (e : ℝ) f 1 0 ξ (1 / nuG (e : ℝ) f))) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hf0 : (0 : ℝ) < f := he0.trans hef
  obtain ⟨k1, h1⟩ := hU1
  obtain ⟨t0, h0⟩ := hD
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  obtain ⟨hαπ, hβπ, hγπ', -, -, -⟩ := angles_lt_pi S
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hmp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (mpG (e : ℝ) f 1 0 ξ1 η1) (mpG (e : ℝ) f 1 0 ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_mpG he0 hef 0 hd hq
  set X := mpG (e : ℝ) f 1 0 ξ 0 with hX
  set Y := mpG (e : ℝ) f 1 0 ξ 1 with hY
  have a1 : (D.tile k1).localAngle X = β :=
    ((h1.anglesG S.tile S.hM).2.1) (hmp _ hb0.le _ _ _ _ (by unfold QfG; ring))
  have a0 : (D.tile t0).localAngle X = γ :=
    ((h0.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have hne : k1 ≠ t0 := ne_of_angle (by rw [a1, a0]; exact hβγ.ne)
  set K : Finset (Fin N) := {t0, k1} with hKdef
  have hXt : X ∈ D.target.carrier := h0.mem₁
  obtain ⟨hΩ, hXy, hXgB⟩ := bdry_total S h2 hH4 hj1 hjf (by rw [← hξ]; exact hXt)
  rw [← hξ] at hΩ hXy hXgB
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = Real.pi - α := by
    rw [hKdef, Finset.sum_pair hne.symm, a0, a1]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have hXY : X ≠ Y := by
    intro h
    obtain ⟨-, h2'⟩ := mpG_inj he0 hef h
    linarith
  have hYt : Y ∈ D.target.carrier := h0.mem₂
  have hint : openSegment ℝ X Y ⊆ interior D.target.carrier := by
    refine S.interior_seg hXt hYt (Or.inl hXy) (Or.inr ?_) (Or.inl hXgB)
    obtain ⟨t, ht, hax, hay'⟩ := h2
    rw [hax, hay', hY, gA_mp he0 hef t ξ 1]
    have hr := rtG_pos he0 hef
    have := mul_pos (mul_pos (mul_pos (mul_pos ht he0) hr) S.c_pos) hb0
    linarith [this]
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
  have hclamp := no_straddle_left D.toDissection hXY hP' hXP hΩ K (θ := α) (by rw [hKsum]) hαπ hKlt
  have hZ : cross (Y - X) (mpG (e : ℝ) f 1 0 (ξ - 1) 1 - X) < 0 := by
    rw [hX, hY, cross_mpG he0 hef]
    have := kapG_pos he0 hef
    nlinarith
  have hV0 : HasV D t0 X Y (mpG (e : ℝ) f 1 0 (ξ - 1) 1) := h0
  have hKray : ∀ k ∈ K, k ≠ t0 → ∀ (j : Fin 3) (s : ℝ), 0 < s →
      (D.tile k).pts j ≠ AffineMap.lineMap X Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact absurd rfl hkt
    · exact known_off_ray hXY h1 (mp_off_ray2 he0 hef 0 ξ 0 ξ 1 _ _ (by norm_num) (Or.inl (by norm_num)))
        (mp_off_ray2 he0 hef 0 ξ 0 ξ 1 _ _ (by norm_num) (Or.inl (by norm_num)))
  obtain ⟨τ, hτK, P, W, hV, ⟨s, hs, hPs⟩, hW, hang, hPW, hsides⟩ :=
    filler_alpha_left S hXY hV0 hZ hP' hXP hint hclamp hΩ K (by rw [hKsum]) hKray
  have hP2 : P = mpG (e : ℝ) f 1 0 ξ s := by
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
  have hκ := kapG_pos he0 hef
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
    have hWc : mpG (e : ℝ) f 1 0 (ξ + nuG (e : ℝ) f) 0 = W := by
      refine same_third_left hXPne ?_ ?_ ?_ hz0
      · rw [dist_comm W X, hd2, hX]
        exact hmp _ hb0.le _ _ _ _ (by unfold QfG nuG; field_simp; ring)
      · rw [dist_comm W P, hPW, hP2]
        have q := qf_flip2 he0 hef ξ 0
        rw [zero_add] at q
        exact hmp _ (by positivity) _ _ _ _ q
      · rw [hP2, hX, cross_mpG he0 hef]
        have e1 : (ξ - ξ) * (0 - 0) - (1 / nuG (e : ℝ) f - 0) * (ξ + nuG (e : ℝ) f - ξ) = -1 := by
          field_simp; ring
        rw [e1]; linarith
    right
    refine ⟨τ, ?_⟩
    have := hV.swap.rot
    rw [← hWc, hP2] at this
    exact this
  · -- b on the up-ray: U'(xi, 0)
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
    have hWc : mpG (e : ℝ) f 1 0 (ξ + 1) 0 = W := by
      refine same_third_left hXPne ?_ ?_ ?_ hz0
      · rw [dist_comm W X, hd2, hX]
        exact hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring)
      · rw [dist_comm W P, hPW, hP2]
        exact hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring)
      · rw [hP2, hX, cross_mpG he0 hef]
        have e1 : (ξ - ξ) * (0 - 0) - (1 - 0) * (ξ + 1 - ξ) = -1 := by ring
        rw [e1]; linarith
    left
    refine ⟨τ, ?_⟩
    have := hV.swap.rot
    rw [← hWc, hP2] at this
    exact this

end side3

end Erdos634.Draft.WGapStmt
