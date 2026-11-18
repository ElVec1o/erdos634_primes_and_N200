/-
Draft/WGapW2.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (use W2 of WEDGE_USES.md, P5 "far half-plane").
Not imported by any aggregate.  Module W4a: the FIRST USE of the wedge API (the `α`-wedge at a mirror lattice point), written to test the design.

Setting (mirror coordinates, real `ξ η`, `X = p'(ξ, η)`; sectors from PROOF 3.3, counter-clockwise from `α`):
 `U'(ξ,η-1) [γ]`, `D'(ξ-1,η-1) [α]`, `U'(ξ-1,η) [β]`, `D'(ξ-1,η) [γ]`, `D'(ξ,η-1) [β]` are tiles (five known tiles, total `2π - α`).
Then the free wedge `(α, 2α)` is one `α`-tile, with `b`, `c` on its two bounding rays in either order:
 `w2_fill` : `U'(ξ,η)` (c on the ray `X → p'(ξ+1,η)`, b along `l'`) OR the flipped tile with vertices `X`, `p'(ξ+ν, η)`, `p'(ξ, η + c/b)` (`ν = b/c`).
The hypotheses of `filler_alpha` are discharged here: `hint` by `openSeg_interior` (X interior by `interior_of_sum`), `hclamp` by `no_straddle` (angle count),
`hKray` by mirror-coordinate sign facts (`mpG_inj`), the identification of the two vertices by `same_third`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLat

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

variable {N : ℕ} {D : CongruentDissection N} {t : Fin N} {A B C : Plane}

theorem sum_five (g : Fin N → ℝ) {a b c d e : Fin N} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : a ≠ e)
    (h5 : b ≠ c) (h6 : b ≠ d) (h7 : b ≠ e) (h8 : c ≠ d) (h9 : c ≠ e) (h10 : d ≠ e) :
    ∑ i ∈ ({a, b, c, d, e} : Finset (Fin N)), g i = g a + g b + g c + g d + g e := by
  simp [Finset.sum_insert, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

/-- mirror-coordinate sign facts: a point `p'(a,b)` with `b ≠ η` or `a ≤ ξ` is not on the open ray `X → p'(ξ+1, η)` -/
theorem mp_off_ray {e f : ℝ} (he : 0 < e) (hef : e < f) (x ξ η a b : ℝ) (h : b ≠ η ∨ a ≤ ξ) :
    ∀ s : ℝ, 0 < s → mpG e f 1 x a b ≠ AffineMap.lineMap (mpG e f 1 x ξ η) (mpG e f 1 x (ξ + 1) η) s := by
  intro s hs hh
  rw [lineMap_mpG he hef] at hh
  obtain ⟨h1, h2⟩ := mpG_inj he hef hh
  rcases h with h | h
  · apply h; linarith
  · nlinarith

theorem mpG_congr' {e f x ξ η ξ' η' : ℝ} (h1 : ξ = ξ') (h2 : η = η') :
    mpG e f 1 x ξ η = mpG e f 1 x ξ' η' := by rw [h1, h2]

theorem hasV_third (h : HasV D t A B C) : ∃ i, (D.tile t).pts i = C := by
  obtain ⟨k, m, j, -, -, -, -, -, hj⟩ := h; exact ⟨j, hj⟩

theorem hasV_second (h : HasV D t A B C) : ∃ i, (D.tile t).pts i = B := by
  obtain ⟨k, m, j, -, -, -, -, hm, -⟩ := h; exact ⟨m, hm⟩

theorem qf_flip1 {e f : ℝ} (he : 0 < e) (hef : e < f) (ξ η : ℝ) :
    QfG e f (ξ - ξ) (η - (η + 1 / nuG e f)) = (f ^ 2) ^ 2 := by
  have hf : 0 < f := he.trans hef
  have hb : f ^ 2 - e ^ 2 ≠ 0 := by nlinarith
  unfold QfG nuG
  field_simp
  ring

theorem qf_flip2 {e f : ℝ} (he : 0 < e) (hef : e < f) (ξ η : ℝ) :
    QfG e f (ξ + nuG e f - ξ) (η - (η + 1 / nuG e f)) = (e * f) ^ 2 := by
  have hf : 0 < f := he.trans hef
  have hb : f ^ 2 - e ^ 2 ≠ 0 := by nlinarith
  unfold QfG nuG
  field_simp
  ring

section w2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
/-- **W2**: the `α`-wedge `(α, 2α)` at the mirror lattice point `X = p'(ξ, η)` (see the module header). -/
theorem w2_fill (S : SetupG D e f α β γ L ax ay) (x ξ η : ℝ)
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ - 1) (η + 1)) (mpG (e : ℝ) f 1 x (ξ - 1) η))
    (hU2 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x ξ (η - 1)) (mpG (e : ℝ) f 1 x (ξ + 1) (η - 1)))
    (hD1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x ξ (η - 1)) (mpG (e : ℝ) f 1 x (ξ - 1) η))
    (hD2 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ - 1) (η + 1)) (mpG (e : ℝ) f 1 x ξ (η + 1)))
    (hD3 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ + 1) η) (mpG (e : ℝ) f 1 x (ξ + 1) (η - 1))) :
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ + 1) η) (mpG (e : ℝ) f 1 x ξ (η + 1))) ∨
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ + nuG (e : ℝ) f) η)
      (mpG (e : ℝ) f 1 x ξ (η + 1 / nuG (e : ℝ) f))) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hf0 : (0 : ℝ) < f := he0.trans hef
  obtain ⟨k1, h1⟩ := hU1
  obtain ⟨k2, h2⟩ := hU2
  obtain ⟨k3, h3⟩ := hD1
  obtain ⟨k4, h4⟩ := hD2
  obtain ⟨t0, h0⟩ := hD3
  set X := mpG (e : ℝ) f 1 x ξ η with hX
  set Y := mpG (e : ℝ) f 1 x (ξ + 1) η with hY
  -- distances
  have dc : ∀ ξ' η' : ℝ, QfG (e : ℝ) f 1 0 = ((f : ℝ) ^ 2) ^ 2 := fun _ _ => by unfold QfG; ring
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  obtain ⟨hαπ, hβπ, hγπ', -, -, -⟩ := angles_lt_pi S
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hmp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (mpG (e : ℝ) f 1 x ξ1 η1) (mpG (e : ℝ) f 1 x ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_mpG he0 hef x hd hq
  -- the angles of the five known tiles at X
  have a1 : (D.tile k1).localAngle X = β :=
    ((h1.anglesG S.tile S.hM).2.1) (hmp _ hb0.le _ _ _ _ (by unfold QfG; ring))
  have a2 : (D.tile k2).localAngle X = γ :=
    ((h2.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a3 : (D.tile k3).localAngle X = α :=
    ((h3.anglesG S.tile S.hM).1) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a4 : (D.tile k4).localAngle X = γ :=
    ((h4.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a0 : (D.tile t0).localAngle X = β :=
    ((h0.anglesG S.tile S.hM).2.1) (hmp _ hb0.le _ _ _ _ (by unfold QfG; ring))
  -- distinctness of the five known tiles
  have nv : ∀ {a b a' b' : ℝ}, (a ≠ a' ∨ b ≠ b') → mpG (e : ℝ) f 1 x a b ≠ mpG (e : ℝ) f 1 x a' b' := by
    intro a b a' b' h hh
    obtain ⟨h1, h2⟩ := mpG_inj he0 hef hh
    rcases h with h | h
    · exact h h1
    · exact h h2
  have n01 : k1 ≠ t0 := by
    obtain ⟨i, hi⟩ := hasV_third h1
    exact HasV.ne_of_vertex h0 hi (nv (Or.inl (by linarith))) (nv (Or.inl (by linarith))) (nv (Or.inl (by linarith)))
  have n24 : k2 ≠ k4 := by
    obtain ⟨i, hi⟩ := hasV_second h2
    exact HasV.ne_of_vertex h4 hi (nv (Or.inr (by linarith))) (nv (Or.inr (by linarith))) (nv (Or.inr (by linarith)))
  have hne : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle X = u → (D.tile j).localAngle X = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have hβγ' : β ≠ γ := hβγ.ne
  have hαβ' : α ≠ β := hA.hαβ
  have hαγ' : α ≠ γ := hαγ.ne
  set K : Finset (Fin N) := {t0, k1, k2, k3, k4} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = 2 * Real.pi - α := by
    rw [hKdef, sum_five _ n01.symm (hne _ _ a0 a2 hβγ') (hne _ _ a0 a3 hαβ'.symm) (hne _ _ a0 a4 hβγ')
      (hne _ _ a1 a2 hβγ') (hne _ _ a1 a3 hαβ'.symm) (hne _ _ a1 a4 hβγ') (hne _ _ a2 a3 hαγ'.symm) n24
      (hne _ _ a3 a4 hαγ'), a0, a1, a2, a3, a4]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have hXt : X ∈ D.target.carrier := h0.mem₁
  have hXint : X ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hXt K ?_
    rw [hKsum]; linarith
  have hΩ : ∑ i, (D.tile i).localAngle X = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq X
    rw [this, D.target.localAngle_interior hXint]
  have hXY : X ≠ Y := by
    intro h
    obtain ⟨h1', -⟩ := mpG_inj he0 hef h
    linarith
  have hYt : Y ∈ D.target.carrier := h0.mem₂
  have hint := openSeg_interior D.toDissection hXint hYt
  have hP' : cross (Y - X) ((X - (Y - X)) - X) = 0 := by
    simp [cross]; ring
  have hXP : X ∈ openSegment ℝ (X - (Y - X)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle X < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [a0]; exact hβπ
    · rw [a1]; exact hβπ
    · rw [a2]; exact hγπ'
    · rw [a3]; exact hαπ
    · rw [a4]; exact hγπ'
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) (by rw [hKsum]) hαπ hKlt
  have hZ : 0 < cross (Y - X) (mpG (e : ℝ) f 1 x (ξ + 1) (η - 1) - X) := by
    rw [hX, hY, cross_mpG he0 hef]
    have := kapG_pos he0 hef
    nlinarith
  have hKray : ∀ k ∈ K, k ≠ t0 → ∀ (j : Fin 3) (s : ℝ), 0 < s →
      (D.tile k).pts j ≠ AffineMap.lineMap X Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hkt
    · exact known_off_ray hXY h1 (mp_off_ray he0 hef x ξ η _ _ (Or.inl (by linarith)))
        (mp_off_ray he0 hef x ξ η _ _ (Or.inr (by linarith)))
    · exact known_off_ray hXY h2 (mp_off_ray he0 hef x ξ η _ _ (Or.inl (by linarith)))
        (mp_off_ray he0 hef x ξ η _ _ (Or.inl (by linarith)))
    · exact known_off_ray hXY h3 (mp_off_ray he0 hef x ξ η _ _ (Or.inl (by linarith)))
        (mp_off_ray he0 hef x ξ η _ _ (Or.inr (by linarith)))
    · exact known_off_ray hXY h4 (mp_off_ray he0 hef x ξ η _ _ (Or.inl (by linarith)))
        (mp_off_ray he0 hef x ξ η _ _ (Or.inl (by linarith)))
  obtain ⟨τ, hτK, P, W, hV, ⟨s, hs, hPs⟩, hW, hang, hPW, hsides⟩ :=
    filler_alpha S hXY h0 hZ hP' hXP hint hclamp hΩ K (by rw [hKsum]) hKray
  have hPX : P - X = s • (Y - X) := by
    rw [hPs, AffineMap.lineMap_apply]; simp
  have hz0 : cross (P - X) (W - X) < 0 := by
    rw [hPX, cross_smul_left']
    exact mul_neg_of_pos_of_neg hs hW
  have hP2 : P = mpG (e : ℝ) f 1 x (ξ + s) η := by
    rw [hPs, hX, hY, lineMap_mpG he0 hef]
    exact mpG_congr' (by ring) (by ring)
  have hdXP : dist X P ^ 2 = ((f : ℝ) ^ 2 * s) ^ 2 := by
    rw [hP2, hX, dist_mpG_sq he0 hef]
    unfold QfG; ring
  have hκ := kapG_pos he0 hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have keyneg : ∀ q : ℝ, q = 1 → -(kapG (e : ℝ) f * q) < 0 := fun q hq => by rw [hq]; linarith
  rcases hsides with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
  · -- c on the ray: U'(ξ,η)
    have hs1 : s = 1 := by
      have h := hdXP
      rw [hd1] at h
      have h' : (f : ℝ) ^ 2 = (f : ℝ) ^ 2 * s := by
        have := (sq_eq_sq₀ hf2.le (by positivity : (0 : ℝ) ≤ (f : ℝ) ^ 2 * s)).mp h
        exact this
      nlinarith
    subst hs1
    have hPY : P = Y := by rw [hPs, AffineMap.lineMap_apply_one]
    have hXPne : X ≠ P := by
      intro h; rw [← h, dist_self] at hd1; exact hf2.ne hd1
    have hWc : W = mpG (e : ℝ) f 1 x ξ (η + 1) := by
      refine same_third hXPne ?_ ?_ hz0 ?_
      · rw [dist_comm W X, hd2, dist_comm]
        symm
        exact hmp _ hb0.le _ _ _ _ (by unfold QfG; ring)
      · rw [dist_comm W P, hPW, dist_comm]
        symm
        rw [hPY]
        exact hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring)
      · rw [hPY, hY, hX, cross_mpG he0 hef]
        exact keyneg _ (by ring)
    left
    exact ⟨τ, by rw [← hPY, ← hWc]; exact hV⟩
  · -- b on the ray: the flipped tile
    have hnu : s = nuG (e : ℝ) f := by
      have h := hdXP
      rw [hd1] at h
      have h' : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 = (f : ℝ) ^ 2 * s :=
        (sq_eq_sq₀ hb0.le (by positivity : (0 : ℝ) ≤ (f : ℝ) ^ 2 * s)).mp h
      have h2 := nuG_spec he0 hef
      have h3 : (f : ℝ) ^ 2 * s = (f : ℝ) ^ 2 * nuG (e : ℝ) f := by linarith
      exact mul_left_cancel₀ hf2.ne' h3
    have hnupos := nuG_pos he0 hef
    subst hnu
    have hXPne : X ≠ P := by
      intro h; rw [← h, dist_self] at hd1; exact hb0.ne hd1
    have hWc : W = mpG (e : ℝ) f 1 x ξ (η + 1 / nuG (e : ℝ) f) := by
      refine same_third hXPne ?_ ?_ hz0 ?_
      · rw [dist_comm W X, hd2, dist_comm]
        symm
        exact hmp _ (by positivity) _ _ _ _ (qf_flip1 he0 hef ξ η)
      · rw [dist_comm W P, hPW, dist_comm]
        symm
        rw [hP2]
        exact hmp _ (by positivity) _ _ _ _ (qf_flip2 he0 hef ξ η)
      · rw [hP2, hX, cross_mpG he0 hef]
        have hnu0 := hnupos.ne'
        exact keyneg _ (by
          rw [show (ξ + nuG (e : ℝ) f - ξ) * (η + 1 / nuG (e : ℝ) f - η) - (η - η) * (ξ - ξ) =
            nuG (e : ℝ) f * (1 / nuG (e : ℝ) f) by ring]
          exact mul_one_div_cancel hnu0)
    right
    exact ⟨τ, by rw [← hP2, ← hWc]; exact hV⟩

end w2

#print axioms w2_fill

end Erdos634.Draft.WGapStmt
