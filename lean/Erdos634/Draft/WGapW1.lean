/-
Draft/WGapW1.lean -- written 15 November 2026 (session 3).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.3, use W1 of WEDGE_USES.md).
Not imported by any aggregate.  Module W5b: the wedge `(2α, γ)` at the lattice point `X = p(0, η) = p'(0, η)` (the point where the corner column `l` meets the strip).

Known tiles at `X` (all in HasV form with `X` first; real `η`, general origin `x`; `T_j = U'(0,j)`):
  `U(0,η)` [α, sector (0,α)], `U'(0,η) = T_η` [α, (α,2α)], `U'(0,η-1) = T_{η-1}` [γ, (γ, π+α)], `U(0,η-1)` [γ, (π+α, 2π-β)]  -- total `2π - 2β` (finding F7).
`w1_fill` : the filler beside the ray `e(γ)` (the `a`-edge of `T_{η-1}` from `X`, towards `Y = p'(1, η-1)`) is a `β`-tile; EITHER it is
  `D'(0,η-1) = (X, Y, p'(1,η))` (its `a`-edge on the ray, `c`-edge along `e(2α)`), OR its `c`-edge lies on the ray: vertices `X`, `P = p'(f/e, η - f/e)`
  (at distance `c` from `X`), `W` with `|XW| = a`, `|PW| = b`, `W` right of the ray.  The second alternative is excluded LATER by the chord partition (Lemma (Aa)); it is NOT excluded here.
Also: `lp_eq_mp` (`p(a,b) = p'(-a, b + s a)`), `mp_off_ray2` (a point of the mirror lattice off the ray in direction `(u,w)`), `sum_four`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapW2
import Erdos634.Draft.WGapFill2

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

theorem sum_four (g : Fin N → ℝ) {a b c d : Fin N} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    ∑ i ∈ ({a, b, c, d} : Finset (Fin N)), g i = g a + g b + g c + g d := by
  simp [Finset.sum_insert, h1, h2, h3, h4, h5, h6]
  ring

theorem sMir_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < sMir e f := by
  unfold sMir
  have hf := he.trans hef
  apply div_pos <;> nlinarith

/-- a corner lattice point is a mirror lattice point at real coordinates: `p(a,b) = p'(-a, b + s a)` -/
theorem lp_eq_mp {e f : ℝ} (he : 0 < e) (hef : e < f) (x a b : ℝ) :
    lpG e f 1 x a b = mpG e f 1 x (-a) (b + sMir e f * a) := by
  rw [mpG_eq he hef]
  exact lpG_congr (by ring) (by ring)

/-- mirror lattice points off the open ray from `p'(ξ,η)` towards `p'(ξ',η')` -/
theorem mp_off_ray2 {e f : ℝ} (he : 0 < e) (hef : e < f) (x ξ η ξ' η' a b : ℝ)
    (huw : 0 < (ξ' - ξ) ^ 2 + (η' - η) ^ 2)
    (h : (a - ξ) * (η' - η) ≠ (b - η) * (ξ' - ξ) ∨ (a - ξ) * (ξ' - ξ) + (b - η) * (η' - η) ≤ 0) :
    ∀ s : ℝ, 0 < s → mpG e f 1 x a b ≠
      AffineMap.lineMap (mpG e f 1 x ξ η) (mpG e f 1 x ξ' η') s := by
  intro s hs hh
  rw [lineMap_mpG he hef] at hh
  obtain ⟨h1, h2⟩ := mpG_inj he hef hh
  rcases h with h | h
  · apply h; rw [h1, h2]; ring
  · have : (a - ξ) * (ξ' - ξ) + (b - η) * (η' - η) = s * ((ξ' - ξ) ^ 2 + (η' - η) ^ 2) := by
      rw [h1, h2]; ring
    have := mul_pos hs huw
    linarith

section w1

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
/-- **W1**: the wedge `(2α, γ)` at `X = p'(0, η)`; see the module header. -/
theorem w1_fill (S : SetupG D e f α β γ L ax ay) (x η : ℝ)
    (hU0 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 1 η) (lpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 η) (mpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 (η - 1)) (mpG (e : ℝ) f 1 x 0 (η - 1)))
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 0 (η - 1)) (lpG (e : ℝ) f 1 x 1 (η - 1))) :
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 (η - 1)) (mpG (e : ℝ) f 1 x 1 η)) ∨
    (∃ τ W, HasV D τ (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x ((f : ℝ) / e) (η - (f : ℝ) / e)) W ∧
      cross (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) (W - mpG (e : ℝ) f 1 x 0 η) < 0 ∧
      (D.tile τ).localAngle (mpG (e : ℝ) f 1 x 0 η) = β ∧
      dist (mpG (e : ℝ) f 1 x 0 η) W = (e : ℝ) * f ∧
      dist (mpG (e : ℝ) f 1 x ((f : ℝ) / e) (η - (f : ℝ) / e)) W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨k0, h0⟩ := hU0
  obtain ⟨k1, h1⟩ := hT
  obtain ⟨t0, ht0⟩ := hT1
  obtain ⟨k3, h3⟩ := hU1
  set X := mpG (e : ℝ) f 1 x 0 η with hX
  set Y := mpG (e : ℝ) f 1 x 1 (η - 1) with hY
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  obtain ⟨hαπ, hβπ, hγπ', -, -, -⟩ := angles_lt_pi S
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hsM := sMir_pos he0 hef
  have hmp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (mpG (e : ℝ) f 1 x ξ1 η1) (mpG (e : ℝ) f 1 x ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_mpG he0 hef x hd hq
  have hlp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (lpG (e : ℝ) f 1 x ξ1 η1) (lpG (e : ℝ) f 1 x ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_lpG he0 hef hε hd hq
  have hl0 : ∀ ξ : ℝ, lpG (e : ℝ) f 1 x 0 ξ = mpG (e : ℝ) f 1 x 0 ξ := fun ξ => (mp_zero_eta _ _ _ _ _).symm
  have hXl : lpG (e : ℝ) f 1 x 0 η = X := hl0 η
  -- angles at X
  have a0 : (D.tile k0).localAngle X = α :=
    ((h0.anglesG S.tile S.hM).1) (hlp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a1 : (D.tile k1).localAngle X = α :=
    ((h1.anglesG S.tile S.hM).1) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have aT : (D.tile t0).localAngle X = γ :=
    ((ht0.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a3 : (D.tile k3).localAngle X = γ :=
    ((h3.anglesG S.tile S.hM).2.2) (hlp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have nv : ∀ {a b a' b' : ℝ}, (a ≠ a' ∨ b ≠ b') → mpG (e : ℝ) f 1 x a b ≠ mpG (e : ℝ) f 1 x a' b' := by
    intro a b a' b' h hh
    obtain ⟨h1, h2⟩ := mpG_inj he0 hef hh
    rcases h with h | h
    · exact h h1
    · exact h h2
  have hne : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle X = u → (D.tile j).localAngle X = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have n01 : k0 ≠ k1 := by
    obtain ⟨i, hi⟩ := hasV_second h0
    refine HasV.ne_of_vertex h1 hi ?_ ?_ ?_
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
  have n3T : k3 ≠ t0 := by
    obtain ⟨i, hi⟩ := hasV_third h3
    refine HasV.ne_of_vertex ht0 hi ?_ ?_ ?_
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
  have hαγ' : α ≠ γ := hαγ.ne
  set K : Finset (Fin N) := {k0, k1, t0, k3} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = 2 * Real.pi - 2 * β := by
    rw [hKdef, sum_four _ n01 (hne _ _ a0 aT hαγ') (hne _ _ a0 a3 hαγ') (hne _ _ a1 aT hαγ')
      (hne _ _ a1 a3 hαγ') n3T.symm, a0, a1, aT, a3]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have h2b := two_beta_lt_pi S
  have hXt : X ∈ D.target.carrier := h1.mem₁
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
  have hYt : Y ∈ D.target.carrier := ht0.mem₂
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
    rcases hk with rfl | rfl | rfl | rfl
    · rw [a0]; exact hαπ
    · rw [a1]; exact hαπ
    · rw [aT]; exact hγπ'
    · rw [a3]; exact hγπ'
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := 2 * β) (by rw [hKsum]) h2b hKlt
  have hZ : 0 < cross (Y - X) (mpG (e : ℝ) f 1 x 0 (η - 1) - X) := by
    rw [hX, hY, cross_mpG he0 hef]
    have := kapG_pos he0 hef
    nlinarith
  have huw : 0 < ((1 : ℝ) - 0) ^ 2 + ((η - 1) - η) ^ 2 := by
    have h := sq_nonneg ((η - 1) - η)
    nlinarith
  have hl0' : ∀ ξ : ℝ, mpG (e : ℝ) f 1 x 0 ξ = lpG (e : ℝ) f 1 x 0 ξ := fun ξ => mp_zero_eta _ _ _ _ _
  have hKray : ∀ k ∈ K, k ≠ t0 → ∀ (j : Fin 3) (s : ℝ), 0 < s →
      (D.tile k).pts j ≠ AffineMap.lineMap X Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · refine known_off_ray hXY h0 ?_ ?_
      · rw [lp_eq_mp he0 hef]
        exact mp_off_ray2 he0 hef x 0 η 1 (η - 1) _ _ huw (Or.inr (by nlinarith))
      · rw [hl0]
        exact mp_off_ray2 he0 hef x 0 η 1 (η - 1) _ _ huw (Or.inr (by nlinarith))
    · refine known_off_ray hXY h1 ?_ ?_
      · exact mp_off_ray2 he0 hef x 0 η 1 (η - 1) _ _ huw (Or.inl (by intro h; nlinarith))
      · exact mp_off_ray2 he0 hef x 0 η 1 (η - 1) _ _ huw (Or.inr (by nlinarith))
    · exact absurd rfl hkt
    · refine known_off_ray hXY h3 ?_ ?_
      · rw [hl0]
        exact mp_off_ray2 he0 hef x 0 η 1 (η - 1) _ _ huw (Or.inl (by intro h; nlinarith))
      · rw [lp_eq_mp he0 hef]
        exact mp_off_ray2 he0 hef x 0 η 1 (η - 1) _ _ huw (Or.inr (by nlinarith))
  have hcnt := wedge_2beta S hΩ (K := K) (by rw [hKsum])
  obtain ⟨τ, hτK, P, W, hV, ⟨s, hs, hPs⟩, hW, hang, hPW, hsides⟩ :=
    filler_beta S hXY ht0 hZ hP' hXP hint hclamp K hcnt.1 hcnt.2.2 hKray
  have hPX : P - X = s • (Y - X) := by
    rw [hPs, AffineMap.lineMap_apply]; simp
  have hz0 : cross (P - X) (W - X) < 0 := by
    rw [hPX, cross_smul_left']
    exact mul_neg_of_pos_of_neg hs hW
  have hP2 : P = mpG (e : ℝ) f 1 x s (η - s) := by
    rw [hPs, hX, hY, lineMap_mpG he0 hef]
    exact mpG_congr' (by ring) (by ring)
  have hdXP : dist X P ^ 2 = ((e : ℝ) * f * s) ^ 2 := by
    rw [hP2, hX, dist_mpG_sq he0 hef]
    unfold QfG; ring
  have hκ := kapG_pos he0 hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have keyneg : ∀ q : ℝ, q = 1 → -(kapG (e : ℝ) f * q) < 0 := fun q hq => by rw [hq]; linarith
  rcases hsides with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
  · -- a on the ray: D'(0, η-1)
    have hs1 : s = 1 := by
      have h := hdXP
      rw [hd1] at h
      have h' : (e : ℝ) * f = (e : ℝ) * f * s :=
        (sq_eq_sq₀ hef0.le (by positivity : (0 : ℝ) ≤ (e : ℝ) * f * s)).mp h
      have h3 : (e : ℝ) * f * 1 = (e : ℝ) * f * s := by linarith
      exact (mul_left_cancel₀ hef0.ne' h3).symm
    subst hs1
    have hPY : P = Y := by rw [hPs, AffineMap.lineMap_apply_one]
    have hXPne : X ≠ P := by
      intro h; rw [← h, dist_self] at hd1; exact hef0.ne hd1
    have hWc : W = mpG (e : ℝ) f 1 x 1 η := by
      refine same_third hXPne ?_ ?_ hz0 ?_
      · rw [dist_comm W X, hd2, dist_comm]
        symm
        exact hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring)
      · rw [dist_comm W P, hPW, dist_comm]
        symm
        rw [hPY]
        exact hmp _ hb0.le _ _ _ _ (by unfold QfG; ring)
      · rw [hPY, hY, hX, cross_mpG he0 hef]
        exact keyneg _ (by ring)
    left
    exact ⟨τ, by rw [← hPY, ← hWc]; exact hV⟩
  · -- c on the ray
    have hsval : s = (f : ℝ) / e := by
      have h := hdXP
      rw [hd1] at h
      have h' : (f : ℝ) ^ 2 = (e : ℝ) * f * s :=
        (sq_eq_sq₀ hf2.le (by positivity : (0 : ℝ) ≤ (e : ℝ) * f * s)).mp h
      rw [eq_div_iff he0.ne']
      have h3 : (f : ℝ) * (s * e) = f * f := by nlinarith
      exact mul_left_cancel₀ hf0.ne' h3
    have hP3 : P = mpG (e : ℝ) f 1 x ((f : ℝ) / e) (η - (f : ℝ) / e) := by
      rw [hP2, hsval]
    right
    exact ⟨τ, W, by rw [← hP3]; exact hV, hW, hang, hd2, by rw [← hP3]; exact hPW⟩

end w1

#print axioms w1_fill

end Erdos634.Draft.WGapStmt
