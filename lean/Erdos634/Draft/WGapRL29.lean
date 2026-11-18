/-
Draft/WGapRL29.lean -- written 16 November 2026 (session 14).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 step (2), `S_{i-lambda-1} != N`, at `i = 2`, `lambda = 1`).
Not imported by any aggregate.  No sorry, no native_decide.
* `colnext_first_false`: the tile beside the `b`-edge of `U(i+1,j0)` cannot lay an `a`- or `c`-edge on the column (first alternative of `ColNext`) when `N_i(j0)` and `N_{i+1}(j0)` are tiles:
  the six tiles at `X = p(i+1,j0+1)` leave the wedge `(alpha,3alpha)` of size `2 alpha` (two `alpha`-tiles), so the tile shows `alpha` and lays its `c`-edge on the column, which would pass through `A = p(i+1,j0+2)`, a vertex of `U(i+1,j0+1)` and of `N_{i+1}(j0)`: `pi + gamma + gamma > 2 pi`.
* `noN_mirror2`: `N_i(j0)` a tile (and `N_{i+1}(j0)` a tile) gives the mirror tile `E'` at the origin `p(i+1,0)` (the `noN_mirror` of WGapSigA without `(K2),(K3)`; the `c`-edge alternative is killed by `colnext_first_false`).
-/
import Erdos634.Draft.WGapRL28

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

theorem off_vert {e f : ℝ} (he : 0 < e) (hef : e < f) (x c η ξ' η' : ℝ) (h : ξ' ≠ c) :
    ∀ s : ℝ, 0 < s → lpG e f 1 x ξ' η' ≠ AffineMap.lineMap (lpG e f 1 x c η) (lpG e f 1 x c (η + 1)) s := by
  refine off_lat he hef x c η c (η + 1) ξ' η' ?_
  intro h0
  apply h
  have h1 : (c - c) * (η' - η) - (η + 1 - η) * (ξ' - c) = -(ξ' - c) := by ring
  rw [h1] at h0
  linarith

theorem below_neg {e f : ℝ} (x c η : ℝ) :
    lpG e f 1 x c η - lpG e f 1 x c (η + 1) = (-1 : ℝ) • (lpG e f 1 x c (η + 1 + 1) - lpG e f 1 x c (η + 1)) := by
  unfold lpG
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring

theorem col_step {e f : ℝ} (x c η t : ℝ) :
    lpG e f 1 x c (η + 1 + t) - lpG e f 1 x c (η + 1) = t • (lpG e f 1 x c (η + 1 + 1) - lpG e f 1 x c (η + 1)) := by
  unfold lpG
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring

section rl29

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem colnext_first_false (S : SetupG D e f α β γ L ax ay) (x : ℝ) {i : ℕ} {η : ℝ}
    {tDL tUl tDl tUr tUi tN tN1 : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) η) (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) η) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) η)
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) η) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) (η + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
      (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) (lpG (e : ℝ) f 1 x (i : ℝ) (η + 1 + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f)))
    (hN1 : HasV D tN1 (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 + 1) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1 - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f)))
    {iT : Fin N} {k m : Fin 3} {t : ℝ} (hkm : k ≠ m)
    (hk : (D.tile iT).pts k = lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
    (hm : (D.tile iT).pts m = lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + t)) (ht : 0 < t)
    (hlen : t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (e : ℝ) * f ∨ t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2)
    (hle : ∀ i', FXG (e : ℝ) f 1 ((D.tile iT).pts i') ≤ lvG (e : ℝ) f 1 x ((i : ℝ) + 1)) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hε1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hνs := nuG_spec he0 hef
  have hA := S.hA
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, h2απ, -, -⟩ := angles_lt_pi S
  have hr := hA.hrel
  have hg := hA.hγdef
  have h1 := hA.hα
  have h2 := hA.hβ
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := b_posG he0 hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  -- the point `X` and the ray `X -> Y`
  have aDL : (D.tile tDL).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = α := (D_anglesG S hε1 hDL).2.2
  have aUl : (D.tile tUl).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = γ := (U_anglesG S hε1 hUl).2.2
  have aDl : (D.tile tDl).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = β := (D_anglesG S hε1 hDl).2.1
  have aUr : (D.tile tUr).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = α := (U_anglesG S hε1 hUr).1
  have aUi : (D.tile tUi).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = β := (U_anglesG S hε1 hUi).2.1
  have aN : (D.tile tN).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = β := (N_anglesG S hε1 hN).1
  -- distinctness
  have n12 : tDL ≠ tUl := ne_of_angle (by rw [aDL, aUl]; exact hαγ)
  have n13 : tDL ≠ tDl := ne_of_angle (by rw [aDL, aDl]; exact hαβ)
  have n15 : tDL ≠ tUi := ne_of_angle (by rw [aDL, aUi]; exact hαβ)
  have n16 : tDL ≠ tN := ne_of_angle (by rw [aDL, aN]; exact hαβ)
  have n23 : tUl ≠ tDl := ne_of_angle (by rw [aUl, aDl]; exact hβγ.symm)
  have n24 : tUl ≠ tUr := ne_of_angle (by rw [aUl, aUr]; exact hαγ.symm)
  have n25 : tUl ≠ tUi := ne_of_angle (by rw [aUl, aUi]; exact hβγ.symm)
  have n26 : tUl ≠ tN := ne_of_angle (by rw [aUl, aN]; exact hβγ.symm)
  have n34 : tDl ≠ tUr := ne_of_angle (by rw [aDl, aUr]; exact hαβ.symm)
  have n45 : tUr ≠ tUi := ne_of_angle (by rw [aUr, aUi]; exact hαβ)
  have n46 : tUr ≠ tN := ne_of_angle (by rw [aUr, aN]; exact hαβ)
  have n14 : tDL ≠ tUr := by
    obtain ⟨i0, hi0⟩ := hasV_third hDL.rot
    refine HasV.ne_of_vertex hUr hi0 ?_ ?_ ?_ <;> intro h <;> have := lpG_eta_eq he0 hef h <;> linarith
  have n35 : tDl ≠ tUi := by
    obtain ⟨i0, hi0⟩ := hasV_third hDl.rot
    refine HasV.ne_of_vertex hUi hi0 ?_ ?_ ?_ <;> intro h <;> have := lpG_eta_eq he0 hef h <;> linarith
  have n36 : tDl ≠ tN := by
    obtain ⟨i0, hi0⟩ := hasV_third hDl.rot
    refine HasV.ne_of_vertex hN hi0 ?_ ?_ ?_ <;> intro h <;> have := lpG_eta_eq he0 hef h <;> linarith
  have n56 : tUi ≠ tN := by
    obtain ⟨i0, hi0⟩ := hasV_third hUi.rot
    refine HasV.ne_of_vertex hN hi0 ?_ ?_ ?_
    · intro h
      have := lpG_xi_eq he0 hef hε1 h
      linarith
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  have hOint : lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1) ∈ interior D.target.carrier := by
    refine interior_of_four D n12 n15 n16 n25 n26 n56 ?_
    rw [aDL, aUl, aUi, aN]
    linarith
  set K : Finset (Fin N) := {tDL, tUl, tDl, tUr, tUi, tN} with hKdef
  have hKsum : ∑ i' ∈ K, (D.tile i').localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = 2 * Real.pi - 2 * α := by
    rw [hKdef, Finset.sum_insert (by simp [n12, n13, n14, n15, n16]), Finset.sum_insert (by simp [n23, n24, n25, n26]),
      Finset.sum_insert (by simp [n34, n35, n36]), Finset.sum_insert (by simp [n45, n46]), Finset.sum_pair n56,
      aDL, aUl, aDl, aUr, aUi, aN]
    linarith
  have hΩ : ∑ i', (D.tile i').localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
    rw [this, D.target.localAngle_interior hOint]
  have hcnt := wedge_2alpha S hΩ hKsum h2απ
  -- the ray `X -> Y` (the column) and the known tiles off it
  have hXY : lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1) ≠ lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1) :=
    lpG_ne_eta he0 hef (by intro h; linarith)
  have hneg : ∀ s : ℝ, 0 < s → lpG (e : ℝ) f 1 x ((i : ℝ) + 1) η ≠
      AffineMap.lineMap (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) s :=
    s6_offneg he0 hef hXY (below_neg x _ η)
  have hov : ∀ ξ' η' : ℝ, ξ' ≠ (i : ℝ) + 1 → ∀ s : ℝ, 0 < s → lpG (e : ℝ) f 1 x ξ' η' ≠
      AffineMap.lineMap (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) s :=
    fun ξ' η' h => off_vert he0 hef x ((i : ℝ) + 1) (η + 1) ξ' η' h
  have hKray : ∀ k' ∈ K, k' ≠ tUr → ∀ (jj : Fin 3) (s : ℝ), 0 < s → (D.tile k').pts jj ≠
      AffineMap.lineMap (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) s := by
    intro k' hk' hne
    rw [hKdef] at hk'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact known_off_ray hXY hDL.rot.rot hneg (hov _ _ (by intro h; linarith))
    · exact known_off_ray hXY hUl.rot.rot hneg (hov _ _ (by intro h; linarith))
    · exact known_off_ray hXY hDl.rot (hov _ _ (by intro h; linarith)) (hov _ _ (by intro h; linarith))
    · exact absurd rfl hne
    · exact known_off_ray hXY hUi.rot (hov _ _ (by intro h; linarith)) (hov _ _ (by intro h; linarith))
    · exact known_off_ray hXY hN (hov _ _ (by intro h; linarith)) (hov _ _ (by intro h; linarith))
  -- the tile `iT` is not in `K`
  have hPray : (D.tile iT).pts m = AffineMap.lineMap (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1))
      (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) t := by
    rw [hm, lineMap_lpG]
    exact lpG_congr (by ring) (by ring)
  have hiK : iT ∉ K := by
    intro hmem
    by_cases hU : iT = tUr
    · subst hU
      obtain ⟨i2, hi2⟩ := hasV_second hUr
      have h3 := hle i2
      rw [hi2, FXG_lp hε1] at h3
      have hhh := hhG_pos he0 hef
      unfold lvG at h3
      nlinarith [hhh, pow_pos hf0 2, mul_pos (pow_pos hf0 2) hhh]
    · exact hKray iT hmem hU m t ht hPray
  -- the angle of `iT` at `X`
  obtain ⟨n3, hn3k, hn3m⟩ := fin3_third k m hkm
  have hkn : k ≠ n3 := hn3k.symm
  have hmn : m ≠ n3 := hn3m.symm
  have hvc := vertex_angle_cases S iT hkm hkn hmn
  have hmemτ : iT ∈ Finset.univ \ K := by simp [hiK]
  have hαiT : (D.tile iT).localAngle ((D.tile iT).pts k) = α := by
    rcases hvc with h | h | h
    · exact h
    · exfalso
      have h0 := hcnt.2.1
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [hk] at h; exact h)
    · exfalso
      have h0 := hcnt.2.2
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [hk] at h; exact h)
  obtain ⟨-, hsd⟩ := sides_of_alpha S iT hkm hkn hmn hαiT
  -- the length of the edge on the column
  have hdist : dist ((D.tile iT).pts k) ((D.tile iT).pts m) = t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rw [hk, hm]
    refine dist_lpG he0 hef hε1 (by positivity) ?_
    rw [QfG_nu he0 hef]
    have hbn : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 = (f : ℝ) ^ 2 * nuG (e : ℝ) f := by linarith
    rw [hbn]
    ring
  have hab : (e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro h
    have hei : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he0
    have hefi : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
    exact S.tile.hab h
  have hac : (e : ℝ) * f ≠ (f : ℝ) ^ 2 := by
    intro h
    nlinarith [he0, hef, hf0]
  have hcb : (f : ℝ) ^ 2 ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro h
    nlinarith [pow_pos he0 2]
  have htc : t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 := by
    rcases hsd with ⟨h3, -⟩ | ⟨h3, -⟩
    · rw [hdist] at h3
      exact h3
    · rw [hdist] at h3
      rcases hlen with h4 | h4
      · exact absurd (h4.symm.trans h3) hab
      · exact absurd (h4.symm.trans h3) hcb
  have ht1 : 1 < t := by
    by_contra hnot
    push_neg at hnot
    nlinarith [pow_pos he0 2]
  -- `A = Y` lies strictly inside the `c`-edge `[X, P]`
  have hYeq : lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1) =
      lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1) + (1 / t) •
        (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + t) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1)) := by
    rw [col_step, smul_smul, one_div, inv_mul_cancel₀ ht.ne', one_smul]
    abel
  have hangY : (D.tile iT).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) = Real.pi := by
    rw [hYeq, ← hk, ← hm]
    exact Erdos634.Draft.E60Second.localAngle_pi_on_edge (D.tile iT) hkm (by positivity)
      (by rw [div_lt_one ht]; exact ht1)
  have aUrY : (D.tile tUr).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) = γ := (U_anglesG S hε1 hUr).2.2
  have aN1Y : (D.tile tN1).localAngle (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) = γ := (N_anglesG S hε1 hN1).2
  have m1 : iT ≠ tUr := ne_of_angle (by rw [hangY, aUrY]; exact hγπ.ne')
  have m2 : iT ≠ tN1 := ne_of_angle (by rw [hangY, aN1Y]; exact hγπ.ne')
  have m3 : tN1 ≠ tUr := by
    obtain ⟨i0, hi0⟩ := hasV_third hN1
    refine HasV.ne_of_vertex hUr hi0 ?_ ?_ ?_ <;> intro h <;> have := lpG_eta_eq he0 hef h <;> linarith
  have hsum := three_angles_le D.toDissection (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1)) m1 m2 m3.symm
  rw [hangY, aUrY, aN1Y] at hsum
  have hle2 := localAngle_le_two_pi D.target (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η + 1 + 1))
  linarith

end rl29

#print axioms colnext_first_false

end Erdos634.Draft.WGapStmt
