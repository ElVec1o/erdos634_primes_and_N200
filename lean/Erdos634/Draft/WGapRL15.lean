/-
Draft/WGapRL15.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 step (6) at `i = 1`).
Not imported by any aggregate.  No sorry, no native_decide.
`rl_step6`: at `A_1 = p(1,j+1)` the tiles `D(0,j)`, `U(1,j)`, `U(0,j+1)`, `N_1(j)` leave the wedge `(2 alpha, pi - beta)`.  Conclusion (three alternatives):
(1) `N_0(j+1)` is a tile (the `beta`-tile beside the ray `e(pi-beta)` lays its `a`-edge: `(C1)` for `lambda + 1`);
(2) `(r3)` for `t = i - lambda = 1` (the tile beside `L^(1)` lays `a` or `c` on it, or an `alpha`-tile lays `c`): the hypothesis `hleft` of `rl_close` with `tau = 1`, `m = 0`;
(3) the `beta`-tile beside the ray `e(pi-beta)` lays its `c`-edge there (to be excluded by `K` or `Sigma`, module WGapRL16).
-/
import Erdos634.Draft.WGapRL15a

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

section rl15

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 8000000 in
theorem rl_step6 (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ)
    {tUi tDL tUl tN2 : Fin N}
    (hDL : HasV D tDL (p1j (e : ℝ) f x j) (p0j1 (e : ℝ) f x j) (pA1 (e : ℝ) f x j))
    (hUl : HasV D tUl (p1j (e : ℝ) f x j) (p2j (e : ℝ) f x j) (pA1 (e : ℝ) f x j))
    (hUi : HasV D tUi (p0j1 (e : ℝ) f x j) (pA1 (e : ℝ) f x j) (pA0 (e : ℝ) f x j))
    (hN2 : HasV D tN2 (p2j (e : ℝ) f x j) (pA1 (e : ℝ) f x j) (pB0 (e : ℝ) f x j)) :
    (∃ tN : Fin N, HasV D tN (pA1 (e : ℝ) f x j) (pA0 (e : ℝ) f x j) (pC0 (e : ℝ) f x j)) ∨
    (∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ))
        (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ))) ∨
    (∃ (τ : Fin N) (P W : Plane), HasV D τ (pA1 (e : ℝ) f x j) P W ∧
      (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap (pA1 (e : ℝ) f x j) (pA0 (e : ℝ) f x j) s) ∧
      cross (pA0 (e : ℝ) f x j - pA1 (e : ℝ) f x j) (W - pA1 (e : ℝ) f x j) < 0 ∧
      (D.tile τ).localAngle (pA1 (e : ℝ) f x j) = β ∧ dist P W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      dist (pA1 (e : ℝ) f x j) P = (f : ℝ) ^ 2 ∧ dist (pA1 (e : ℝ) f x j) W = (e : ℝ) * f) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hν0 := nuG_pos he0 hef
  have hν := nuG_spec he0 hef
  have hκ := kapG_pos he0 hef
  have hb := b_posG he0 hef
  have hef0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hA := S.hA
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have hr := hA.hrel
  have hg := hA.hγdef
  have h1 := hA.hα
  have h2 := hA.hβ
  have aDL : (D.tile tDL).localAngle (pA1 (e : ℝ) f x j) = α := (D_anglesG S hε hDL).2.2
  have aUl : (D.tile tUl).localAngle (pA1 (e : ℝ) f x j) = γ := (U_anglesG S hε hUl).2.2
  have aUi : (D.tile tUi).localAngle (pA1 (e : ℝ) f x j) = β := (U_anglesG S hε hUi).2.1
  have aN2 : (D.tile tN2).localAngle (pA1 (e : ℝ) f x j) = γ := (N_anglesG S hε hN2).2
  have nUlN2 : tN2 ≠ tUl := by
    obtain ⟨k, hk⟩ := hasV_third hN2
    refine HasV.ne_of_vertex hUl hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  have n12 : tDL ≠ tUl := ne_of_angle (by rw [aDL, aUl]; exact hαγ)
  have n13 : tDL ≠ tUi := ne_of_angle (by rw [aDL, aUi]; exact hαβ)
  have n14 : tDL ≠ tN2 := ne_of_angle (by rw [aDL, aN2]; exact hαγ)
  have n23 : tUl ≠ tUi := ne_of_angle (by rw [aUl, aUi]; exact hβγ.symm)
  have n24 : tUl ≠ tN2 := nUlN2.symm
  have n34 : tUi ≠ tN2 := ne_of_angle (by rw [aUi, aN2]; exact hβγ)
  have hOint : pA1 (e : ℝ) f x j ∈ interior D.target.carrier := by
    refine interior_of_four D n12 n13 n14 n23 n24 n34 ?_
    rw [aDL, aUl, aUi, aN2]
    linarith
  set K : Finset (Fin N) := {tDL, tUl, tUi, tN2} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle (pA1 (e : ℝ) f x j) = 2 * Real.pi - (α + β) := by
    rw [hKdef, sum_four' _ n12 n13 n14 n23 n24 n34, aDL, aUl, aUi, aN2]
    linarith
  have hΩ : ∑ i, (D.tile i).localAngle (pA1 (e : ℝ) f x j) = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq (pA1 (e : ℝ) f x j)
    rw [this, D.target.localAngle_interior hOint]
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle (pA1 (e : ℝ) f x j) < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [aDL]; exact hαπ
    · rw [aUl]; exact hγπ
    · rw [aUi]; exact hβπ
    · rw [aN2]; exact hγπ
  have hαβπ : α + β < Real.pi := by linarith
  -- the scalar identities for the points on the ray
  have key : ∀ s d : ℝ, d = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) → s * nuG (e : ℝ) f * (f : ℝ) ^ 2 = d := by
    intro s d h
    rw [h]
    linear_combination s * hν
  -- conversion of a tile beside the ray `L^(1)` into the form of `rl_close`
  have mk : ∀ (τ : Fin N) (P W : Plane) (s lamc : ℝ), HasV D τ (pA1 (e : ℝ) f x j) P W →
      P = AffineMap.lineMap (pA1 (e : ℝ) f x j) (pB0 (e : ℝ) f x j) s →
      0 < cross (pB0 (e : ℝ) f x j - pA1 (e : ℝ) f x j) (W - pA1 (e : ℝ) f x j) →
      s * nuG (e : ℝ) f = lamc → (lamc = (e : ℝ) / f ∨ lamc = 1) →
      ∃ (F : Fin N) (R : Plane) (lamc' : ℝ), (lamc' = (e : ℝ) / f ∨ lamc' = 1) ∧
        HasV D F (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ))
          (PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc' • dcvec (e : ℝ) f x) R ∧
        0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
    intro τ P W s lamc hV hP hcr hsν hlam
    have hPA := s6_PIR_A1 he0 hef x j
    refine ⟨τ, W, lamc, hlam, ?_, ?_⟩
    · rw [hPA]
      refine hasV_congr hV rfl ?_ rfl
      rw [hP, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, s6_B0_sub he0 hef x j, smul_smul, hsν, add_comm]
    · rw [hPA]
      rw [s6_B0_sub he0 hef x j, cross_smul_left] at hcr
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonneg hν0.le (neg_nonneg.2 hneg)]
  -- the first ray: `A_1 -> B_0` (the line `L^(1)`), the tile `N_1(j)` is on its right
  have hXY1 := s6_XY_B he0 hef x j
  have hint1 := openSeg_interior D.toDissection hOint (hN2.mem₃ : pB0 (e : ℝ) f x j ∈ D.target.carrier)
  have hP'1 : cross (pB0 (e : ℝ) f x j - pA1 (e : ℝ) f x j)
      ((pA1 (e : ℝ) f x j - (pB0 (e : ℝ) f x j - pA1 (e : ℝ) f x j)) - pA1 (e : ℝ) f x j) = 0 := by
    simp [cross]; ring
  have hXP1 : pA1 (e : ℝ) f x j ∈ openSegment ℝ (pA1 (e : ℝ) f x j - (pB0 (e : ℝ) f x j - pA1 (e : ℝ) f x j)) (pB0 (e : ℝ) f x j) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hcl1 := no_straddle_left D.toDissection hXY1 hP'1 hXP1 hΩ K (θ := α + β) hKsum hαβπ hKlt
  have hKray1 : ∀ k ∈ K, k ≠ tN2 → ∀ (jj : Fin 3) (s : ℝ), 0 < s →
      (D.tile k).pts jj ≠ AffineMap.lineMap (pA1 (e : ℝ) f x j) (pB0 (e : ℝ) f x j) s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact known_off_ray hXY1 hDL.rot.rot
        (off_ray_of_cross_ne (by rw [s6_cr_B1j he0 hef x j]; exact (mul_pos hκ hν0).ne'))
        (off_ray_of_cross_ne (by rw [s6_cr_B01 he0 hef x j]; exact (mul_pos hκ (by linarith)).ne'))
    · exact known_off_ray hXY1 hUl.rot.rot
        (off_ray_of_cross_ne (by rw [s6_cr_B1j he0 hef x j]; exact (mul_pos hκ hν0).ne'))
        (off_ray_of_cross_ne (by rw [s6_cr_B2 he0 hef x j]; exact neg_ne_zero.mpr hκ.ne'))
    · exact known_off_ray hXY1 hUi.rot
        (off_ray_of_cross_ne (by rw [s6_cr_BA0 he0 hef x j]; exact hκ.ne'))
        (off_ray_of_cross_ne (by rw [s6_cr_B01 he0 hef x j]; exact (mul_pos hκ (by linarith)).ne'))
    · exact absurd rfl hkt
  obtain ⟨τ1, hτ1K, P1, W1, hV1, ⟨s1, hs1, hP1⟩, hW1, hcase⟩ :=
    filler_ab_left S hXY1 hN2.rot (by rw [s6_cr_B2 he0 hef x j]; linarith) hP'1 hXP1 hint1 hcl1 hΩ K hKsum hKray1
  have hdAP1 : dist (pA1 (e : ℝ) f x j) P1 = s1 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rw [hP1, dist_left_lineMap, Real.norm_of_nonneg hs1.le, s6_dAB he0 hef x j]
  have sν_c : ∀ d : ℝ, d = (f : ℝ) ^ 2 → d = s1 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) → s1 * nuG (e : ℝ) f = 1 := by
    intro d hd hd'
    have := key s1 d hd'
    rw [hd] at this
    exact mul_right_cancel₀ hf2.ne' (by linarith)
  have sν_a : ∀ d : ℝ, d = (e : ℝ) * f → d = s1 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) → s1 * nuG (e : ℝ) f = (e : ℝ) / f := by
    intro d hd hd'
    have h3 := key s1 d hd'
    rw [hd] at h3
    rw [eq_div_iff hf0.ne']
    have h4 : (s1 * nuG (e : ℝ) f * f - e) * f = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · exact absurd h5 hf0.ne'
  rcases hcase with ⟨hang1, hPW1, hsd1⟩ | ⟨hang1, hPW1, hsd1⟩
  · rcases hsd1 with ⟨hc, hb'⟩ | ⟨hb', hc⟩
    · -- an `alpha`-tile laying `c` on `L^(1)`: (r3)
      right; left
      exact mk τ1 P1 W1 s1 1 hV1 hP1 hW1 (sν_c _ hc hdAP1) (Or.inr rfl)
    · -- an `alpha`-tile laying `b` on `L^(1)`: it is `(A_1, B_0, C_0)`
      have hs11 : s1 = 1 := by
        rw [hb'] at hdAP1
        have : (s1 - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h hb.ne'
      have hP1B : P1 = pB0 (e : ℝ) f x j := by rw [hP1, hs11, AffineMap.lineMap_apply_one]
      have hW1C : pC0 (e : ℝ) f x j = W1 := by
        refine same_third_left hXY1 ?_ ?_ (by rw [s6_cr_BC he0 hef x j]; exact hκ) hW1
        · rw [dist_comm (pC0 (e : ℝ) f x j), s6_dAC he0 hef x j, dist_comm W1, hc]
        · rw [dist_comm (pC0 (e : ℝ) f x j), s6_dBC he0 hef x j, ← hP1B, dist_comm W1, hPW1]
      have hΓ : HasV D τ1 (pA1 (e : ℝ) f x j) (pB0 (e : ℝ) f x j) (pC0 (e : ℝ) f x j) :=
        hasV_congr hV1 rfl hP1B hW1C.symm
      -- the second ray: `A_1 -> A_0`, the tile `U(0,j+1)` is on its left
      set K' : Finset (Fin N) := insert τ1 K with hK'def
      have hK'sum : ∑ i ∈ K', (D.tile i).localAngle (pA1 (e : ℝ) f x j) = 2 * Real.pi - β := by
        rw [hK'def, Finset.sum_insert hτ1K, hKsum, hang1]; linarith
      have hcnt := wedge_beta S hΩ hK'sum hβπ
      have hXY2 := s6_XY_A0 he0 hef x j
      have hint2 := openSeg_interior D.toDissection hOint (hUi.mem₃ : pA0 (e : ℝ) f x j ∈ D.target.carrier)
      have hP'2 : cross (pA0 (e : ℝ) f x j - pA1 (e : ℝ) f x j)
          ((pA1 (e : ℝ) f x j - (pA0 (e : ℝ) f x j - pA1 (e : ℝ) f x j)) - pA1 (e : ℝ) f x j) = 0 := by
        simp [cross]; ring
      have hXP2 : pA1 (e : ℝ) f x j ∈ openSegment ℝ (pA1 (e : ℝ) f x j - (pA0 (e : ℝ) f x j - pA1 (e : ℝ) f x j)) (pA0 (e : ℝ) f x j) := by
        refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
        ext i; simp; ring
      have hK'lt : ∀ k ∈ K', (D.tile k).localAngle (pA1 (e : ℝ) f x j) < Real.pi := by
        intro k hk
        rw [hK'def, Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · rw [hang1]; exact hαπ
        · exact hKlt k hk
      have hcl2 := no_straddle D.toDissection hXY2 hP'2 hXP2 hΩ K' (θ := β) hK'sum hβπ hK'lt
      have hKray2 : ∀ k ∈ K', k ≠ tUi → ∀ (jj : Fin 3) (s : ℝ), 0 < s →
          (D.tile k).pts jj ≠ AffineMap.lineMap (pA1 (e : ℝ) f x j) (pA0 (e : ℝ) f x j) s := by
        intro k hk hkt
        rw [hK'def, Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact known_off_ray hXY2 hΓ
            (off_ray_of_cross_ne (by rw [s6_cr_A0B he0 hef x j]; exact neg_ne_zero.mpr hκ.ne'))
            (off_ray_of_cross_ne (by rw [s6_cr_A0C he0 hef x j]; exact neg_ne_zero.mpr hκ.ne'))
        · rw [hKdef] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl | rfl
          · exact known_off_ray hXY2 hDL.rot.rot
              (off_ray_of_cross_ne (by rw [s6_cr_A01j he0 hef x j]; exact hκ.ne'))
              (off_ray_of_cross_ne (by rw [s6_cr_A01 he0 hef x j]; exact hκ.ne'))
          · exact known_off_ray hXY2 hUl.rot.rot
              (off_ray_of_cross_ne (by rw [s6_cr_A01j he0 hef x j]; exact hκ.ne'))
              (s6_offneg he0 hef hXY2 (s6_neg2 he0 hef x j))
          · exact absurd rfl hkt
          · exact known_off_ray hXY2 hN2.rot
              (off_ray_of_cross_ne (by rw [s6_cr_A0B he0 hef x j]; exact neg_ne_zero.mpr hκ.ne'))
              (s6_offneg he0 hef hXY2 (s6_neg2 he0 hef x j))
      obtain ⟨τ2, -, P2, W2, hV2, ⟨s2, hs2, hP2⟩, hW2, hang2, hPW2, hsd2⟩ :=
        filler_beta S hXY2 hUi.rot (by rw [s6_cr_A01 he0 hef x j]; exact hκ) hP'2 hXP2 hint2 hcl2 K' hcnt.1 hcnt.2.2 hKray2
      have hdAP2 : dist (pA1 (e : ℝ) f x j) P2 = s2 * ((e : ℝ) * f) := by
        rw [hP2, dist_left_lineMap, Real.norm_of_nonneg hs2.le, s6_dAA he0 hef x j]
      rcases hsd2 with ⟨ha2, hc2⟩ | ⟨hc2, ha2⟩
      · -- `a` on the ray: `N_0(j+1)`
        have hs21 : s2 = 1 := by
          rw [ha2] at hdAP2
          have : (s2 - 1) * ((e : ℝ) * f) = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · exact absurd h hef0.ne'
        have hP2A : P2 = pA0 (e : ℝ) f x j := by rw [hP2, hs21, AffineMap.lineMap_apply_one]
        have hW2C : pC0 (e : ℝ) f x j = W2 := by
          refine same_third hXY2 ?_ ?_ (by rw [s6_cr_A0C he0 hef x j]; linarith) hW2
          · rw [dist_comm (pC0 (e : ℝ) f x j), s6_dAC he0 hef x j, dist_comm W2, hc2]
          · rw [dist_comm (pC0 (e : ℝ) f x j), s6_dA0C he0 hef x j, ← hP2A, dist_comm W2, hPW2]
        left
        exact ⟨τ2, hasV_congr hV2 rfl hP2A hW2C.symm⟩
      · -- `c` on the ray
        right; right
        exact ⟨τ2, P2, W2, hV2, ⟨s2, hs2, hP2⟩, hW2, hang2, hPW2, hc2, ha2⟩
  · rcases hsd1 with ⟨ha, hc⟩ | ⟨hc, ha⟩
    · right; left
      exact mk τ1 P1 W1 s1 _ hV1 hP1 hW1 (sν_a _ ha hdAP1) (Or.inl rfl)
    · right; left
      exact mk τ1 P1 W1 s1 1 hV1 hP1 hW1 (sν_c _ hc hdAP1) (Or.inr rfl)

end rl15

#print axioms rl_step6

end Erdos634.Draft.WGapStmt
