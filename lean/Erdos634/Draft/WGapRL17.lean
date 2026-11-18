/-
Draft/WGapRL17.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.3 at `lambda = 1`, `i = 1`: the `beta`-wedge `(2 alpha, gamma)` at `A_0`).
Not imported by any aggregate.  No sorry, no native_decide.
* `filler_beta_left`: LEFT filler of a wedge of size `beta`.
* `rl_A0_fill`: at `A_0 = p(0,j+2)` the strip tile `E_{j+1}`, `U(0,j+1)`, `N_0(j+1)` leave the wedge `beta` (size `beta`); the tile beside `L^(0)` has an `a`- or `c`-edge on it: the hypothesis `hleft` of `rl_one`.
-/
import Erdos634.Draft.WGapRL16

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

theorem sum_three' (g : Fin N → ℝ) {a b c : Fin N} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :
    ∑ i ∈ ({a, b, c} : Finset (Fin N)), g i = g a + g b + g c := by
  simp [Finset.sum_insert, h1, h2, h3]
  ring

section rl17a

variable {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j : ℕ)

include he hef

theorem s7_PIR_A0 : PIR e f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = pA0 e f x j := by
  rw [PIR_lp1 he hef]; exact lpG_congr (by push_cast; ring) (by push_cast; ring)

theorem s7_C0_sub : pC0 e f x j - pA0 e f x j = nuG e f • dcvec e f x := by
  have h1 : pC0 e f x j = PIR e f x j 1 0 1 := by
    rw [PIR_lp1 he hef]; exact lpG_congr (by ring) (by ring)
  have h0 : pA0 e f x j = PIR e f x j 1 0 0 := by
    rw [PIR_lp1 he hef]; exact lpG_congr (by ring) (by ring)
  rw [h1, h0, PIR_aff e f x j 1 0 1, one_smul, wvec_eq]
  abel

theorem s7_cr_CA1 : cross (pC0 e f x j - pA0 e f x j) (pA1 e f x j - pA0 e f x j) = -kapG e f := by
  unfold pC0 pA0 pA1; rw [cross_lpG]; ring

theorem s7_cr_C01 : cross (pC0 e f x j - pA0 e f x j) (p0j1 e f x j - pA0 e f x j) = kapG e f * nuG e f := by
  unfold pC0 pA0 p0j1; rw [cross_lpG]; ring

theorem s7_cr_CQ : cross (pC0 e f x j - pA0 e f x j)
    (lpG e f 1 x (-1) (((j : ℝ) + 1) + sMir e f * 1) - pA0 e f x j) = kapG e f * nuG e f := by
  have hns := nu_s he hef
  unfold pC0 pA0; rw [cross_lpG]
  linear_combination (-(kapG e f)) * hns

theorem s7_XY : pA0 e f x j ≠ pC0 e f x j := by
  intro h
  have := s6_dA0C he hef x j
  rw [h, dist_self] at this
  have hb := b_posG he hef
  linarith

end rl17a

section rl17

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem filler_beta_left (S : SetupG D e f α β γ L ax ay) {X Y Z P' : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : cross (Y - X) (Z - X) < 0)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (X - Y)) (cross (X - Y) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    {Ω : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - β)
    (hKray : ∀ k ∈ K, k ≠ t₀ → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, τ ∉ K ∧ ∃ P W : Plane, HasV D τ X P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      0 < cross (Y - X) (W - X) ∧ (D.tile τ).localAngle X = β ∧ dist P W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      ((dist X P = (e : ℝ) * f ∧ dist X W = (f : ℝ) ^ 2) ∨
        (dist X P = (f : ℝ) ^ 2 ∧ dist X W = (e : ℝ) * f)) := by
  obtain ⟨τ, k, m, t, hτ, hkm, hk, ht, hm, hle⟩ := ray_filler_left D hXY hV hZ hP' hXP hint hclamp
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hkn : k ≠ n := hnk.symm
  have hmn : m ≠ n := hnm.symm
  have hτK : τ ∉ K := fun h => hKray τ h hτ m t ht hm
  have hne := tri_cross_ne (D.tile τ) hkm hkn hmn
  have hmX : (D.tile τ).pts m - (D.tile τ).pts k = t • (Y - X) := by
    rw [hm, hk, AffineMap.lineMap_apply]; simp
  have hneg : 0 < cross (Y - X) ((D.tile τ).pts n - X) := by
    rcases lt_or_eq_of_le (hle n) with h | h
    · exact h
    · exfalso; apply hne
      rw [hmX, cross_smul_left', hk, ← h]; ring
  have hvc := vertex_angle_cases S τ hkm hkn hmn
  have hcnt := wedge_beta S hΩ hK (angles_lt_pi S).2.1
  have hmemτ : τ ∈ Finset.univ \ K := by simp [hτK]
  have hangβ : (D.tile τ).localAngle ((D.tile τ).pts k) = β := by
    rcases hvc with h | h | h
    · exfalso
      have h0 := hcnt.1
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [← hk]; exact h)
    · exact h
    · exfalso
      have h0 := hcnt.2.2
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [← hk]; exact h)
  obtain ⟨hopp, hsd⟩ := sides_of_beta S τ hkm hkn hmn hangβ
  rw [hk] at hangβ hsd
  exact ⟨τ, hτK, (D.tile τ).pts m, (D.tile τ).pts n, ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩,
    ⟨t, ht, hm⟩, hneg, hangβ, hopp, hsd⟩

set_option maxHeartbeats 8000000 in
theorem rl_A0_fill (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j : ℕ)
    {tE tUi tN0 : Fin N}
    (hE0 : HasV D tE (mpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1)) (mpG (e : ℝ) f 1 x (0 + 1) ((j : ℝ) + 1))
      (mpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1)))
    (hUi : HasV D tUi (p0j1 (e : ℝ) f x j) (pA1 (e : ℝ) f x j) (pA0 (e : ℝ) f x j))
    (hN0 : HasV D tN0 (pA1 (e : ℝ) f x j) (pA0 (e : ℝ) f x j) (pC0 (e : ℝ) f x j)) :
    ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))
        (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hν := nuG_spec he0 hef
  have hκ := kapG_pos he0 hef
  have hb := b_posG he0 hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hs2 := sMir_gt_two he0 hef
  have hA := S.hA
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have hr := hA.hrel
  have hg := hA.hγdef
  have h1 := hA.hα
  have h2 := hA.hβ
  -- the strip tile `E_{j+1}` in lattice form
  have hXm : mpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1 + 1) = pA0 (e : ℝ) f x j := mpG_eq_zero he0 hef x _
  have hP'm : mpG (e : ℝ) f 1 x (0 + 1) ((j : ℝ) + 1) = lpG (e : ℝ) f 1 x (-1) (((j : ℝ) + 1) + sMir (e : ℝ) f * 1) := by
    rw [zero_add]; exact mpG_eq he0 hef x 1 _
  have hAm : mpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1) = p0j1 (e : ℝ) f x j := mpG_eq_zero he0 hef x _
  have hE' : HasV D tE (p0j1 (e : ℝ) f x j) (lpG (e : ℝ) f 1 x (-1) (((j : ℝ) + 1) + sMir (e : ℝ) f * 1)) (pA0 (e : ℝ) f x j) :=
    hasV_congr hE0 hAm hP'm hXm
  have dEA : dist (p0j1 (e : ℝ) f x j) (lpG (e : ℝ) f 1 x (-1) (((j : ℝ) + 1) + sMir (e : ℝ) f * 1)) = (f : ℝ) ^ 2 := by
    refine dist_lpG he0 hef hε hf2.le ?_
    have e1 : (0 : ℝ) - (-1) = 1 := by ring
    have e2 : ((j : ℝ) + 1) - (((j : ℝ) + 1) + sMir (e : ℝ) f * 1) = -sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    have hsm := sMir_mul he0 hef
    linear_combination (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * sMir (e : ℝ) f) * hsm
  have aE : (D.tile tE).localAngle (pA0 (e : ℝ) f x j) = γ := ((hE'.rot.rot.anglesG S.tile S.hM).2.2) dEA
  have aU : (D.tile tUi).localAngle (pA0 (e : ℝ) f x j) = γ := (U_anglesG S hε hUi).2.2
  have aN : (D.tile tN0).localAngle (pA0 (e : ℝ) f x j) = γ := (N_anglesG S hε hN0).2
  -- distinctness
  have hU1y : ∀ i, ((D.tile tUi).pts i) 1 ≤ (((j : ℝ) + 1) + 1) * hhG (e : ℝ) (f : ℝ) :=
    hUi.all (P := fun p => p 1 ≤ (((j : ℝ) + 1) + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl)
  have P'high : (((j : ℝ) + 1) + 1) * hhG (e : ℝ) (f : ℝ) <
      (lpG (e : ℝ) f 1 x (-1) (((j : ℝ) + 1) + sMir (e : ℝ) f * 1)) 1 := lpG_y_gt he0 hef (by linarith)
  have nUE : tUi ≠ tE := by
    obtain ⟨i2, hi2⟩ := hE'.idx₂
    exact ne_of_F (fun p : Plane => p 1) hU1y (i := i2) (by rw [hi2]; exact P'high)
  have nNU : tN0 ≠ tUi := by
    obtain ⟨k, hk⟩ := hasV_third hN0
    refine HasV.ne_of_vertex hUi hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_xi_eq he0 hef hε h
      linarith
  have nNE : tN0 ≠ tE := by
    obtain ⟨k, hk⟩ := hasV_third hN0
    refine HasV.ne_of_vertex hE' hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_xi_eq he0 hef hε h
      linarith
  have hOint : pA0 (e : ℝ) f x j ∈ interior D.target.carrier :=
    interior_of_two_tiles D.toDissection hUi.mem₃ nUE aU aE
      (by have := Erdos634.Draft.WGapAngles.two_gamma_gt_pi hA; linarith)
  set K : Finset (Fin N) := {tE, tUi, tN0} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle (pA0 (e : ℝ) f x j) = 2 * Real.pi - β := by
    rw [hKdef, sum_three' _ nUE.symm nNE.symm nNU.symm, aE, aU, aN]
    linarith
  have hΩ : ∑ i, (D.tile i).localAngle (pA0 (e : ℝ) f x j) = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq (pA0 (e : ℝ) f x j)
    rw [this, D.target.localAngle_interior hOint]
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle (pA0 (e : ℝ) f x j) < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · rw [aE]; exact hγπ
    · rw [aU]; exact hγπ
    · rw [aN]; exact hγπ
  have hXY := s7_XY he0 hef x j
  have hint := openSeg_interior D.toDissection hOint (hN0.mem₃ : pC0 (e : ℝ) f x j ∈ D.target.carrier)
  have hP' : cross (pC0 (e : ℝ) f x j - pA0 (e : ℝ) f x j)
      ((pA0 (e : ℝ) f x j - (pC0 (e : ℝ) f x j - pA0 (e : ℝ) f x j)) - pA0 (e : ℝ) f x j) = 0 := by
    simp [cross]; ring
  have hXP : pA0 (e : ℝ) f x j ∈ openSegment ℝ (pA0 (e : ℝ) f x j - (pC0 (e : ℝ) f x j - pA0 (e : ℝ) f x j)) (pC0 (e : ℝ) f x j) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hcl := no_straddle_left D.toDissection hXY hP' hXP hΩ K (θ := β) hKsum hβπ hKlt
  have hKray : ∀ k ∈ K, k ≠ tN0 → ∀ (jj : Fin 3) (s : ℝ), 0 < s →
      (D.tile k).pts jj ≠ AffineMap.lineMap (pA0 (e : ℝ) f x j) (pC0 (e : ℝ) f x j) s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact known_off_ray hXY hE'.rot.rot
        (off_ray_of_cross_ne (by rw [s7_cr_C01 he0 hef x j]; exact (mul_pos hκ hν0).ne'))
        (off_ray_of_cross_ne (by rw [s7_cr_CQ he0 hef x j]; exact (mul_pos hκ hν0).ne'))
    · exact known_off_ray hXY hUi.rot.rot
        (off_ray_of_cross_ne (by rw [s7_cr_C01 he0 hef x j]; exact (mul_pos hκ hν0).ne'))
        (off_ray_of_cross_ne (by rw [s7_cr_CA1 he0 hef x j]; exact neg_ne_zero.mpr hκ.ne'))
    · exact absurd rfl hkt
  obtain ⟨τ, -, P, W, hV, ⟨s, hs, hP⟩, hW, hang, hPW, hsd⟩ :=
    filler_beta_left S hXY hN0.rot (by rw [s7_cr_CA1 he0 hef x j]; linarith) hP' hXP hint hcl hΩ K hKsum hKray
  have hdAP : dist (pA0 (e : ℝ) f x j) P = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rw [hP, dist_left_lineMap, Real.norm_of_nonneg hs.le, s6_dA0C he0 hef x j]
  have key : ∀ d : ℝ, d = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) → s * nuG (e : ℝ) f * (f : ℝ) ^ 2 = d := by
    intro d h
    rw [h]
    linear_combination s * hν
  have mk : ∀ lamc : ℝ, s * nuG (e : ℝ) f = lamc → (lamc = (e : ℝ) / f ∨ lamc = 1) →
      ∃ (F : Fin N) (R : Plane) (lamc' : ℝ), (lamc' = (e : ℝ) / f ∨ lamc' = 1) ∧
        HasV D F (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))
          (PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) + lamc' • dcvec (e : ℝ) f x) R ∧
        0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
    intro lamc hsν hlam
    have hPA := s7_PIR_A0 he0 hef x j
    refine ⟨τ, W, lamc, hlam, ?_, ?_⟩
    · rw [hPA]
      refine hasV_congr hV rfl ?_ rfl
      rw [hP, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, s7_C0_sub he0 hef x j, smul_smul, hsν, add_comm]
    · rw [hPA]
      have hcr := hW
      rw [s7_C0_sub he0 hef x j, cross_smul_left] at hcr
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonneg hν0.le (neg_nonneg.2 hneg)]
  rcases hsd with ⟨ha, hc⟩ | ⟨hc, ha⟩
  · refine mk ((e : ℝ) / f) ?_ (Or.inl rfl)
    have h3 := key _ (by rw [← hdAP, ha])
    rw [eq_div_iff hf0.ne']
    have h4 : (s * nuG (e : ℝ) f * f - e) * f = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · exact absurd h5 hf0.ne'
  · refine mk 1 ?_ (Or.inr rfl)
    have h3 := key _ (by rw [← hdAP, hc])
    exact mul_right_cancel₀ hf2.ne' (by linarith)

end rl17

#print axioms rl_A0_fill

end Erdos634.Draft.WGapStmt
