/-
Draft/WGapRL6.lean -- written 16 November 2026 (session 10).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, Case tau < i-m, layer m = 0: the wedge fill for Gamma_{t'}).
Not imported by any aggregate.  No sorry, no native_decide.
`rl_gamma_fill`: the filler of the wedge `(2alpha, 3alpha)` (size alpha) at `O = A_{t'} = p(a+1, eta+1)`, where the five known tiles are
`U(a, eta+1)` (beta), `D(a, eta)` (alpha), `U(a+1, eta)` (gamma)  [= the three lattice tiles below the anti-diagonal, `(r1)`],
`N = N_a(eta+1) = N^{t'-1}` (beta, `nu(t'-1,0)`) and `N2 = N_{a+1}(eta) = N^{t'}` (gamma, `nu(t',0)`).  Their angles at `O` sum to `2 pi - alpha`.
Conclusion: the filler is `gamma(t',0)` (b on the ray `O -> V = O + dcvec`, i.e. 2alpha) or the FLIPPED tile (b on the ray `O -> Y`, 3alpha); same output shape as `dich_fill_int`.
-/
import Erdos634.Draft.WGapDich2

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

section rl6

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem rl_gamma_fill (S : SetupG D e f α β γ L ax ay) (x a η : ℝ)
    {tUi tDL tUl tN tN2 : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1))
      (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f)))
    (hN2 : HasV D tN2 (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1))
      (lpG (e : ℝ) f 1 x (a + 1 - nuG (e : ℝ) f) (η + 2 + nuG (e : ℝ) f))) :
    (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f x a (η + 1)) (ptO e f x a (η + 1) + nuG (e : ℝ) f • (ptV e f x a (η + 1) - ptO e f x a (η + 1))) R ∧
        0 < cross (ptV e f x a (η + 1) - ptO e f x a (η + 1)) (R - ptO e f x a (η + 1))) ∨
    (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f x a (η + 1)) (ptO e f x a (η + 1) + nuG (e : ℝ) f • (ptY e f x a (η + 1) - ptO e f x a (η + 1))) R ∧
        cross (ptY e f x a (η + 1) - ptO e f x a (η + 1)) (R - ptO e f x a (η + 1)) < 0) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA := S.hA
  have hnu0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos hb (by positivity)
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have aDL := (D_anglesG S hε hDL).2.2
  have aUl := (U_anglesG S hε hUl).2.2
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  have aN2 := (N_anglesG S hε hN2).2
  -- geometric distinctness
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) 1 p ≤ -lvG (e : ℝ) (f : ℝ) 1 x (a + (η + 1) + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) 1) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have nUlN2 : tN2 ≠ tUl := by
    obtain ⟨k, hk⟩ := hasV_third hN2
    refine HasV.ne_of_vertex hUl hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  have n12 : tDL ≠ tUl := ne_of_angle (by rw [aDL, aUl]; exact hαγ)
  have n13 : tDL ≠ tUi := ne_of_angle (by rw [aDL, aUi]; exact hαβ)
  have n14 : tDL ≠ tN := ne_of_angle (by rw [aDL, aN]; exact hαβ)
  have n15 : tDL ≠ tN2 := ne_of_angle (by rw [aDL, aN2]; exact hαγ)
  have n23 : tUl ≠ tUi := ne_of_angle (by rw [aUl, aUi]; exact hβγ.symm)
  have n24 : tUl ≠ tN := ne_of_angle (by rw [aUl, aN]; exact hβγ.symm)
  have n25 : tUl ≠ tN2 := nUlN2.symm
  have n34 : tUi ≠ tN := nUiN
  have n35 : tUi ≠ tN2 := ne_of_angle (by rw [aUi, aN2]; exact hβγ)
  have n45 : tN ≠ tN2 := ne_of_angle (by rw [aN, aN2]; exact hβγ)
  set O := lpG (e : ℝ) f 1 x (a + 1) (η + 1) with hOdef
  set Y := lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f) with hYdef
  have hOint : O ∈ interior D.target.carrier := by
    refine interior_of_four D n12 n14 n15 n24 n25 n45 ?_
    rw [aDL, aUl, aN, aN2]
    have hr := hA.hrel
    have hg := hA.hγdef
    have h1 := hA.hα
    have h2 := hA.hβ
    linarith
  set K : Finset (Fin N) := {tDL, tUl, tUi, tN, tN2} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle O = 2 * Real.pi - α := by
    rw [hKdef, sum_five _ n12 n13 n14 n15 n23 n24 n25 n34 n35 n45, aDL, aUl, aUi, aN, aN2]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have hΩ : ∑ i, (D.tile i).localAngle O = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq O
    rw [this, D.target.localAngle_interior hOint]
  have hXY : O ≠ Y := by
    intro h
    have := lpG_eta_eq he0 hef h
    linarith
  have hYt : Y ∈ D.target.carrier := hN.mem₃
  have hint := openSeg_interior D.toDissection hOint hYt
  have hP' : cross (Y - O) ((O - (Y - O)) - O) = 0 := by
    simp [cross]; ring
  have hXP : O ∈ openSegment ℝ (O - (Y - O)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle O < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [aDL]; exact hαπ
    · rw [aUl]; exact hγπ
    · rw [aUi]; exact hβπ
    · rw [aN]; exact hβπ
    · rw [aN2]; exact hγπ
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) hKsum hαπ hKlt
  have hZ : 0 < cross (Y - O) (lpG (e : ℝ) f 1 x a (η + 1 + 1) - O) := by
    rw [hOdef, hYdef, cross_lpG]
    have := kapG_pos he0 hef
    have e1 : (a - nuG (e : ℝ) f - (a + 1)) * (η + 1 + 1 - (η + 1)) -
        (η + 1 + 2 + nuG (e : ℝ) f - (η + 1)) * (a - (a + 1)) = 1 := by ring
    rw [e1]; linarith
  have hKray : ∀ k ∈ K, k ≠ tN → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap O Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    have off : ∀ ξ η' : ℝ, (a - nuG (e : ℝ) f - (a + 1)) * (η' - (η + 1)) -
        (η + 1 + 2 + nuG (e : ℝ) f - (η + 1)) * (ξ - (a + 1)) ≠ 0 →
        ∀ s : ℝ, 0 < s → lpG (e : ℝ) f 1 x ξ η' ≠ AffineMap.lineMap O Y s :=
      fun ξ η' h => off_lat he0 hef x (a + 1) (η + 1) (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f) ξ η' h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · refine known_off_ray hXY hDL.rot.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hUl.rot.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hUi.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · exact absurd rfl hkt
    · refine known_off_ray hXY hN2.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
  obtain ⟨τ, hτK, P, W, hV, hPray, hW, hang', hPW, hsides⟩ :=
    filler_alpha S hXY hN.swap.rot hZ hP' hXP hint hclamp hΩ K hKsum hKray
  have := dich_conv S x a (η + 1) hV hPray hW hPW hsides
  rcases this with ⟨R, h1, h2⟩ | ⟨R, h1, h2⟩
  · exact Or.inl ⟨τ, R, h1, h2⟩
  · exact Or.inr ⟨τ, R, h1, h2⟩

end rl6

end Erdos634.Draft.WGapStmt
