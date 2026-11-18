/-
Draft/WGapDich2.lean -- written 15 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.1, PROOF 7.5 (a2-b)).
Not imported by any aggregate.  No sorry, no native_decide.
`dich_fill_int`: the filler `F` at an INTERIOR point `O = p(a+1, η+1)` (`y₀ = η+1 ≥ 1`) of the target, where the known tiles are the four lower tiles `D(a,η)`, `U(a+1,η)`, `D(a+1,η)`,
`U(a+1,η+1)` (`lower_half`), `U(a,η+1)`, `N = N_a(η+1)` and the mirror tile `E′` (vertices `O`, `p(a+1,η+2)`, `V_E`): the free wedge `(2α,3α)` has size `α`; the filler adjacent to
the ray `O → Y` is `F_c` or `F_b` (output of `dich_conv`).
-/
import Erdos634.Draft.WGapDich1
import Erdos634.Draft.WGapTop

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

theorem sum_seven (g : Fin N → ℝ) {a b c d e' f' h : Fin N}
    (h12 : a ≠ b) (h13 : a ≠ c) (h14 : a ≠ d) (h15 : a ≠ e') (h16 : a ≠ f') (h17 : a ≠ h)
    (h23 : b ≠ c) (h24 : b ≠ d) (h25 : b ≠ e') (h26 : b ≠ f') (h27 : b ≠ h)
    (h34 : c ≠ d) (h35 : c ≠ e') (h36 : c ≠ f') (h37 : c ≠ h)
    (h45 : d ≠ e') (h46 : d ≠ f') (h47 : d ≠ h)
    (h56 : e' ≠ f') (h57 : e' ≠ h) (h67 : f' ≠ h) :
    ∑ i ∈ ({a, b, c, d, e', f', h} : Finset (Fin N)), g i = g a + g b + g c + g d + g e' + g f' + g h := by
  simp [Finset.sum_insert, h12, h13, h14, h15, h16, h17, h23, h24, h25, h26, h27, h34, h35, h36, h37,
    h45, h46, h47, h56, h57, h67]
  ring

/-- a lattice point off the open ray `O → Y` (lattice coordinates): the cross product is nonzero -/
theorem off_lat {e f : ℝ} (he : 0 < e) (hef : e < f) (x ξ0 η0 ξ1 η1 ξ η : ℝ)
    (h : (ξ1 - ξ0) * (η - η0) - (η1 - η0) * (ξ - ξ0) ≠ 0) :
    ∀ s : ℝ, 0 < s → lpG e f 1 x ξ η ≠ AffineMap.lineMap (lpG e f 1 x ξ0 η0) (lpG e f 1 x ξ1 η1) s := by
  refine off_ray_of_cross_ne ?_
  rw [cross_lpG]
  exact mul_ne_zero (kapG_pos he hef).ne' h

section dich2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 2000000 in
theorem dich_fill_int (S : SetupG D e f α β γ L ax ay) (x a η : ℝ)
    {tDL tUl tDl tUr tUi tN tE : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1 + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1))
      (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f)))
    (hE : HasV D tE (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1 + 1))
      (lpG (e : ℝ) f 1 x a (η + 1 + sMir (e : ℝ) f))) :
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
  have hsM := sMir_gt_two he0 hef
  have hnu0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos hb (by positivity)
  have hsm := sMir_mul he0 hef
  obtain ⟨aDL, aUl, aDl, aUr, hOint, n12, n13, n14, n23, n24, n34⟩ := lower_half S hε hDL hUl hDl hUr
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  -- the angle of `E′` at `O`
  have aE : (D.tile tE).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = α := by
    refine ((hE.anglesG S.tile S.hM).1) ?_
    refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
    have e1 : a + 1 - a = 1 := by ring
    have e2 : η + 1 + 1 - (η + 1 + sMir (e : ℝ) f) = 1 - sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
  -- distinctness inside the classes `α`: `{DL, Ur, E′}`, `β`: `{Dl, Ui, N}`
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) 1 p ≤ -lvG (e : ℝ) (f : ℝ) 1 x (a + (η + 1) + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) 1) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have hyDl : ∀ i, ((D.tile tDl).pts i) 1 ≤ (η + 1) * hhG (e : ℝ) (f : ℝ) :=
    hDl.all (P := fun p => p 1 ≤ (η + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl) (lpG_y_le he0 hef le_rfl)
  have nUiDl : tUi ≠ tDl := by
    obtain ⟨k, hk⟩ := hUi.idx₃
    exact (ne_of_F (fun p : Plane => p 1) hyDl (i := k)
      (by rw [hk]; exact lpG_y_gt he0 hef (by linarith))).symm
  have nNDl : tN ≠ tDl := by
    obtain ⟨k, hk⟩ := hN.idx₂
    exact (ne_of_F (fun p : Plane => p 1) hyDl (i := k)
      (by rw [hk]; exact lpG_y_gt he0 hef (by linarith))).symm
  have nDLE : tE ≠ tDL := by
    obtain ⟨k, hk⟩ := hasV_third hE
    refine HasV.ne_of_vertex hDL hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  have nUrE : tE ≠ tUr := by
    obtain ⟨k, hk⟩ := hasV_third hE
    refine HasV.ne_of_vertex hUr hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  set K : Finset (Fin N) := {tDL, tUl, tDl, tUr, tUi, tN, tE} with hKdef
  have hang : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = u →
      (D.tile j).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = 2 * Real.pi - α := by
    rw [hKdef, sum_seven _ n12 n13 n14 (hang _ _ aDL aUi hαβ) (hang _ _ aDL aN hαβ) nDLE.symm
      n23 n24 (hang _ _ aUl aUi hβγ.symm) (hang _ _ aUl aN hβγ.symm) (hang _ _ aUl aE hαγ.symm)
      n34 nUiDl.symm nNDl.symm (hang _ _ aDl aE hαβ.symm)
      (hang _ _ aUr aUi hαβ) (hang _ _ aUr aN hαβ) nUrE.symm
      nUiN (hang _ _ aUi aE hαβ.symm) (hang _ _ aN aE hαβ.symm), aDL, aUl, aDl, aUr, aUi, aN, aE]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  set O := lpG (e : ℝ) f 1 x (a + 1) (η + 1) with hOdef
  set Y := lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f) with hYdef
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
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [aDL]; exact hαπ
    · rw [aUl]; exact hγπ
    · rw [aDl]; exact hβπ
    · rw [aUr]; exact hαπ
    · rw [aUi]; exact hβπ
    · rw [aN]; exact hβπ
    · rw [aE]; exact hαπ
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) hKsum hαπ hKlt
  have hZ : 0 < cross (Y - O) (lpG (e : ℝ) f 1 x a (η + 1 + 1) - O) := by
    rw [hOdef, hYdef, cross_lpG]
    have := kapG_pos he0 hef
    have e1 : (a - nuG (e : ℝ) f - (a + 1)) * (η + 1 + 1 - (η + 1)) -
        (η + 1 + 2 + nuG (e : ℝ) f - (η + 1)) * (a - (a + 1)) = 1 := by ring
    rw [e1]; linarith
  have hν := hnu0
  have hKray : ∀ k ∈ K, k ≠ tN → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap O Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    have off : ∀ ξ η' : ℝ, (a - nuG (e : ℝ) f - (a + 1)) * (η' - (η + 1)) -
        (η + 1 + 2 + nuG (e : ℝ) f - (η + 1)) * (ξ - (a + 1)) ≠ 0 →
        ∀ s : ℝ, 0 < s → lpG (e : ℝ) f 1 x ξ η' ≠ AffineMap.lineMap O Y s :=
      fun ξ η' h => off_lat he0 hef x (a + 1) (η + 1) (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f) ξ η' h
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine known_off_ray hXY hDL.rot.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hUl.rot.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hDl.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hUr ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hUi.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · exact absurd rfl hkt
    · refine known_off_ray hXY hE ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by
          intro h
          have h3 := (dich_ids he0 hef).2.2
          have hpos : 0 < (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := div_pos (by positivity) hb
          nlinarith)
  have hcnt := wedge_alpha S hΩ (K := K) (by rw [hKsum]) (angles_lt_pi S).1
  obtain ⟨τ, hτK, P, W, hV, hPray, hW, hang', hPW, hsides⟩ :=
    filler_alpha S hXY hN.swap.rot hZ hP' hXP hint hclamp hΩ K hKsum hKray
  have := dich_conv S x a (η + 1) hV hPray hW hPW hsides
  rcases this with ⟨R, h1, h2⟩ | ⟨R, h1, h2⟩
  · exact Or.inl ⟨τ, R, h1, h2⟩
  · exact Or.inr ⟨τ, R, h1, h2⟩

end dich2

end Erdos634.Draft.WGapStmt
