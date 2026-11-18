/-
Draft/WGapDich3.lean -- written 15 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.1, PROOF 7.5 (a2-b)).
Not imported by any aggregate.  No sorry, no native_decide.
`dich_fill_bdry`: the filler `F` at a BOUNDARY point `O = p(a+1, η0)` (`y₀ = 0`: `O` on the side, not a vertex of the target; total angle `π`): the known tiles are
`U(a+1,η0)`, `U(a,η0)`, `N` and `E′` (total `π − α`); output as `dich_fill_int`.
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

theorem sum_four' (g : Fin N → ℝ) {a b c d : Fin N} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    ∑ i ∈ ({a, b, c, d} : Finset (Fin N)), g i = g a + g b + g c + g d := by
  simp [Finset.sum_insert, h1, h2, h3, h4, h5, h6]
  ring

section dich3

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 2000000 in
theorem dich_fill_bdry (S : SetupG D e f α β γ L ax ay) (x a η0 : ℝ)
    {tUa tUi tN tE : Fin N}
    (hUa : HasV D tUa (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x (a + 1 + 1) η0) (lpG (e : ℝ) f 1 x (a + 1) (η0 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x a η0) (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x a (η0 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x a (η0 + 1))
      (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η0 + 2 + nuG (e : ℝ) f)))
    (hE : HasV D tE (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x (a + 1) (η0 + 1))
      (lpG (e : ℝ) f 1 x a (η0 + sMir (e : ℝ) f)))
    (hη0 : 0 ≤ η0)
    (hfr : lpG (e : ℝ) f 1 x (a + 1) η0 ∈ frontier D.target.carrier ∧
      lpG (e : ℝ) f 1 x (a + 1) η0 ∉ Set.range D.target.pts) :
    (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f x a η0) (ptO e f x a η0 + nuG (e : ℝ) f • (ptV e f x a η0 - ptO e f x a η0)) R ∧
        0 < cross (ptV e f x a η0 - ptO e f x a η0) (R - ptO e f x a η0)) ∨
    (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f x a η0) (ptO e f x a η0 + nuG (e : ℝ) f • (ptY e f x a η0 - ptO e f x a η0)) R ∧
        cross (ptY e f x a η0 - ptO e f x a η0) (R - ptO e f x a η0) < 0) := by
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
  have aUa := (U_anglesG S hε hUa).1
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have aE : (D.tile tE).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = α := by
    refine ((hE.anglesG S.tile S.hM).1) ?_
    refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
    have e1 : a + 1 - a = 1 := by ring
    have e2 : η0 + 1 - (η0 + sMir (e : ℝ) f) = 1 - sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) 1 p ≤ -lvG (e : ℝ) (f : ℝ) 1 x (a + η0 + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) 1) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have nUaE : tE ≠ tUa := by
    obtain ⟨k, hk⟩ := hasV_third hE
    refine HasV.ne_of_vertex hUa hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  set K : Finset (Fin N) := {tUa, tE, tN, tUi} with hKdef
  have hang : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = u →
      (D.tile j).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = Real.pi - α := by
    rw [hKdef, sum_four' _ nUaE.symm (hang _ _ aUa aN hαβ) (hang _ _ aUa aUi hαβ)
      (hang _ _ aE aN hαβ) (hang _ _ aE aUi hαβ) nUiN.symm, aUa, aE, aN, aUi]
    have hr := hA.hrel
    linarith
  set O := lpG (e : ℝ) f 1 x (a + 1) η0 with hOdef
  set Y := lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η0 + 2 + nuG (e : ℝ) f) with hYdef
  have hΩ : ∑ i, (D.tile i).localAngle O = Real.pi := (D.toDissection.hasAngleSums).2.1 O hfr.1 hfr.2
  have hXY : O ≠ Y := by
    intro h
    have := lpG_eta_eq he0 hef h
    linarith
  have hYt : Y ∈ D.target.carrier := hN.mem₃
  have hint : openSegment ℝ O Y ⊆ interior D.target.carrier := by
    have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
    refine C.seg_intG (ξ := a + 1) (η := η0) (ξ' := a - nuG (e : ℝ) f) (η' := η0 + 2 + nuG (e : ℝ) f) hUa.mem₁ hYt ?_ ?_ ?_
    · exact Or.inr (by linarith)
    · exact Or.inl ⟨1, one_pos, hUa.mem₂⟩
    · refine Or.inl ⟨1, one_pos, ?_⟩
      have := hUi.mem₁
      rwa [show a + 1 - 1 = a by ring]
  have hP' : cross (Y - O) ((O - (Y - O)) - O) = 0 := by
    simp [cross]; ring
  have hXP : O ∈ openSegment ℝ (O - (Y - O)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle O < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [aUa]; exact hαπ
    · rw [aE]; exact hαπ
    · rw [aN]; exact hβπ
    · rw [aUi]; exact hβπ
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) hKsum hαπ hKlt
  have hZ : 0 < cross (Y - O) (lpG (e : ℝ) f 1 x a (η0 + 1) - O) := by
    rw [hOdef, hYdef, cross_lpG]
    have := kapG_pos he0 hef
    have e1 : (a - nuG (e : ℝ) f - (a + 1)) * (η0 + 1 - η0) -
        (η0 + 2 + nuG (e : ℝ) f - η0) * (a - (a + 1)) = 1 := by ring
    rw [e1]; linarith
  have hν := hnu0
  have hKray : ∀ k ∈ K, k ≠ tN → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap O Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    have off : ∀ ξ η' : ℝ, (a - nuG (e : ℝ) f - (a + 1)) * (η' - η0) -
        (η0 + 2 + nuG (e : ℝ) f - η0) * (ξ - (a + 1)) ≠ 0 →
        ∀ s : ℝ, 0 < s → lpG (e : ℝ) f 1 x ξ η' ≠ AffineMap.lineMap O Y s :=
      fun ξ η' h => off_lat he0 hef x (a + 1) η0 (a - nuG (e : ℝ) f) (η0 + 2 + nuG (e : ℝ) f) ξ η' h
    rcases hk with rfl | rfl | rfl | rfl
    · refine known_off_ray hXY hUa ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
    · refine known_off_ray hXY hE ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by
          intro h
          have h3 := (dich_ids he0 hef).2.2
          have hpos : 0 < (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := div_pos (by positivity) hb
          nlinarith)
    · exact absurd rfl hkt
    · refine known_off_ray hXY hUi.rot ?_ ?_
      · exact off _ _ (by intro h; nlinarith)
      · exact off _ _ (by intro h; nlinarith)
  obtain ⟨τ, hτK, P, W, hV, hPray, hW, hang', hPW, hsides⟩ :=
    filler_alpha S hXY hN.swap.rot hZ hP' hXP hint hclamp hΩ K (by rw [hKsum]) hKray
  have := dich_conv S x a η0 hV hPray hW hPW hsides
  rcases this with ⟨R, h1, h2⟩ | ⟨R, h1, h2⟩
  · exact Or.inl ⟨τ, R, h1, h2⟩
  · exact Or.inr ⟨τ, R, h1, h2⟩

end dich3

#print axioms dich_fill_bdry

end Erdos634.Draft.WGapStmt
