/-
Draft/WGapStation1.lean -- written 16 November 2026 (session 17).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 (3b): the tile `E_k` at the station candidate `O = p(a+1, η+1)`).
Not imported by any aggregate.  No sorry, no native_decide.
`station_E_lat`: at `O = p(a+1,η+1)` of the lattice with origin `x₀`, from the six lattice tiles `D(a,η), U(a+1,η), D(a+1,η), U(a+1,η+1), U(a,η+1)` and `N_a(η+1)`
(the six tiles of the `(2α)`-wedge of `dich_fill_int`), the tile `E` beside the `b`-edge of `U(a+1,η+1)` (on the left of the column `a+1`) either lays `c` on the column
(the data of `K1J` at the origin `p(a+1,0)`, in the old coordinates) or lays `b` (`MirrorAt` at the shifted origin: `E` is the mirror image of `U(a+1,η+1)`).
The angle `γ` at `O` is excluded by the wedge count (`wedge_2alpha`: the six known tiles leave exactly two `α`-tiles).
Credit: the method (`col_next`, `clamp_tile`, `mirror_of_b_n`) is the project's lattice machinery after Beeson-Rosu / Laczkovich; the wedge count is the project's `WGapWedge2`.
-/
import Erdos634.Draft.WGapClimb11

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

theorem sum_six (g : Fin N → ℝ) {a b c d e' f' : Fin N}
    (h12 : a ≠ b) (h13 : a ≠ c) (h14 : a ≠ d) (h15 : a ≠ e') (h16 : a ≠ f')
    (h23 : b ≠ c) (h24 : b ≠ d) (h25 : b ≠ e') (h26 : b ≠ f')
    (h34 : c ≠ d) (h35 : c ≠ e') (h36 : c ≠ f')
    (h45 : d ≠ e') (h46 : d ≠ f') (h56 : e' ≠ f') :
    ∑ i ∈ ({a, b, c, d, e', f'} : Finset (Fin N)), g i = g a + g b + g c + g d + g e' + g f' := by
  simp [Finset.sum_insert, h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56]
  ring

section station1

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 8000000 in
theorem station_E_lat (S : SetupG D e f α β γ L ax ay) (x₀ a η : ℝ) (n : ℕ) (hn : (n : ℝ) = a + 1)
    {tDL tUl tDl tUr tUi tN : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x₀ (a + 1) η) (lpG (e : ℝ) f 1 x₀ a (η + 1)) (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x₀ (a + 1) η) (lpG (e : ℝ) f 1 x₀ (a + 1 + 1) η) (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) f 1 x₀ (a + 1 + 1) η) (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x₀ (a + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x₀ (a + 1 + 1) (η + 1)) (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x₀ a (η + 1)) (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x₀ a (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x₀ a (η + 1 + 1))
      (lpG (e : ℝ) f 1 x₀ (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f))) :
    (∃ (iT : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile iT).pts k = lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1) ∧
      (D.tile iT).pts m = lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1 + t) ∧ 0 < t ∧
      (t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (e : ℝ) * f ∨ t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2) ∧
      ∀ i, FXG (e : ℝ) f 1 ((D.tile iT).pts i) ≤ lvG (e : ℝ) f 1 x₀ (a + 1)) ∨
    MirrorAt D (e : ℝ) f 1 (shiftX (f : ℝ) 1 x₀ n) (η + 1) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA := S.hA
  have hnu0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos hb (by positivity)
  obtain ⟨aDL, aUl, aDl, aUr, hOint, n12, n13, n14, n23, n24, n34⟩ := lower_half S hε hDL hUl hDl hUr
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, h2απ, -, -⟩ := angles_lt_pi S
  -- distinctness of the six known tiles
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) 1 p ≤ -lvG (e : ℝ) (f : ℝ) 1 x₀ (a + (η + 1) + 1))
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
  have hang : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)) = u →
      (D.tile j).localAngle (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1)) = v → u ≠ v → i ≠ j :=
    fun u v h1 h2 h3 => ne_of_angle (by rw [h1, h2]; exact h3)
  set O := lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1) with hOdef
  set K : Finset (Fin N) := {tDL, tUl, tDl, tUr, tUi, tN} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle O = 2 * Real.pi - 2 * α := by
    rw [hKdef, sum_six _ n12 n13 n14 (hang _ _ aDL aUi hαβ) (hang _ _ aDL aN hαβ)
      n23 n24 (hang _ _ aUl aUi hβγ.symm) (hang _ _ aUl aN hβγ.symm)
      n34 nUiDl.symm nNDl.symm
      (hang _ _ aUr aUi hαβ) (hang _ _ aUr aN hαβ)
      nUiN, aDL, aUl, aDl, aUr, aUi, aN]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have hΩ : ∑ i, (D.tile i).localAngle O = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq O
    rw [this, D.target.localAngle_interior hOint]
  have hcnt := wedge_2alpha S hΩ (K := K) hKsum h2απ
  -- the open segment `[O, V']` with `V' = p(a+1, η+2)`
  have hV'mem : lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1 + 1) ∈ D.target.carrier := hUr.mem₃
  have hint := openSeg_interior D.toDissection hOint hV'mem
  -- the clamp from below: the `b`-edge `[p(a+1,η), O]` of `D(a,η)`
  have hcl : ∃ P' : Plane, FXG (e : ℝ) f 1 P' = lvG (e : ℝ) f 1 x₀ (a + 1) ∧
      lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1 + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) f 1) (lvG (e : ℝ) f 1 x₀ (a + 1)),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1))
          (lpG (e : ℝ) f 1 x₀ (a + 1) (η + 1 + 1)) := by
    have hDLle : ∀ i, FXG (e : ℝ) f 1 ((D.tile tDL).pts i) ≤ lvG (e : ℝ) f 1 x₀ (a + 1) := by
      refine hDL.all (P := fun p => FXG (e : ℝ) f 1 p ≤ lvG (e : ℝ) f 1 x₀ (a + 1))
        (le_of_eq (FXG_lp hε _ _)) ?_ (le_of_eq (FXG_lp hε _ _))
      dsimp only
      rw [FXG_lp hε]
      exact lvG_le he0 hef (by linarith)
    obtain ⟨k0, m0, j0, hkm0, hkj0, hmj0, hk0, hm0, hj0⟩ := hDL
    exact clamp_tile S hε (c := a + 1) (η := η) (x := x₀) hkj0 hk0 hj0 hDLle
  have hcn := col_next S hε hUr hint hcl
  rcases hcn with ⟨iT, k, m, t, hkm, hk, hm, ht, hlen, hle⟩ | ⟨iT, k, m, hkm, hk, hm, hle⟩
  · exact Or.inl ⟨iT, k, m, t, hkm, hk, hm, ht, hlen, hle⟩
  · right
    -- the angle of `iT` at `O` is not `γ`: `iT` is not one of the six known tiles
    have niDL : iT ≠ tDL := by
      refine HasV.ne_of_vertex hDL hm ?_ ?_ ?_ <;>
      · intro h; have := lpG_eta_eq he0 hef h; linarith
    have niUl : iT ≠ tUl := by
      refine HasV.ne_of_vertex hUl hm ?_ ?_ ?_ <;>
      · intro h; have := lpG_eta_eq he0 hef h; linarith
    have niDl : iT ≠ tDl := by
      refine HasV.ne_of_vertex hDl hm ?_ ?_ ?_ <;>
      · intro h; have := lpG_eta_eq he0 hef h; linarith
    have niUi : iT ≠ tUi := by
      refine HasV.ne_of_vertex hUi hm ?_ ?_ ?_
      · intro h; have := lpG_eta_eq he0 hef h; linarith
      · intro h; have := lpG_eta_eq he0 hef h; linarith
      · exact lpG_ne_xi he0 hef hε (by intro h; linarith)
    have niN : iT ≠ tN := by
      refine HasV.ne_of_vertex hN hm ?_ ?_ ?_
      · intro h; have := lpG_eta_eq he0 hef h; linarith
      · exact lpG_ne_xi he0 hef hε (by intro h; linarith)
      · intro h; have := lpG_eta_eq he0 hef h; linarith
    have niUr : iT ≠ tUr := by
      obtain ⟨i2, hi2⟩ := hUr.idx₂
      exact ne_of_F (D := D) (FXG (e : ℝ) f 1) hle (i := i2)
        (by rw [hi2, FXG_lp hε]; exact lvG_lt he0 hef (by linarith))
    have hnK : iT ∉ K := by
      simp [hKdef, niDL, niUl, niDl, niUr, niUi, niN]
    have hnγ : (D.tile iT).localAngle (lpG (e : ℝ) f 1 x₀ (n : ℝ) (η + 1)) ≠ γ := by
      intro hγ
      have h0 := hcnt.2.2
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      refine h0 (x := iT) (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hnK⟩) ?_
      rw [hn] at hγ
      exact hγ
    exact mirror_of_b_n S hε (n := n) (η := η + 1) hkm (by rw [hn]; exact hk) (by rw [hn]; exact hm)
      (by rw [hn]; exact hle) hnγ

end station1

end Erdos634.Draft.WGapStmt
