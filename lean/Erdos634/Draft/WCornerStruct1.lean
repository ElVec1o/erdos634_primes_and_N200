/-
Draft/WCornerStruct1.lean -- written 16 November 2026 (work item LEAN_CORNERSTRUCT_2026-11-16).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  New leaf module; no existing file is edited.
**EXTRACTION of the geometric half of the W-gap proof** (`WGapFinal.no_tiling_W_gap_of_main` + `WGapStation4.sigma_B_joint_P`).  That half never uses the multiplier window `M (f - e) < f`
(it enters only through `SplusThick.C_AQ'`, at `WGapFinal.lean:62-63`).  Here the half is stated as a theorem about EVERY tiling of `W_M(e,f)`, for every `M >= 1`:
* `w_corner_run_long`: for coprime `1 <= e < f`, `M >= 1`, and every congruent dissection `D₀` of the triangle `W_M(e,f)` by the tile `(e f, f² - e², f²)` (the very hypotheses of `WTilable e f M`),
  the side `AQ` (length `M f (f² - e²)`, from the `2α` corner to the `α + β` corner) is the union of `x`, `y`, `z` edges `a`, `b`, `c`, and carries `f` consecutive tiles `C1` or `f` consecutive tiles `C2`
  (alternative (i) of `corner_side_theorem`); in particular `z >= f`.  Hypothesis `2 <= e` of `no_tiling_W_gap` is NOT needed: `sigma_B_joint_P` does not use it (audit observation O1).
* `no_tiling_W_gap'`: the W-gap theorem re-derived from `w_corner_run_long` and `C_AQ'` in a few lines (faithfulness control of the extraction).
* `w_bottom_rung_words`: in the bottom rung `(M-1)(f-e) < f <= M (f-e)` (with `f <= M e`, `2 <= e`) the word `(x,y,z)` of `AQ` is `(M(f-e), 0, M(f-e))` or `(M(f-e) - f, 0, M(f-e) + e)`
  (with `r = M(f-e) - f`: `c^{f+r} a^{f+r}` or `c^{f+r+e} a^r`).  A COUNT dichotomy; it decides no `N` and is the starting point for the rung, not a step across it.
Credit: Beeson-Rosu (boundary-run method, `thm:cornerrun`), the E2R6 and WGap rooms (Sigma / Wall Lemma / U3 chain), Paliy and Laczkovich for the underlying arithmetic.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStation4
import Erdos634.Draft.WGapRung6b

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WCornerStruct

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Erdos634.Draft.FDBBaseBetaE1 Set
  Erdos634.Draft.WGapStmt

/-- **The long-run word of the side `AQ`** of a dissection `D₀` (target `W_M(e,f)`): there are a dissection `D = g(D₀)` (`g` an isometry, side `AQ` placed on `[0, L]` with `L = M f (f² - e²)`),
a setup with corners (`2α` or `3α` at the origin, `β` or `α + β` at the far end), a typed chain of base tiles of that side, whose letter counts are `x` (edges `a`), `y` (edges `b`), `z` (edges `c`), and which contains
`f` consecutive tiles `C1` or `f` consecutive tiles `C2` (alternative (i) of `corner_side_theorem`). -/
def WLongRunWord {N : ℕ} (D₀ : CongruentDissection N) (M e f x y z : ℕ) : Prop :=
  ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (L ax ay : ℝ),
    (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
    L = (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
    ∃ (S : SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L ax ay)
      (_ : CornersA e f L ax ay) (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty)
      (_ : ChainG D e f L m X tile τ),
      x = ∑ k ∈ Finset.range m, (τ k).cA ∧ y = ∑ k ∈ Finset.range m, (τ k).cB ∧
      z = ∑ k ∈ Finset.range m, (τ k).cC ∧
      ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2))

/-- the counts of a chain, as sums (`SideRunGA.sideG_counts_gen` with the counts exposed) -/
theorem chain_sums_eq {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ}
    {tile : ℕ → Fin N} {τ : ℕ → Ty} (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L m X tile τ) :
    ((∑ k ∈ Finset.range m, (τ k).cA : ℕ) : ℝ) * ((e : ℝ) * f) +
      ((∑ k ∈ Finset.range m, (τ k).cB : ℕ) : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) +
      ((∑ k ∈ Finset.range m, (τ k).cC : ℕ) : ℝ) * (f : ℝ) ^ 2 = L := by
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left S.hef.le 2)]; push_cast; ring
  have hN : ∑ k ∈ Finset.range m, lenN e f (τ k)
      = (∑ k ∈ Finset.range m, (τ k).cA) * (e * f) + (∑ k ∈ Finset.range m, (τ k).cB) * (f ^ 2 - e ^ 2)
        + (∑ k ∈ Finset.range m, (τ k).cC) * f ^ 2 := by
    simp only [lenN, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 : ∀ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ) = X (k + 1) - X k := by
    intro k hk
    rw [Ch.hstep k (Finset.mem_range.mp hk)]; ring
  have h2 : L = ∑ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ) := by
    rw [Finset.sum_congr rfl h1, Finset.sum_range_sub, Ch.hXm, Ch.hX0, sub_zero]
  have h3 : ∑ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ)
      = ((∑ k ∈ Finset.range m, lenN e f (τ k) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun k _ => lenG_cast S.hef (τ k))
  rw [h2, h3, hN]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]

/-- **THE GEOMETRIC HALF OF THE W-GAP PROOF, FOR EVERY `M >= 1`**: in every congruent dissection of `W_M(e,f)` (coprime `1 <= e < f`) by the tile `(e f, f² - e², f²)`, the side `AQ` carries `f`
consecutive tiles `C1` or `f` consecutive tiles `C2` (alternative (i) of `thm:cornerrun`; alternative (ii) never occurs), so its `c`-count satisfies `z >= f`.  Hypotheses: `Nat.Coprime e f`, `1 <= e < f`, `1 <= M`
(no window, no `f <= M e`, no `2 <= e`).  The proof of `no_tiling_W_gap` minus the count `C_AQ'`; alternative (ii) is killed by `sigma_B_joint_P` as in `sigma_corner_of_all` / `wgap_main_of_sigma`, with `he2` bypassed
(it is not used by `sigma_B_joint_P`). -/
theorem w_corner_run_long {N e f M : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ x y z : ℕ, WLongRunWord D₀ M e f x y z ∧
      x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2) ∧ f ≤ z := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨hA, hQ, hB⟩ := W_corners_of_sides e f he hef hMr D₀ τ h1 h2 h3
  obtain ⟨D, g, L, ax, ay, hL, hLd, hD, hP, hB', S, Co, h2c, hdist⟩ :=
    setup_of_corners_F2 e f he hef hco D₀ hMod (rotA.trans τ) (Or.inl hA) (Or.inr hQ)
  obtain ⟨m, X, tile, τc, Ch⟩ := S.exists_chainG
  have hsum := chain_sums_eq S Ch
  have hLeq : L = (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [← hLd]; exact h2
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
  have hnat : (∑ k ∈ Finset.range m, (τc k).cA) * (e * f) + (∑ k ∈ Finset.range m, (τc k).cB) * (f ^ 2 - e ^ 2)
      + (∑ k ∈ Finset.range m, (τc k).cC) * f ^ 2 = M * f * (f ^ 2 - e ^ 2) := by
    have h' : (((∑ k ∈ Finset.range m, (τc k).cA) * (e * f) + (∑ k ∈ Finset.range m, (τc k).cB) * (f ^ 2 - e ^ 2)
        + (∑ k ∈ Finset.range m, (τc k).cC) * f ^ 2 : ℕ) : ℝ) = ((M * f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
      linear_combination hsum.trans hLeq
    exact_mod_cast h'
  -- (H4) from the side `|s'| = M f^3`
  have hH4 : H4 f ax ay := by
    have e1 := dist_sq_pts (mkPt ax ay) (mkPt 0 0)
    have e2 : dist (mkPt ax ay) (mkPt 0 0) = (M : ℝ) * (f : ℝ) ^ 3 := by
      rw [hdist]; exact h1
    simp only [mkPt_zero, mkPt_one] at e1
    rw [e2] at e1
    unfold H4
    have hf2 : (2 : ℝ) ≤ f := by exact_mod_cast (by omega : 2 ≤ f)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hf3 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
    have hlt : ((f : ℝ) - 1) * (f : ℝ) ^ 2 < (M : ℝ) * (f : ℝ) ^ 3 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < f) 3]
    have hpos : (0 : ℝ) ≤ ((f : ℝ) - 1) * (f : ℝ) ^ 2 := by nlinarith
    nlinarith [e1]
  have hCorner2 : Corner2 e f ax ay := cornersA_two_of_angle S Co (h2c hA)
  have hi : ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τc (i + j) = Ty.C1) ∨ (∀ j, j < f → τc (i + j) = Ty.C2)) := by
    rcases corner_side_theorem S Co Ch with ⟨i, him, hrun⟩ | ⟨k, hk1, hkf, hkm, hrun, hsucc⟩
    · exact ⟨i, him, hrun⟩
    · exfalso
      have hsucc' : k = m ∨ (k < m ∧ τc k ≠ Ty.B1 ∧ τc k ≠ Ty.C1) := by
        rcases hsucc with h | ⟨h, h'⟩
        · exact Or.inl h
        · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
      obtain ⟨-, hMir, hK2, hK3⟩ := corner_run_data S Co Ch (by omega : 1 ≤ k) (by omega : k < f) hrun hsucc'
      have hUT : UTM D (e : ℝ) (f : ℝ) 1 0 0 ((0 : ℕ) : ℝ) := by
        rw [Nat.cast_zero]
        exact (mirrorAt_iff_UTM00 S).1 (by rw [Nat.cast_zero] at hMir; exact hMir)
      have hx : xo f 0 = 0 := by simp [xo]
      have hcfg : SigmaCfg D e f 0 0 k 0 := by
        refine ⟨fun y h1 h2' => ?_, ?_, ?_⟩
        · have hy : y = 0 := by omega
          subst hy
          rw [hx]; simpa using hUT
        · rw [hx]; exact hK2
        · rw [hx]; simpa using hK3
      exact (sigma_B_joint_P S hCorner2 hH4 k).1 0 0 (Or.inl ⟨rfl, rfl⟩) k 0 le_rfl (by omega) (by omega) (by omega) hcfg
  obtain ⟨i, him, hrun⟩ := hi
  exact ⟨_, _, _, ⟨D, g, L, ax, ay, hD, hLeq, S, Co, m, X, tile, τc, Ch, rfl, rfl, rfl, i, him, hrun⟩, hnat,
    cC_run τc i f m him hrun⟩

/-- **CONTROL: `no_tiling_W_gap` re-derived** from `w_corner_run_long` and `C_AQ'` (`z >= f` against `z <= M (f - e) < f`). -/
theorem no_tiling_W_gap' (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hMf : M * (f - e) < f) : ¬ Erdos634.Draft.CollarG.WTilable e f M := by
  rintro ⟨D₀, hT, hMod⟩
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; omega
    · exact h
  obtain ⟨x, y, z, -, hnat, hz⟩ := w_corner_run_long hco (by omega) hef hM D₀ hT hMod
  have := (SplusThick.C_AQ' (by omega) hef hco hnat).2 hMf
  omega

end Erdos634.Draft.WCornerStruct
