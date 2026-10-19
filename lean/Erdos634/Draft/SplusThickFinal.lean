/-
Credit: D. Paliy (2026-10-03 to 10-08, W/beta caps, exact boundary-adjacency and thick-member observations; public repository github.com/DenisUkranian/erdos-634-tilings), M. Beeson and G. Rosu.
Draft/SplusThickFinal.lean -- written 19 October 2026.  UNAUDITED.  Not in `All`; in `AllSplusThick`.

**`wTilable_not_of_small_M`**: for coprime `2 ≤ e < f`, `M < f`, `f ≤ M e`, `M (f − e) ≤ e + 1`, the triangle `W_M(e, f)` has no tiling (`¬ WTilable e f M`).
Chain (hand: `project working notes`, audit `project working notes`): the side `AQ` has length `M f b`, corners `2α → α + β` (`W_corners_of_sides`);
`cornerrun_counts_thick` gives a representation with `z ≥ e + 1` (`z ≥ e + 2` if `e + 2 ≤ f`), which uses `thm_corner_run_ep1_thick`; `SplusThickArith.C_AQ'` (`M (f − e) < f`) gives `z ≤ M (f − e) ≤ e + 1`.
Credit: Beeson-Rosu (framework), E2R6 room, Chisel, the S+ audit.  No sorry, no native_decide.
-/
import Erdos634.Draft.SplusThickMain
import Erdos634.Draft.SideRunGThickCount

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SplusThick

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunGA
  Set

variable {N : ℕ}

section counts

/-- the counting step of `cor:thickw`, with the addendum for every member -/
theorem cornerrun_counts_thick (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 =
        dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      e + 1 ≤ z ∧
      (e + 2 ≤ f →
        cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
          2 * modelAlpha (e : ℝ) (f : ℝ) → e + 2 ≤ z) := by
  obtain ⟨D, g, L, ax, ay, hL, hLd, hD, hP, hB, S, Co, h2⟩ :=
    setup_of_corners e f he hef hco D₀ hMod τ hA hQ
  obtain ⟨m, X, tile, τc, Ch⟩ := S.exists_chainG
  obtain ⟨x, y, z, hsum, hz⟩ := sideG_counts_gen S Ch
  refine ⟨x, y, z, by rw [hLd]; exact hsum, ?_⟩
  rcases corner_side_theorem S Co Ch with ⟨i, him, hrun⟩ | ⟨k, hk1, hkf, hkm, hrun, hsucc⟩
  · -- alternative (i): `f` consecutive tiles `C1` or `C2`
    have hfz := hz i f him hrun
    exact ⟨by omega, fun h _ => by omega⟩
  · -- alternative (ii): the run `C1^k`
    have hsucc' : k = m ∨ (k < m ∧ τc k ≠ Ty.B1 ∧ τc k ≠ Ty.C1) := by
      rcases hsucc with h | ⟨h, h'⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
    have hek : e + 1 ≤ k := by
      by_contra hlt
      exact corner_run_short S Co Ch hk1 (by omega) hrun hsucc'
    have hkz : k ≤ z := hz 0 k (by omega) (Or.inl (fun j hj => by rw [Nat.zero_add]; exact hrun j hj))
    refine ⟨by omega, fun hef2 h2' => ?_⟩
    have hk2 : e + 2 ≤ k := by
      by_contra hlt
      exact corner_run_short_o_any S Co (by omega) (h2 h2') Ch hk1 (by omega) hrun hsucc'
    omega


theorem thickw_count_tiling_thick (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ x y z : ℕ, x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2) ∧ e + 1 ≤ z ∧
      (e + 2 ≤ f → e + 2 ≤ z) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨hA, hQ, hB⟩ := W_corners_of_sides e f he hef hMr D₀ τ h1 h2 h3
  obtain ⟨x, y, z, hsum, hz1, hz2⟩ := cornerrun_counts_thick e f he hef hco D₀ hMod (rotA.trans τ)
    (Or.inl hA) (Or.inr hQ)
  have hd : dist (D₀.target.pts ((rotA.trans τ) 0)) (D₀.target.pts ((rotA.trans τ) 1)) =
      (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := h2
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
  refine ⟨x, y, z, ?_, hz1, fun h => hz2 h hA⟩
  have h' : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℝ) =
      ((M * f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
    linear_combination hsum.trans hd
  exact_mod_cast h'



end counts

/-- **`wTilable_not_of_small_M`** (S+ for the thick members; audit fixes G1 `M < f`, G2 `M (f − e) < f`) -/
theorem wTilable_not_of_small_M {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hMf : M < f) (hfM : f ≤ M * e) (hMfe : M * (f - e) ≤ e + 1) :
    ¬ Erdos634.Draft.CollarG.WTilable e f M := by
  rintro ⟨D, hT, hMod⟩
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; omega
    · exact h
  obtain ⟨x, y, z, hN, hz1, hz2⟩ := thickw_count_tiling_thick e f M (by omega) hef hco hM D hT hMod
  exact no_rep_z_ge (by omega) hef hco hMf hMfe hN hz1 hz2

/-! ## Instances: the hypotheses are satisfiable, and the theorem applies -/

theorem not_W_5_8_2 : ¬ Erdos634.Draft.CollarG.WTilable 5 8 2 :=
  wTilable_not_of_small_M (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem not_W_5_7_3 : ¬ Erdos634.Draft.CollarG.WTilable 5 7 3 :=
  wTilable_not_of_small_M (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem not_W_7_11_2 : ¬ Erdos634.Draft.CollarG.WTilable 7 11 2 :=
  wTilable_not_of_small_M (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem not_W_8_11_3 : ¬ Erdos634.Draft.CollarG.WTilable 8 11 3 :=
  wTilable_not_of_small_M (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
/-- the control: the existing `W_2(3,5)` theorem, here from the new statement -/
theorem not_W_3_5_2 : ¬ Erdos634.Draft.CollarG.WTilable 3 5 2 :=
  wTilable_not_of_small_M (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Erdos634.Draft.SplusThick

#print axioms Erdos634.Draft.SplusThick.cornerrun_counts_thick
#print axioms Erdos634.Draft.SplusThick.thickw_count_tiling_thick
#print axioms Erdos634.Draft.SplusThick.wTilable_not_of_small_M
#print axioms Erdos634.Draft.SplusThick.not_W_5_8_2
#print axioms Erdos634.Draft.SplusThick.not_W_5_7_3
#print axioms Erdos634.Draft.SplusThick.not_W_7_11_2
#print axioms Erdos634.Draft.SplusThick.not_W_8_11_3
#print axioms Erdos634.Draft.SplusThick.not_W_3_5_2
