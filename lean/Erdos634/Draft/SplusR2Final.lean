/-
Draft/SplusR2Final.lean -- written 20 October 2026.  UNAUDITED.  Not in `All`; in `AllSplusR2`.

**Corollary of Theorem R2, CONDITIONAL on the geometric statement `R2Count e f`.**
`R2Count e f` is the count form of `M(e+2, 0)` (hand proof `project working notes`, audit SOUND-WITH-FIX): at a `2α`
corner with the other end `β` or `α+β`, the side carries a representation of its length with `z ≥ e + 3` (when `e + 3 ≤ f`).
CONDITIONAL corollary: it is NOT proved in Lean (blocker list in `project working notes`); this file proves only the implication
`R2Count e f → ¬ WTilable e f M` for the audited range (G1 statement), with the arithmetic of `SplusR2Arith` (G2 closed).
The hypothesis is a statement about all dissections, so it is not vacuous in itself; it is the open target.

Credit: Beeson-Rosu, Paliy, E2R6, SPLUS/SPLUS2, the AI assistant (Lemmas Z, R, Z'), the two audits.  No sorry, no native_decide.
-/
import Erdos634.Draft.SplusThickFinal
import Erdos634.Draft.SplusR2Arith

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SplusR2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunGA
  Erdos634.Draft.SplusThick Set

/-- **`R2Count e f`** (the open geometric target = count form of `M(e+2, 0)`): at a `2α` corner `A'` of a congruent dissection
whose model is the tile `(e f, f²-e², f²)`, with `β` or `α+β` at the other end of the side, the side length is a sum
`x a + y b + z c` with `z ≥ e + 3`. -/
def R2Count (e f : ℕ) : Prop :=
  ∀ {N : ℕ} (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3)),
    cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) →
    (cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) →
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 =
        dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧ e + 3 ≤ z

/-- the counting step of the corollary: the `thickw_count_tiling_thick` of S+ with the `z ≥ e+3` addendum from `R2Count` -/
theorem count_tiling_r2 {N : ℕ} (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hR2 : e + 3 ≤ f → R2Count e f)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ x y z : ℕ, x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2) ∧ e + 1 ≤ z ∧
      (e + 2 ≤ f → e + 2 ≤ z) ∧ (e + 3 ≤ f → e + 3 ≤ z) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨hA, hQ, hB⟩ := W_corners_of_sides e f he hef hMr D₀ τ h1 h2 h3
  obtain ⟨x, y, z, hsum, hz1, hz2⟩ := cornerrun_counts_thick e f he hef hco D₀ hMod (rotA.trans τ)
    (Or.inl hA) (Or.inr hQ)
  have hd : dist (D₀.target.pts ((rotA.trans τ) 0)) (D₀.target.pts ((rotA.trans τ) 1)) =
      (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := h2
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
  have hcast : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2) := by
    have h' : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℝ) =
        ((M * f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
      linear_combination hsum.trans hd
    exact_mod_cast h'
  by_cases h3f : e + 3 ≤ f
  · -- the new content: R2Count gives a representation with z ≥ e + 3 (its own x y z; the arithmetic below uses it)
    obtain ⟨x', y', z', hs', hz'⟩ := hR2 h3f D₀ hMod (rotA.trans τ) hA (Or.inr hQ)
    have h'' : ((x' * (e * f) + y' * (f ^ 2 - e ^ 2) + z' * f ^ 2 : ℕ) : ℝ) =
        ((M * f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
      linear_combination hs'.trans hd
    exact ⟨x', y', z', by exact_mod_cast h'', by omega, fun _ => by omega, fun _ => hz'⟩
  · exact ⟨x, y, z, hcast, hz1, fun h2' => hz2 h2' hA, fun h => absurd h h3f⟩

/-- **`wTilable_not_of_small_M2`** (CONDITIONAL on `R2Count e f` when `e + 3 ≤ f`): audited statement (G1):
`e ≥ 2`, `M < f`, `M e ≥ f`, `M (f - e) ≤ e + 2`. -/
theorem wTilable_not_of_small_M2_of_R2 {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hMf : M < f) (hfM : f ≤ M * e) (hMfe : M * (f - e) ≤ e + 2)
    (hR2 : e + 3 ≤ f → R2Count e f) :
    ¬ Erdos634.Draft.CollarG.WTilable e f M := by
  rintro ⟨D, hT, hMod⟩
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; omega
    · exact h
  obtain ⟨x, y, z, hN, hz1, hz2, hz3⟩ := count_tiling_r2 e f M (by omega) hef hco hM hR2 D hT hMod
  exact r2_arith he hef hco hMf hMfe hN hz1 hz2 hz3

/-- the part that needs no geometry beyond S+: if `M (f - e) ≤ e + 1` the corollary is already `SplusThick.wTilable_not_of_small_M` -/
theorem wTilable_not_of_small_M2_easy {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hMf : M < f) (hfM : f ≤ M * e) (hMfe : M * (f - e) ≤ e + 1) :
    ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  wTilable_not_of_small_M hco he hef hMf hfM hMfe

-- the three covered instances are within the statement (hypotheses by `decide`)
theorem not_W_4_7_2_of_R2 (h : R2Count 4 7) : ¬ Erdos634.Draft.CollarG.WTilable 4 7 2 :=
  wTilable_not_of_small_M2_of_R2 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => h)
theorem not_W_7_10_3_of_R2 (h : R2Count 7 10) : ¬ Erdos634.Draft.CollarG.WTilable 7 10 3 :=
  wTilable_not_of_small_M2_of_R2 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => h)
theorem not_W_8_13_2_of_R2 (h : R2Count 8 13) : ¬ Erdos634.Draft.CollarG.WTilable 8 13 2 :=
  wTilable_not_of_small_M2_of_R2 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => h)
-- r = e+1 control (unconditional, from the old theorem)
theorem not_W_5_8_2_ctl : ¬ Erdos634.Draft.CollarG.WTilable 5 8 2 :=
  wTilable_not_of_small_M2_easy (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Erdos634.Draft.SplusR2

#print axioms Erdos634.Draft.SplusR2.count_tiling_r2
#print axioms Erdos634.Draft.SplusR2.wTilable_not_of_small_M2_of_R2
#print axioms Erdos634.Draft.SplusR2.not_W_4_7_2_of_R2
#print axioms Erdos634.Draft.SplusR2.not_W_5_8_2_ctl
