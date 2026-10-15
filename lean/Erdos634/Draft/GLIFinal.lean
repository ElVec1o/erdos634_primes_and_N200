import Mathlib.Tactic
import Erdos634.Draft.GLIMain

/-!
# `leafG_of_dissection`: the leaf-G triangle admits no `CongruentDissection` into the `γ = 2α` tile `s·(k², 2k+1, k(k+1))`, `k ≥ 3`

Hypotheses (all about a REAL `CongruentDissection D`):
* the model is the `γ = 2α` tile with sides `(a, b, c) = s·(k², 2k+1, k(k+1))`, `s > 0`, `k ≥ 3`, `α ∉ ℚπ` (`TwoAlphaData α a b c`);
* the target has base angles `α` at vertices `0` and `1` (so apex `π − 2α = α + β` at vertex `2`);
* its leg `|pts 1 − pts 2|` equals `s · 2k(2k+1)` (the leaf `m = 1` scale; the base is then forced by the law of sines to be `s · 2(k+1)(2k+1)`).
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG
  Erdos634.BaseChain

variable {N : ℕ}

theorem leafG_of_dissection (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ) (hk : 3 ≤ k) (hs : 0 < s)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α)
    (hX : dist (D.target.pts 1) (D.target.pts 2) = s * ((2 * k * (2 * k + 1) : ℕ) : ℝ)) : False := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hN : 0 < N := D.toDissection.pos
  have hC : D.target.angleAt 2 = Real.pi - 2 * α := by
    have hsum := D.target.angleAt_sum; rw [hA, hB] at hsum; linarith
  obtain ⟨κ, -, -, -, -, hcκ, -, hY, hL⟩ := Row4.sides D h hA hB
  have e1 : D.target.oppLen 0 = dist (D.target.pts 1) (D.target.pts 2) := rfl
  have e2 : D.target.oppLen 1 = dist (D.target.pts 2) (D.target.pts 0) := rfl
  have e3 : D.target.oppLen 2 = dist (D.target.pts 0) (D.target.pts 1) := rfl
  have d12 := hX
  have d20 : dist (D.target.pts 2) (D.target.pts 0) = s * ((2 * k * (2 * k + 1) : ℕ) : ℝ) := by
    rw [← e2, hL, e1]; exact hX
  have hκk : 2 * κ * k = k + 1 := by
    rw [hc, ha] at hcκ
    have h1 : s * k * ((k + 1) - 2 * κ * k) = 0 := by linear_combination hcκ
    have h2 : s * k ≠ 0 := by positivity
    have := (mul_eq_zero.mp h1).resolve_left h2
    linarith
  have d01 : dist (D.target.pts 0) (D.target.pts 1) = s * ((2 * (k + 1) * (2 * k + 1) : ℕ) : ℝ) := by
    rw [← e3, hY, e1, hX]; push_cast
    linear_combination (2 * s * (2 * k + 1)) * hκk
  -- walls and chains
  obtain ⟨W02, hW02a, hW02b⟩ := exists_wall D.toDissection 0 2 (by decide)
  obtain ⟨W12, hW12a, hW12b⟩ := exists_wall D.toDissection 1 2 (by decide)
  obtain ⟨W01, hW01a, hW01b⟩ := exists_wall D.toDissection 0 1 (by decide)
  obtain ⟨W10, hW10a, hW10b⟩ := exists_wall D.toDissection 1 0 (by decide)
  obtain ⟨E02, n02, C02⟩ := W02.exists_chain hN
  obtain ⟨E12, n12, C12⟩ := W12.exists_chain hN
  obtain ⟨E01, n01, C01⟩ := W01.exists_chain hN
  obtain ⟨E10, n10, C10⟩ := W10.exists_chain hN
  have hap := apex_pair D hα h (p := 0) (q := 1) (r := 2) (by decide) (by decide) (by decide) hC
    C02 C12 hW02a hW02b hW12a hW12b
  rcases hap with hap | hap
  · exact leafG_core D k hk hs ha hb hc hα h (p := 0) (q := 1) (r := 2) (by decide) (by decide) (by decide)
      hA hB hC (by rw [dist_comm]; exact d20) hX d01 C02 C12 C01 ⟨hW02a, hW02b⟩ ⟨hW12a, hW12b⟩
      ⟨hW01a, hW01b⟩ hap
  · exact leafG_core D k hk hs ha hb hc hα h (p := 1) (q := 0) (r := 2) (by decide) (by decide) (by decide)
      hB hA hC hX (by rw [dist_comm]; exact d20) (by rw [dist_comm]; exact d01) C12 C02 C10
      ⟨hW12a, hW12b⟩ ⟨hW02a, hW02b⟩ ⟨hW10a, hW10b⟩ ⟨hap.2, hap.1⟩

end Erdos634.GLI

#print axioms Erdos634.GLI.leafG_of_dissection
