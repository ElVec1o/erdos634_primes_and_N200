/-
Draft/WGapMirrorLat.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P3, P5).
Not imported by any aggregate.  Module W2c of the W-gap Lean plan.

KEY BRIDGE: the mirror lattice IS a lattice with real coordinates of the corner lattice.
`mpG_eq` : `p'(ξ, η) = μ p(ξ, η) = p(−ξ, η + s ξ)`,  `s = (2f² − e²)/(f² − e²) = K/b`.
Hence every fact about the mirror lattice (distances `dist_lpG`, `QfG`, crosses `cross_mG`, `cross_rowG`, `lineMap_lpG`, injectivity
`lpG_ne_xi`) is a fact about `lpG` at the real coordinates `(−ξ, η + sξ)`; no coordinate formula for the reflection is ever needed again.
Proof: `μ` is an isometry fixing `p(0,0)`, `p(0,1)`; the candidate `q = p(−ξ, η + sξ)` has the same two distances to those points
(`QfG` identity); two circles meet in at most two points (`Mathlib eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`), and `μ p = p` only
on the line `ξ = 0` where `q = p`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapMirror

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

/-- the slope `s = K / b` of the mirror: `μ u = −u + s v` -/
noncomputable def sMir (e f : ℝ) : ℝ := (2 * f ^ 2 - e ^ 2) / (f ^ 2 - e ^ 2)

theorem sMir_mul {e f : ℝ} (he : 0 < e) (hef : e < f) : sMir e f * (f ^ 2 - e ^ 2) = 2 * f ^ 2 - e ^ 2 := by
  unfold sMir
  have : f ^ 2 - e ^ 2 ≠ 0 := by nlinarith
  field_simp

theorem QfG_mirror {e f : ℝ} (he : 0 < e) (hef : e < f) (dξ dη : ℝ) :
    QfG e f (-dξ) (dη + sMir e f * dξ) = QfG e f dξ dη := by
  have h := sMir_mul he hef
  unfold QfG
  have : (2 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) * (-dξ * (dη + sMir e f * dξ)) =
      -((2 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) * (dξ * dη)) - (2 * f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2) * dξ ^ 2 := by
    rw [← h]; ring
  have h2 : (f ^ 2 - e ^ 2) ^ 2 * (dη + sMir e f * dξ) ^ 2 =
      (f ^ 2 - e ^ 2) ^ 2 * dη ^ 2 + 2 * (2 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) * dξ * dη + (2 * f ^ 2 - e ^ 2) ^ 2 * dξ ^ 2 := by
    have : (f ^ 2 - e ^ 2) ^ 2 * (dη + sMir e f * dξ) ^ 2 = ((f ^ 2 - e ^ 2) * dη + sMir e f * (f ^ 2 - e ^ 2) * dξ) ^ 2 := by ring
    rw [this, h]; ring
  rw [show (-dξ) ^ 2 = dξ ^ 2 by ring]
  linear_combination this + h2

/-- **THE BRIDGE** -/
theorem mpG_eq {e f : ℝ} (he : 0 < e) (hef : e < f) (x ξ η : ℝ) :
    mpG e f 1 x ξ η = lpG e f 1 x (-ξ) (η + sMir e f * ξ) := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  set p := lpG e f 1 x ξ η with hp
  set q := lpG e f 1 x (-ξ) (η + sMir e f * ξ) with hq
  set A := lpG e f 1 x 0 0 with hA
  set B := lpG e f 1 x 0 1 with hB
  have hAB : A ≠ B := lpG_ne_eta he hef (by norm_num)
  by_cases hξ : ξ = 0
  · subst hξ
    have hqp : q = p := by
      rw [hq, hp]; exact lpG_congr (by ring) (by ring)
    rw [hqp]
    have hmem : p ∈ affineSpan ℝ {A, B} := by
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨η, ?_⟩
      rw [hA, hB, lineMap_lpG, hp]
      exact lpG_congr (by ring) (by ring)
    unfold mpG reflL
    exact (EuclideanGeometry.reflection_eq_self_iff _).mpr hmem
  · have hpq : p ≠ q := lpG_ne_xi he hef hε (by intro h; apply hξ; linarith)
    have hrA : dist (mpG e f 1 x ξ η) A = dist p A := by
      have := refl_dist e f 1 x p A
      have h0 : reflL e f 1 x A = A := by
        unfold reflL
        exact (EuclideanGeometry.reflection_eq_self_iff _).mpr (left_mem_affineSpan_pair ℝ _ _)
      rw [h0] at this; exact this
    have hrB : dist (mpG e f 1 x ξ η) B = dist p B := by
      have := refl_dist e f 1 x p B
      have h0 : reflL e f 1 x B = B := by
        unfold reflL
        exact (EuclideanGeometry.reflection_eq_self_iff _).mpr (right_mem_affineSpan_pair ℝ _ _)
      rw [h0] at this; exact this
    have hqA : dist q A = dist p A := by
      apply dist_eq_of_sq_eq _ dist_nonneg dist_nonneg
      rw [hq, hp, hA, dist_lpG_sq he hef hε, dist_lpG_sq he hef hε]
      have h := QfG_mirror he hef ξ η
      simp only [sub_zero]
      exact h
    have hqB : dist q B = dist p B := by
      apply dist_eq_of_sq_eq _ dist_nonneg dist_nonneg
      rw [hq, hp, hB, dist_lpG_sq he hef hε, dist_lpG_sq he hef hε]
      have h := QfG_mirror he hef ξ (η - 1)
      rw [show η + sMir e f * ξ - 1 = η - 1 + sMir e f * ξ by ring]
      simp only [sub_zero]
      exact h
    have hfr : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
    rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hfr (c₁ := A) (c₂ := B) (p₁ := p) (p₂ := q)
      (p := mpG e f 1 x ξ η) (r₁ := dist p A) (r₂ := dist p B) hAB hpq rfl hqA hrA rfl hqB hrB with h | h
    · exfalso
      have hfix : reflL e f 1 x p = p := h
      have hmem : p ∈ affineSpan ℝ {A, B} :=
        (EuclideanGeometry.reflection_eq_self_iff _).mp hfix
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hmem
      obtain ⟨t, ht⟩ := hmem
      rw [hA, hB, lineMap_lpG, hp] at ht
      have h0 := lpG_xi_eq he hef hε ht
      exact hξ (by linarith)
    · exact h

theorem mpG_eq_zero {e f : ℝ} (he : 0 < e) (hef : e < f) (x η : ℝ) :
    mpG e f 1 x 0 η = lpG e f 1 x 0 η := by
  rw [mpG_eq he hef]; exact lpG_congr (by ring) (by ring)

/-- negative control: the mirror is NOT the identity off the line (`p'(1,0) ≠ p(1,0)`) -/
theorem mpG_ne_lpG {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) :
    mpG e f 1 x 1 0 ≠ lpG e f 1 x 1 0 := by
  rw [mpG_eq he hef]
  exact lpG_ne_xi he hef (by norm_num) (by norm_num)

/-- witness at `(e,f) = (2,3)`: `s = 14/5` and `p'(1,0) = p(−1, 14/5)` -/
example : sMir 2 3 = 14 / 5 := by unfold sMir; norm_num

#print axioms mpG_eq

end Erdos634.Draft.WGapStmt
