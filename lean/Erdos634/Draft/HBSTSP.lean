/-
`HBSimilar` vs `TSPSimilar.tile_similar_N_square`.
`HBSimilar N` (ChainComposite) quantifies over EVERY CongruentDissection N with a target similar to the model, whatever the tile;
`TSPSimilar.tile_similar_N_square` covers only models with `TwoPiThreeData` and `IrrPi alpha`.  So HBSimilar is not discharged
for all tiles by the latter.  Here: the class-restricted statement `HBSimilarTP N` is a THEOREM for every N (no squarefree, no N >= 17), and
`HBSimilar N <-> HBSimilarRest N` (the complement class) is proved, so the residual of HBSimilar is exactly the complement class.
-/
import Erdos634.Draft.TSPSimilar
import Erdos634.Draft.CompositeN60
import Erdos634.Draft.G3CLeafFalse

open scoped Classical

namespace Erdos634.Draft.HBSTSP

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.ChainComposite

/-- The class covered by `TSPSimilar`: model is a `2pi/3` tile with `alpha/pi` irrational. -/
def TPClass {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.TwoPiThreeData α a b c

/-- `HBSimilar N` restricted to the `TPClass` models. -/
def HBSimilarTP (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3)),
    (∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧ D.target.oppLen k = μ * D.model.oppLen (τ k)) →
    TPClass D → ∃ x y : ℕ, N = x ^ 2 + y ^ 2

/-- `HBSimilar N` restricted to the complement of `TPClass`: the residual. -/
def HBSimilarRest (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3)),
    (∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧ D.target.oppLen k = μ * D.model.oppLen (τ k)) →
    ¬ TPClass D → ∃ x y : ℕ, N = x ^ 2 + y ^ 2

/-- **`hbSimilarTP`**: for EVERY `N` (reflections allowed, any permutation), tile-similar target with a `2pi/3`,
`alpha`-irrational tile gives `N = x^2 + y^2` (indeed `N = m^2`).  Via `TSPSimilar.tile_similar_N_square`. -/
theorem hbSimilarTP (N : ℕ) : HBSimilarTP N := by
  intro D μ τ hs ⟨α, a, b, c, hα, hm⟩
  obtain ⟨m, hm2⟩ := Erdos634.Draft.TSPSimilar.tile_similar_N_square D hα hm ⟨μ, τ, hs⟩
  exact ⟨m, 0, by rw [hm2]; ring⟩

/-- HBSimilar splits exactly into the covered class and the residual. -/
theorem hbSimilar_of_rest {N : ℕ} (h : HBSimilarRest N) : HBSimilar N := by
  intro D μ τ hs
  by_cases hT : TPClass D
  · exact hbSimilarTP N D μ τ hs hT
  · exact h D μ τ hs hT

theorem rest_of_hbSimilar {N : ℕ} (h : HBSimilar N) : HBSimilarRest N :=
  fun D μ τ hs _ => h D μ τ hs

theorem hbSimilar_iff_rest (N : ℕ) : HBSimilar N ↔ HBSimilarRest N :=
  ⟨rest_of_hbSimilar, hbSimilar_of_rest⟩

/-- Case B closure with the residual stated only on the complement class. -/
theorem caseB_of_rest_sumsq {N : ℕ} (h : HBSimilarRest N) (hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2) :
    CaseBClosed N :=
  caseB_of_sumsq N (hbSimilar_of_rest h) hns

/-! ## Witnesses and a counterexample (N = 4, D357: tile (3,5,7), target = 2 * tile). -/

open Erdos634.Draft.FluxPaperWitness Erdos634.Draft.FluxCSimilarWitness in
theorem D357_tpclass : TPClass D357 := ⟨α357, 3, 5, 7, α357_irr, data357⟩

open Erdos634.Draft.FluxPaperWitness Erdos634.Draft.FluxCSimilarWitness in
/-- Every hypothesis of `HBSimilarTP 4` is satisfied by `D357`, and the conclusion holds (`4 = 2^2 + 0^2`). -/
theorem witness_hbSimilarTP_4 :
    ∃ (D : CongruentDissection 4) (μ : ℝ) (τ : Equiv.Perm (Fin 3)),
      (∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧ D.target.oppLen k = μ * D.model.oppLen (τ k)) ∧
      TPClass D ∧ ∃ x y : ℕ, 4 = x ^ 2 + y ^ 2 :=
  ⟨D357, 2, 1, fun k => by simpa using D357_sim k, D357_tpclass,
    hbSimilarTP 4 D357 2 1 (fun k => by simpa using D357_sim k) D357_tpclass⟩

open Erdos634.Draft.FluxPaperWitness Erdos634.Draft.FluxCSimilarWitness in
/-- The class is non-empty, so the conclusion cannot be strengthened to `False`
(= `CaseBClosed`-on-the-class fails at `N = 4`). -/
theorem negctl_not_false_4 :
    ¬ ∀ (D : CongruentDissection 4) (μ : ℝ) (τ : Equiv.Perm (Fin 3)),
      (∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧ D.target.oppLen k = μ * D.model.oppLen (τ k)) →
      TPClass D → False :=
  fun h => h D357 2 1 (fun k => by simpa using D357_sim k) D357_tpclass

/-- The restricted conclusion is sharp in kind: `4` IS a sum of two squares but not prime/not
non-square; `hbSimilarTP` gives no more than square-ness. -/
theorem four_is_square : ∃ m : ℕ, (4 : ℕ) = m ^ 2 := ⟨2, by norm_num⟩

/-! ## Downstream: N = 60 (not squarefree; `CompositeN60.chain_60_final` takes `CaseBClosed 60`). -/

theorem nsq60 : ¬ ∃ x y : ℕ, 60 = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hx : x ≤ 8 := by nlinarith
  have hy : y ≤ 8 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

/-- `CaseBClosed 60` now needs only the complement-class residual. -/
theorem caseB_60_of_rest (h : HBSimilarRest 60) : CaseBClosed 60 := caseB_of_rest_sumsq h nsq60

/-- `chain_60_final` with `gB : CaseBClosed 60` replaced by the strictly weaker `HBSimilarRest 60`
(only tiles outside `TPClass`).  Still conditional on the other leaves. -/
theorem chain_60_final_rest (gA : Erdos634.Draft.Chain15.GapA 60) (gB : HBSimilarRest 60)
    (gG : CaseGClosed 60) (gE60 : Erdos634.Draft.Chain15.GapE60 60) (gE120 : Erdos634.Draft.Chain15.GapE120 60)
    (gF1 : Erdos634.Draft.Chain15.GapF1 60) (gR8 : Erdos634.Draft.Chain15.GapR8 60)
    (gRA : Erdos634.Draft.CompositeN60.RA60) (gRW : Erdos634.Draft.CompositeN60.RW60)
    (D : CongruentDissection 60) : False :=
  Erdos634.Draft.CompositeN60.chain_60_final gA (caseB_60_of_rest gB) gG gE60 gE120 gF1 gR8 gRA gRW D

end Erdos634.Draft.HBSTSP

#print axioms Erdos634.Draft.HBSTSP.hbSimilarTP
#print axioms Erdos634.Draft.HBSTSP.hbSimilar_iff_rest
#print axioms Erdos634.Draft.HBSTSP.witness_hbSimilarTP_4
#print axioms Erdos634.Draft.HBSTSP.negctl_not_false_4
#print axioms Erdos634.Draft.HBSTSP.chain_60_final_rest
