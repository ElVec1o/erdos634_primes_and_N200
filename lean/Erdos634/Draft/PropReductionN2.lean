-- Draft/PropReductionN2.lean
-- `N = 2` of prop:reduction WITHOUT the plane-topology axiom `two_piece_cut_of_twoPiThree`.
--
-- Counting argument.  Each tile has exactly one corner of each of the three (distinct) angles `α, π/3 − α, 2π/3`,
-- so at most `N = 2` tile corners of a given angle sit at the three target corners (`cfig_le`).  The target angles sum
-- to `π`, and `α/π` is irrational: the only solution with all three counts `≤ 2` is one corner of each angle, i.e. the
-- target is similar to the tile (`LemmaCSimilar.cfig_ne_of_notSimilar`), which `TSPSimilar.tile_similar_prime_false`
-- excludes (`2` is not a square).
-- 0 sorry, standard axioms.

import Erdos634.Draft.PropReductionN3
import Erdos634.Draft.LemmaCFinal
import Erdos634.CornerAnglePerm

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCAssemble

namespace Erdos634.Draft.PropReductionN2

theorem third_vertex : ∀ m m' : Fin 3, m ≠ m' → ∃ n : Fin 3, m ≠ n ∧ m' ≠ n := by decide

/-- the model angles are `α`, `π/3 − α`, `2π/3` -/
theorem model_angle_cases {T : Tri} {α a b c : ℝ} (hm : T.TwoPiThreeData α a b c) (j : Fin 3) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = α ∨
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = Real.pi / 3 - α ∨
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = 2 * Real.pi / 3 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hm
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

/-- two corners of a tile cannot carry the same model angle -/
theorem no_double_angle {α θ δ : ℝ} (hirr : IrrPi α)
    (hθ : θ = α ∨ θ = Real.pi / 3 - α ∨ θ = 2 * Real.pi / 3)
    (hδ : δ = α ∨ δ = Real.pi / 3 - α ∨ δ = 2 * Real.pi / 3)
    (hsum : θ + θ + δ = Real.pi) : False := by
  have hpi := Real.pi_pos
  rcases hθ with rfl | rfl | rfl <;> rcases hδ with rfl | rfl | rfl
  · exact hirr ⟨1 / 3, by push_cast; linarith⟩
  · exact hirr ⟨2 / 3, by push_cast; linarith⟩
  · exact hirr ⟨1 / 6, by push_cast; linarith⟩
  · exact hirr ⟨-1 / 3, by push_cast; linarith⟩
  · exact hirr ⟨0, by push_cast; linarith⟩
  · exact hirr ⟨1 / 6, by push_cast; linarith⟩
  · exact hirr ⟨-1 / 3, by push_cast; linarith⟩
  · exact hirr ⟨2 / 3, by push_cast; linarith⟩
  · linarith

/-- **At most `N` tile corners of a given model angle sit at the three target corners.** -/
theorem cfig_le {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) (j : Fin 3) :
    ∑ k : Fin 3, cnt D (cornerAngle (D.model.pts (j + 1)) (D.model.pts j) (D.model.pts (j + 2))) (D.target.pts k)
      ≤ N := by
  set θ := cornerAngle (D.model.pts (j + 1)) (D.model.pts j) (D.model.pts (j + 2)) with hθ
  have hθ0 : 0 < θ := Erdos634.MarchFlank.cornerAngle_pos D.model j
  have hθπ : θ < Real.pi := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model j
  have hpi := Real.pi_pos
  set S : Fin 3 → Finset (Fin N) := fun k => {i | (D.tile i).localAngle (D.target.pts k) = θ} with hS
  have hdisj : ∀ k ∈ (Finset.univ : Finset (Fin 3)), ∀ l ∈ (Finset.univ : Finset (Fin 3)), k ≠ l →
      Disjoint (S k) (S l) := by
    intro k _ l _ hkl
    rw [Finset.disjoint_left]
    intro i hik hil
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hik hil
    obtain ⟨m, hmk⟩ := vertex_of_localAngle_corner (D.tile i) hik hθ0.ne' hθπ.ne (by linarith)
    obtain ⟨m', hml⟩ := vertex_of_localAngle_corner (D.tile i) hil hθ0.ne' hθπ.ne (by linarith)
    have hmm : m ≠ m' := by
      rintro rfl
      exact hkl (D.target.indep.injective (hmk.symm.trans hml))
    rw [← hmk, Tri.localAngle_vertex] at hik
    rw [← hml, Tri.localAngle_vertex] at hil
    obtain ⟨n, hmn, hm'n⟩ := third_vertex m m' hmm
    obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm n
    have hsum := Erdos634.Draft.LemmaCFinal.sum3
      (fun q => cornerAngle ((D.tile i).pts (q + 1)) ((D.tile i).pts q) ((D.tile i).pts (q + 2))) m m' n hmm hmn hm'n
    have hpiT := Erdos634.Geometry.cornerAngle_sum (D.tile i)
    have hsum' : θ + θ + cornerAngle (D.model.pts (k' + 1)) (D.model.pts k') (D.model.pts (k' + 2)) = Real.pi := by
      have e : (fun q => cornerAngle ((D.tile i).pts (q + 1)) ((D.tile i).pts q) ((D.tile i).pts (q + 2))) 0
          + (fun q => cornerAngle ((D.tile i).pts (q + 1)) ((D.tile i).pts q) ((D.tile i).pts (q + 2))) 1
          + (fun q => cornerAngle ((D.tile i).pts (q + 1)) ((D.tile i).pts q) ((D.tile i).pts (q + 2))) 2
          = Real.pi := hpiT
      rw [← hsum] at e
      simp only at e
      rw [hik, hil, hk'] at e
      exact e
    exact no_double_angle hirr (model_angle_cases hm j) (model_angle_cases hm k') hsum'
  calc ∑ k : Fin 3, cnt D θ (D.target.pts k) = ∑ k : Fin 3, (S k).card := rfl
    _ = ((Finset.univ : Finset (Fin 3)).biUnion S).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = N := by simp

/-- **`N = 2` is impossible for a `2π/3`-tile with irrational angle** -- no axiom. -/
theorem tp_two_excluded (D : CongruentDissection 2) {α a b c : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) : False := by
  by_cases hs : SimilarTM D
  · exact Erdos634.Draft.TSPSimilar.tile_similar_prime_false D Nat.prime_two hirr hm hs
  have hpi := Real.pi_pos
  set x0 := cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) with hx0
  set x1 := cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) with hx1
  set x2 := cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) with hx2
  have hpos : ∀ m, 0 < cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2)) :=
    fun m => Erdos634.MarchFlank.cornerAngle_pos D.model m
  have hlt : ∀ m, cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2)) < Real.pi :=
    fun m => Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model m
  have hsumM : x0 + x1 + x2 = Real.pi := Erdos634.Geometry.cornerAngle_sum D.model
  -- the three model angles are α, π/3 − α, 2π/3 in some order: all distinct
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := id hm
  have hval : ∀ m : Fin 3, cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2)) =
      D.model.angleAt m := fun _ => rfl
  have hne01 : α ≠ Real.pi / 3 - α := fun h => hirr ⟨1 / 6, by push_cast; linarith⟩
  have hne02 : α ≠ 2 * Real.pi / 3 := fun h => hirr ⟨2 / 3, by push_cast; linarith⟩
  have hne12 : Real.pi / 3 - α ≠ 2 * Real.pi / 3 := fun h => hirr ⟨-1 / 3, by push_cast; linarith⟩
  have hinj : ∀ p q : Fin 3, D.model.angleAt p = D.model.angleAt q → p = q := by
    intro p q hpq
    obtain ⟨p', rfl⟩ := σ.surjective p
    obtain ⟨q', rfl⟩ := σ.surjective q
    congr 1
    have hp : p' = 0 ∨ p' = 1 ∨ p' = 2 := by fin_cases p' <;> simp
    have hq : q' = 0 ∨ q' = 1 ∨ q' = 2 := by fin_cases q' <;> simp
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
      | rfl
      | (rw [h0, h1] at hpq; exact absurd hpq hne01)
      | (rw [h0, h2] at hpq; exact absurd hpq hne02)
      | (rw [h1, h0] at hpq; exact absurd hpq.symm hne01)
      | (rw [h1, h2] at hpq; exact absurd hpq hne12)
      | (rw [h2, h0] at hpq; exact absurd hpq.symm hne02)
      | (rw [h2, h1] at hpq; exact absurd hpq.symm hne12)
  have h01 : x0 ≠ x1 := fun h => absurd (hinj 0 1 h) (by decide)
  have h02 : x0 ≠ x2 := fun h => absurd (hinj 0 2 h) (by decide)
  have h12 : x1 ≠ x2 := fun h => absurd (hinj 1 2 h) (by decide)
  have hne := Erdos634.Draft.LemmaCSimilar.cfig_ne_of_notSimilar D x0 x1 x2 rfl rfl rfl h01 h02 h12
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) hs
  have hcorner := fun kk => Erdos634.Draft.LemmaCFigures.corner_figure D x0 x1 x2 rfl rfl rfl h01 h02 h12
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) kk
  -- the corner totals
  set A : Fin 3 → ℕ := fun m => ∑ k : Fin 3,
    cnt D (cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))) (D.target.pts k) with hA
  have hA2 : ∀ m, A m ≤ 2 := fun m => cfig_le D hirr hm m
  have hAsum : (A 0 : ℝ) * x0 + (A 1 : ℝ) * x1 + (A 2 : ℝ) * x2 = Real.pi := by
    have e0 := (hcorner 0).2.1
    have e1 := (hcorner 1).2.1
    have e2 := (hcorner 2).2.1
    have hT := Erdos634.Geometry.cornerAngle_sum D.target
    have t0 : cornerAngle (D.target.pts ((0 : Fin 3) + 1)) (D.target.pts 0) (D.target.pts ((0 : Fin 3) + 2)) =
        cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) := rfl
    have t1 : cornerAngle (D.target.pts ((1 : Fin 3) + 1)) (D.target.pts 1) (D.target.pts ((1 : Fin 3) + 2)) =
        cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) := rfl
    have t2 : cornerAngle (D.target.pts ((2 : Fin 3) + 1)) (D.target.pts 2) (D.target.pts ((2 : Fin 3) + 2)) =
        cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) := rfl
    rw [t0] at e0; rw [t1] at e1; rw [t2] at e2
    simp only [hA, Fin.sum_univ_three, cnt]
    push_cast
    have a0 : cornerAngle (D.model.pts ((0 : Fin 3) + 1)) (D.model.pts 0) (D.model.pts ((0 : Fin 3) + 2)) = x0 := rfl
    have a1 : cornerAngle (D.model.pts ((1 : Fin 3) + 1)) (D.model.pts 1) (D.model.pts ((1 : Fin 3) + 2)) = x1 := rfl
    have a2 : cornerAngle (D.model.pts ((2 : Fin 3) + 1)) (D.model.pts 2) (D.model.pts ((2 : Fin 3) + 2)) = x2 := rfl
    simp only [← hx0, ← hx1, ← hx2]
    linarith
  have hA3 : 3 ≤ A 0 + A 1 + A 2 := by
    have p0 : 1 ≤ cnt D x0 (D.target.pts 0) + cnt D x1 (D.target.pts 0) + cnt D x2 (D.target.pts 0) :=
      (hcorner 0).2.2
    have p1 : 1 ≤ cnt D x0 (D.target.pts 1) + cnt D x1 (D.target.pts 1) + cnt D x2 (D.target.pts 1) :=
      (hcorner 1).2.2
    have p2 : 1 ≤ cnt D x0 (D.target.pts 2) + cnt D x1 (D.target.pts 2) + cnt D x2 (D.target.pts 2) :=
      (hcorner 2).2.2
    show 3 ≤ (∑ k : Fin 3, cnt D x0 (D.target.pts k)) + (∑ k : Fin 3, cnt D x1 (D.target.pts k))
      + (∑ k : Fin 3, cnt D x2 (D.target.pts k))
    simp only [Fin.sum_univ_three]
    omega
  -- reindex by σ: the totals at the α-, (π/3−α)-, 2π/3-corners
  have hre : (A (σ 0) : ℝ) * α + (A (σ 1) : ℝ) * (Real.pi / 3 - α) + (A (σ 2) : ℝ) * (2 * Real.pi / 3) = Real.pi := by
    have hs3 := Erdos634.Draft.LemmaCFinal.sum3 (fun m => (A m : ℝ) * D.model.angleAt m) (σ 0) (σ 1) (σ 2)
      (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
    simp only at hs3
    rw [h0, h1, h2] at hs3
    rw [hs3]
    exact hAsum
  have hsum3 : A (σ 0) + A (σ 1) + A (σ 2) = A 0 + A 1 + A 2 :=
    Erdos634.Draft.LemmaCFinal.sum3 A (σ 0) (σ 1) (σ 2)
      (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
  have b0 := hA2 (σ 0); have b1 := hA2 (σ 1); have b2 := hA2 (σ 2)
  -- irrationality: A(σ0) = A(σ1)
  have heq : A (σ 0) = A (σ 1) := by
    by_contra hne'
    have hd : ((A (σ 0) : ℝ) - A (σ 1)) ≠ 0 := by
      intro h
      exact hne' (by exact_mod_cast sub_eq_zero.mp h)
    refine hirr ⟨((3 : ℚ) - A (σ 1) - 2 * A (σ 2)) / (3 * ((A (σ 0) : ℚ) - A (σ 1))), ?_⟩
    push_cast
    field_simp
    nlinarith [hre]
  rw [heq] at hre
  have hlin : (A (σ 1) : ℝ) + 2 * A (σ 2) = 3 := by
    have : ((A (σ 1) : ℝ) + 2 * A (σ 2) - 3) * Real.pi = 0 := by nlinarith [hre]
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpi.ne'
  have hlinN : A (σ 1) + 2 * A (σ 2) = 3 := by exact_mod_cast hlin
  have hall : A (σ 0) = 1 ∧ A (σ 1) = 1 ∧ A (σ 2) = 1 := by omega
  -- hence every total is 1
  have hA1 : ∀ m, A m = 1 := by
    intro m
    obtain ⟨m', rfl⟩ := σ.surjective m
    have hm' : m' = 0 ∨ m' = 1 ∨ m' = 2 := by fin_cases m' <;> simp
    rcases hm' with rfl | rfl | rfl
    · exact hall.1
    · exact hall.2.1
    · exact hall.2.2
  exact hne ⟨hA1 0, hA1 1, hA1 2⟩

end Erdos634.Draft.PropReductionN2

#print axioms Erdos634.Draft.PropReductionN2.tp_two_excluded
