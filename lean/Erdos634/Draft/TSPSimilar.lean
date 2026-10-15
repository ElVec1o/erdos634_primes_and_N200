-- Tile-similar target, prime N, no mod-4 hypothesis; combined with G1NFinal into the complete
-- tiling-level reduction for primes.
-- `Paper.cor_similar` (FluxCSimilar) is stated for the identity vertex order; `SimilarTM`
-- carries a permutation, so we relabel the model.
import Mathlib
import Erdos634.Draft.G1NFinal
import Erdos634.Draft.FluxCSimilar
import Erdos634.Draft.FluxCSimilarWitness

open scoped Classical

namespace Erdos634.Draft.TSPSimilar

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

/-- The relabelled model keeps a `TwoPiThreeData` description (`sigma' = tau^-1 * sigma`). -/
theorem twoPiThreeData_relabel {T U : Tri} (τ : Equiv.Perm (Fin 3)) (hU : ∀ k, U.pts k = T.pts (τ k))
    {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) : U.TwoPiThreeData α a b c := by
  obtain ⟨σ, h0, ha, h1, hb, h2, hc⟩ := h
  have key : ∀ k, U.angleAt (τ.symm k) = T.angleAt k ∧ U.oppLen (τ.symm k) = T.oppLen k := by
    intro k
    have := Row2.angleAt_comp T U τ hU (τ.symm k)
    simpa using this
  refine ⟨τ.symm * σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Equiv.Perm.mul_apply]
  · rw [(key _).1]; exact h0
  · rw [(key _).2]; exact ha
  · rw [(key _).1]; exact h1
  · rw [(key _).2]; exact hb
  · rw [(key _).1]; exact h2
  · rw [(key _).2]; exact hc

/-- **Tile-similar target, any vertex correspondence: `N` is a perfect square.**  `D` any `CongruentDissection N`
(reflections allowed), model a `2pi/3` tile with `alpha/pi` irrational, target similar to the model (some permutation,
ratio `mu`).  No primality, no residue condition on `N`. -/
theorem tile_similar_N_square {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) (hs : SimilarTM D) : ∃ m : ℕ, N = m ^ 2 := by
  obtain ⟨μ, τ, h⟩ := hs
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  have hm' : (D.relabelModel τ).model.TwoPiThreeData α a b c :=
    twoPiThreeData_relabel τ (fun k => rfl) hm
  obtain ⟨m, hN, -, -⟩ := Paper.cor_similar (D.relabelModel τ) hα hm' (μ := μ) (fun k => by
    rw [(hMa k).1, (hMa k).2]; exact h k)
  exact ⟨m, hN⟩

/-- **`tile_similar_prime_false`.**  Prime `N` (no `N > 3`, no mod 4), `2pi/3` tile, `alpha/pi` irrational,
target similar to the tile: `False`. -/
theorem tile_similar_prime_false {N : ℕ} (D : CongruentDissection N) (hN : N.Prime) {α a b c : ℝ}
    (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) (hs : SimilarTM D) : False := by
  obtain ⟨m, hm2⟩ := tile_similar_N_square D hα hm hs
  exact hN.not_isSquare ⟨m, by rw [hm2]; ring⟩

/-- **`prop:reduction` for primes, complete at the tiling level**: no `N`-tiling with `N` prime, `N > 3`, by a tile
`(alpha, beta, 2pi/3)` with `alpha/pi` irrational, whatever the target (similar or not).  No integrality, no `N % 4`. -/
theorem reduction_tiling_complete {N : ℕ} (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 < N)
    {α a b c : ℝ} (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) : False := by
  by_cases hs : SimilarTM D
  · exact tile_similar_prime_false D hN hα hm hs
  · exact Erdos634.Draft.G1NFinal.tp_prime_excluded D hN h3 hα hm hs

/-! ## Witnesses.  `D357` (real `CongruentDissection 4`, tile `(3,5,7)`, target `2 * tile`) satisfies every hypothesis
of `tile_similar_prime_false` except `N.Prime`, and the conclusion of `tile_similar_N_square` holds there. -/

open Erdos634.Draft.FluxPaperWitness Erdos634.Draft.FluxCSimilarWitness in
theorem D357_similarTM : SimilarTM D357 := ⟨2, 1, fun k => by simpa using D357_sim k⟩

open Erdos634.Draft.FluxPaperWitness Erdos634.Draft.FluxCSimilarWitness in
theorem control_D357 :
    IrrPi α357 ∧ D357.model.TwoPiThreeData α357 3 5 7 ∧ SimilarTM D357 ∧ ¬ (2 * 2 : ℕ).Prime ∧
      ∃ m : ℕ, (2 * 2 : ℕ) = m ^ 2 :=
  ⟨α357_irr, data357, D357_similarTM, by decide, tile_similar_N_square D357 α357_irr data357 D357_similarTM⟩

-- Permutation path exercised: the same dissection with the model relabelled by a transposition is still tile-similar,
-- now with a non-identity `tau`; `tile_similar_N_square` goes through the relabelling.
open Erdos634.Draft.FluxPaperWitness Erdos634.Draft.FluxCSimilarWitness in
theorem control_D357_perm :
    ∃ (D : CongruentDissection (2 * 2)) (a b c : ℝ), D.model.TwoPiThreeData α357 a b c ∧ SimilarTM D ∧
      ∃ m : ℕ, (2 * 2 : ℕ) = m ^ 2 := by
  have hm : (D357.relabelModel (Equiv.swap 0 1)).model.TwoPiThreeData α357 3 5 7 :=
    twoPiThreeData_relabel (Equiv.swap 0 1) (fun k => rfl) data357
  have hs : SimilarTM (D357.relabelModel (Equiv.swap 0 1)) := by
    refine ⟨2, Equiv.swap 0 1, fun k => ?_⟩
    have hMa := Row2.angleAt_comp D357.model (D357.relabelModel (Equiv.swap 0 1)).model (Equiv.swap 0 1) (fun k => rfl)
    obtain ⟨h1, h2⟩ := D357_sim k
    rw [(hMa _).1, (hMa _).2]
    simpa using (⟨h1, h2⟩ : _ ∧ _)
  exact ⟨_, 3, 5, 7, hm, hs, tile_similar_N_square _ α357_irr hm hs⟩

end Erdos634.Draft.TSPSimilar

#print axioms Erdos634.Draft.TSPSimilar.twoPiThreeData_relabel
#print axioms Erdos634.Draft.TSPSimilar.tile_similar_N_square
#print axioms Erdos634.Draft.TSPSimilar.tile_similar_prime_false
#print axioms Erdos634.Draft.TSPSimilar.reduction_tiling_complete
#print axioms Erdos634.Draft.TSPSimilar.control_D357
#print axioms Erdos634.Draft.TSPSimilar.control_D357_perm
