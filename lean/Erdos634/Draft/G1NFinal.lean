import Mathlib
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.ISUCore
import Erdos634.Draft.ISUReduce
import Erdos634.Draft.ISUMain
import Erdos634.Draft.R8F2to4Bridge
import Erdos634.Draft.F1FreeProof
import Erdos634.Draft.FluxCRow5TwoPiThreeFull
import Erdos634.Draft.FluxERow2S
import Erdos634.Draft.G3CIsoControl

/-!
# The reduction for PRIME N with no integer-tile hypothesis

The reduction takes the tile `(alpha, beta, 2pi/3)` with `alpha/pi` irrational and
NOTHING about integer sides.  Every exclusion theorem the route ends in already exists with REAL sides, and the
classification of the target is `LemmaCFinal.lemmaC_general` (N-free).  Hence an integer-tile hypothesis is not needed
for the conclusion at prime N > 3:

* `tp_prime_excluded`: prime `N > 3` (ANY residue mod 4), `D : CongruentDissection N`, tile `TwoPiThreeData alpha a b c` with
  `a b c : R`, `IrrPi alpha`, target NOT similar to the tile  ==>  `False`.
* `reduction_tiling_final`: the conclusion (two equal angles, not all pi/3), obtained from `tp_prime_excluded`.
* `tp_prime_excluded_mod3`: `N % 4 = 3` allows the similar target as well (`Row2.theoremS_perm`).

The F2..F4' dispatch is `R8F2to4Bridge.r8_reduction_statement` and the F1 dispatch is `F1FreeProof.f1_free_statement` with
the (unused) hypothesis `N % 4 = 3` removed; both proofs never used it.  `f1_word_from_bzero` is `private` in `F1FreeProof`
and is copied verbatim below.
-/

open scoped Classical

open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.G1NFinal

open Erdos634.Geometry Erdos634.Draft.LemmaCFinal Erdos634.Draft.ISUReduce
open Erdos634.Draft.F1BEdgeBoundary (f1_V1V2_b_zero)
open Erdos634.Draft.F1TprimeExtract (f1_Tprime_K2_proved)
open Erdos634.Draft.F1AreaIdentity (F1_area_identity)
open Erdos634.Draft.F1AlgebraPin (f1_pin_mu_of_prime)

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

/-! ## F1 and F1': copy of `F1FreeProof.f1_word_from_bzero` (private there) and of `f1_free_statement` without `N % 4 = 3` -/

private lemma f1_word_from_bzero {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) (hN : N.Prime) (h3 : 3 < N)
    (σ : Equiv.Perm (Fin 3))
    (hside_eq : dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) = μ * (a + b)) :
    ∀ P R : ℕ, (P : ℝ) * a + (R : ℝ) * c =
      dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) →
    P = 1 ∧ R = 1 := by
  -- Arithmetic is identical to f1_V1V2_word_count; σ and hside_eq come from the caller.
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, hmu⟩ := f1_pin_mu_of_prime D hirr hm hF1 hμ hN
  have harea : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmu_ab : μ * (a + b) = 2 * (N : ℝ) * c / ((N : ℝ) + 1) :=
    F1BEdgeBoundary.f1_mu_ab_val ha0 hb0 hc0 hμ hpin hmu harea hN1pos
  have ha_val : a = c * ((N : ℝ) - 1) / ((N : ℝ) + 1) := by
    field_simp [hN1pos.ne']; linarith
  intro P R hPR
  rw [hside_eq, hmu_ab] at hPR
  rw [ha_val] at hPR
  have hNm2 : (N : ℤ) ≥ 5 := by
    have h4 : N ≠ 4 := by intro h; subst h; exact absurd hN (by norm_num)
    have := hN.two_le; omega
  have hcne : c ≠ 0 := hc0.ne'
  have hN1ne : ((N : ℝ) + 1) ≠ 0 := hN1pos.ne'
  have hPR_eq : (P : ℝ) * ((N : ℝ) - 1) + (R : ℝ) * ((N : ℝ) + 1) = 2 * (N : ℝ) := by
    have : c * ((P : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) + (R : ℝ)) =
           c * (2 * (N : ℝ) / ((N : ℝ) + 1)) := by
      field_simp [hcne, hN1ne] at hPR ⊢; linarith
    have := mul_left_cancel₀ hcne this
    field_simp [hN1ne] at this ⊢; linarith
  have hN_ge5 : 5 ≤ N := by exact_mod_cast hNm2
  have hN1 : 1 ≤ N := by omega
  have hPR_nat : P * (N - 1) + R * (N + 1) = 2 * N := by
    have hN1cast : (N : ℝ) - 1 = ((N - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub hN1]
    have hN1cast2 : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    have h : (P : ℝ) * ((N - 1 : ℕ) : ℝ) + (R : ℝ) * ((N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) := by
      rw [← hN1cast, ← hN1cast2]; exact hPR_eq
    exact_mod_cast h
  have hR_le1 : R ≤ 1 := by nlinarith [Nat.zero_le (P * (N - 1))]
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0; simp at hPR_nat
    have hdvd_2 : (N : ℤ) - 1 ∣ 2 := by
      have heq : ((N : ℤ) - 1) * P = 2 * (N : ℤ) := by
        have : P * (N - 1) = 2 * N := hPR_nat
        exact_mod_cast show (N - 1) * P = 2 * N from by linarith
      have h1 : (N : ℤ) - 1 ∣ ((N : ℤ) - 1) * P := dvd_mul_right _ _
      have h2 : (N : ℤ) - 1 ∣ 2 * ((N : ℤ) - 1) := dvd_mul_left _ _
      have h3 : ((N : ℤ) - 1) * (P : ℤ) - 2 * ((N : ℤ) - 1) = 2 := by linarith
      exact h3 ▸ dvd_sub h1 h2
    have hle : (N : ℤ) - 1 ≤ 2 := Int.le_of_dvd (by omega) hdvd_2
    omega
  · have hR1 : R = 1 := by omega
    subst hR1
    have hPN : P * (N - 1) = N - 1 := by omega
    constructor
    · exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < N - 1) (by rw [one_mul]; exact hPN)
    · rfl

theorem f1_prime_free {N : ℕ} (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 < N)
    {α a b c : ℝ} (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1shape : F1Shape D α) : False := by
  rcases f1_data_of_f1shape D hm hF1shape with ⟨μ, hμ, hF1⟩ | ⟨μ, hμ, hF1'⟩
  · obtain ⟨σ, hside_eq, hQzero⟩ := f1_V1V2_b_zero D hirr hm hF1 hμ hN
    have hword := f1_word_from_bzero D hirr hm hF1 hμ hN h3 σ hside_eq
    obtain ⟨i', X, hγ, j₂, hj_ne, hX1, hX2⟩ :=
      f1_Tprime_K2_proved D hirr hm hF1 hμ hN σ hside_eq hQzero hword
    exact f1_k2_contradiction D hirr hm hF1 i' X hγ (σ 2 + 1) j₂ hj_ne.symm hX1 hX2
  · have hirr' : IrrPi (Real.pi / 3 - α) := by
      intro ⟨q, hq⟩; apply hirr; exact ⟨1/3 - q, by push_cast; linarith⟩
    have hm' : D.model.TwoPiThreeData (Real.pi / 3 - α) b a c :=
      Erdos634.Geometry.twoPiThreeData_swap D.model hm
    obtain ⟨σ, hside_eq, hQzero⟩ := f1_V1V2_b_zero D hirr' hm' hF1' hμ hN
    have hword := f1_word_from_bzero D hirr' hm' hF1' hμ hN h3 σ hside_eq
    obtain ⟨i', X, hγ, j₂, hj_ne, hX1, hX2⟩ :=
      f1_Tprime_K2_proved D hirr' hm' hF1' hμ hN σ hside_eq hQzero hword
    exact f1_k2_contradiction D hirr' hm' hF1' i' X hγ (σ 2 + 1) j₂ hj_ne.symm hX1 hX2

/-! ## F2..F4': `R8F2to4Bridge.r8_reduction_statement` without `N % 4 = 3` -/

open Erdos634.Draft.R8F2to4Bridge in
theorem r8_prime_free {N : ℕ} (D : CongruentDissection N) (hprime : N.Prime) (hN3 : 3 < N)
    {α a b c : ℝ} (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hshape : F2to4Shape D α) : False := by
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4 | hF4'
  · obtain ⟨ν, hνpos, hF2data⟩ := f2_data_of_shape D hm hF2
    exact R8F2Contradiction.f2_prime_contradiction D hirr hm hF2data ha0 hb0 hνpos hprime hN3
  · obtain ⟨ν, hνpos, hF3data⟩ := f3_data_of_shape D hm hF3
    exact R8F3Contradiction.f3_prime_contradiction D hirr hm hF3data ha0 hb0 hνpos hprime hN3
  · obtain ⟨ν, hνpos, hF3pdata⟩ := f3prime_data_of_shape D hm hF3'
    exact R8F3PrimeContradiction.f3prime_contradiction D hirr hm hF3pdata ha0 hb0 hνpos hprime hN3
  · obtain ⟨ν, hνpos, hF4data⟩ := f4_data_of_shape D hm hF4
    exact R8F4Contradiction.f4_prime_contradiction D hirr hm hF4data ha0 hb0 hνpos hprime (by linarith)
  · obtain ⟨ν, hνpos, hF4pdata⟩ := f4prime_data_of_shape D hm hF4'
    exact R8F4PrimeContradiction.f4prime_prime_contradiction D hirr hm hF4pdata ha0 hb0 hνpos hprime (by linarith)

/-! ## F2..F4': any prime ≠ 2 (including N = 3) -/

open Erdos634.Draft.R8F2to4Bridge in
theorem r8_prime_free_any {N : ℕ} (D : CongruentDissection N) (hprime : N.Prime) (hN2 : N ≠ 2)
    {α a b c : ℝ} (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hshape : F2to4Shape D α) : False := by
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4 | hF4'
  · obtain ⟨ν, hνpos, hF2data⟩ := f2_data_of_shape D hm hF2
    exact R8F2Contradiction.f2_any_prime_contradiction D hirr hm hF2data ha0 hb0 hνpos hprime hN2
  · obtain ⟨ν, hνpos, hF3data⟩ := f3_data_of_shape D hm hF3
    exact R8F3Contradiction.f3_any_prime_contradiction D hirr hm hF3data ha0 hb0 hνpos hprime hN2
  · obtain ⟨ν, hνpos, hF3pdata⟩ := f3prime_data_of_shape D hm hF3'
    exact R8F3PrimeContradiction.f3prime_any_prime_contradiction D hirr hm hF3pdata ha0 hb0 hνpos hprime hN2
  · obtain ⟨ν, hνpos, hF4data⟩ := f4_data_of_shape D hm hF4
    exact R8F4Contradiction.f4_any_prime_contradiction D hirr hm hF4data ha0 hb0 hνpos hprime hN2
  · obtain ⟨ν, hνpos, hF4pdata⟩ := f4prime_data_of_shape D hm hF4'
    exact R8F4PrimeContradiction.f4prime_prime_contradiction D hirr hm hF4pdata ha0 hb0 hνpos hprime (by
      have := hprime.two_le; omega)

/-! ## The classification dispatch -/

theorem tp_prime_excluded {N : ℕ} (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 < N)
    {α a b c : ℝ} (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hns : ¬ SimilarTM D) : False := by
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    obtain ⟨σ, h0, -⟩ := hm
    exact ⟨σ 0, by rw [h0]; exact hα⟩
  rcases lemmaC_general D hirr hns with h | h | h | h | h
  · exact not_right D hα hm h
  · exact not_twoAlpha D hα hm h
  · exact not_sixty D hα hm h
  · obtain ⟨α', a', b', c', hα', hm', hc⟩ := h
    rcases hc with h | h | h | h
    · exact Erdos634.Geometry.Row5TwoPiThreeFull.Row5.theoremE_twoPiThree_full D hα' hm' h ⟨hN, h3⟩
    · exact Erdos634.Draft.ISUCore.thmIsoCore N D hN α' a' b' c' hα' hm' h
    · exact f1_prime_free D hN h3 hα' hm' h
    · exact r8_prime_free D hN h3 hα' hm' h
  · exact not_threeTwo D hα hm h

/-- `N % 4 = 3`: the tile-similar target is excluded as well (`Row2.theoremS_perm`). -/
theorem tp_prime_excluded_mod3 {N : ℕ} (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 < N)
    (h4 : N % 4 = 3) {α a b c : ℝ} (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) : False := by
  by_cases hs : SimilarTM D
  · obtain ⟨μ, τ, h⟩ := hs
    rcases Row2.theoremS_perm D μ τ h hN with h' | h'
    · exact h' h4
    · omega
  · exact tp_prime_excluded D hN h3 hα hm hs

/-- **`prop:reduction`, tiling level, no integrality of the tile.**  Paper hypotheses (tile
`(alpha, beta, 2pi/3)`, `alpha/pi` irrational, `N` prime) plus `N > 3` and the target not similar to the tile
(the tile-similar target is the paper's `N = n^2` citation; in Lean only for `N % 4 = 3`).
Conclusion: the paper's `ABC isosceles and not equilateral` (here obtained because the hypotheses are inconsistent). -/
theorem reduction_tiling_final {N : ℕ} (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 < N)
    {α a b c : ℝ} (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) (hns : ¬ SimilarTM D) :
    (∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) ∧
      ¬ (∀ i, D.target.angleAt i = Real.pi / 3) :=
  (tp_prime_excluded D hN h3 hα hm hns).elim

/-! ## Witnesses and a composite control.
Every hypothesis of `tp_prime_excluded` except `N.Prime` is satisfied by the REAL certified 2673-tile tiling
(`G3CIsoControl.D`: tile `1890 (3,5,7)`, isosceles target), and `2673` is not prime. -/

open Erdos634.Draft.G3CIsoControl in
theorem control_hypotheses_minus_prime :
    ∃ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), 3 < N ∧ ¬ N.Prime ∧ IrrPi α ∧
      D.model.TwoPiThreeData α a b c ∧ ¬ SimilarTM D := by
  refine ⟨_, D, α, 1890 * 3, 1890 * 5, 1890 * 7, ?_, ?_, α_irr, data, ?_⟩
  · rw [Erdos634.Draft.G3CIso2673.cert_len]; norm_num
  · rw [Erdos634.Draft.G3CIso2673.cert_len]; exact Erdos634.Draft.ISUMain.control_N_not_prime
  obtain ⟨-, -, ⟨i, j, hij, h⟩, -⟩ := Erdos634.Draft.ISUMain.control_hypotheses
  exact not_similar D α_irr data
    ⟨i, j, hij, Erdos634.Draft.ISUMain.angleAt_eq_of_oppLen_eq _ i j hij h⟩

end Erdos634.Draft.G1NFinal

#print axioms Erdos634.Draft.G1NFinal.f1_prime_free
#print axioms Erdos634.Draft.G1NFinal.r8_prime_free
#print axioms Erdos634.Draft.G1NFinal.tp_prime_excluded
#print axioms Erdos634.Draft.G1NFinal.tp_prime_excluded_mod3
#print axioms Erdos634.Draft.G1NFinal.reduction_tiling_final
#print axioms Erdos634.Draft.G1NFinal.control_hypotheses_minus_prime
