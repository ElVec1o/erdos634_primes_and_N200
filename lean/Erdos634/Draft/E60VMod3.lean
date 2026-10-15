/-
Draft/E60VMod3.lean: the π/3 equilateral pair `(m₁, m₂)` with non-square `D` forces `3 ∣ m₁` (uniform in the pair).  No sorry, no native_decide.

Mathematics (infrastructure: `E60Mod9A/B/C`, `Dissection.flux_cancel`, `Row5.theoremE_sixty`):
  * Take the odd weight `gV (j, k) = [j = 0] - [j = 3]` (it depends on the direction class mod π/3 only).
    Its boundary value on an equilateral target is `gV(0)+gV(2)+gV(4) = 1`.
  * For every tile type `(t, o, x)` (216 of them, `decide +kernel`), the integer coefficients of the `b`- and `c`-edges
    cancel: `coef gV t pos 1 + coef gV t pos 2 = 0`.  Geometrically: the edge directions of the `b`- and `c`-sides differ by
    π plus a multiple of α, so any weight that ignores the α-level is opposite on them.
  * `flux_cancel` gives `P a + Q b + R c = S` with integers `P, Q, R = -Q`.  With `D = (m₁+m₂)² - 16 N` non-square the
    irrational part forces `P = Q`, and then `P (a + b - c) = S`, i.e. `3 P = m₁` (since `m₁ (a+b-c) = 3 S`).
  Hence `¬ 3 ∣ m₁` kills the pair: `e60Pair_of_not_three_dvd`.  At N = 87, (29, 9) this recovers `E60Mod9C.e60Pair_87`.
  The same argument with the weight `gV · (-1)^k` gives `m₁ ∣ N` (no new information for x-type pairs).
-/
import Erdos634.Draft.E60Mod9C

open scoped Classical

namespace Erdos634.Draft.E60V

open Erdos634.Geometry Erdos634.Geometry.Row5Hr0 Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.E60Mod9 Erdos634.Draft.CompositeE5Gen

/-- The single-direction-class odd weight. -/
def gV (x : GZ) : ℤ := if x.1 = 0 then 1 else if x.1 = 3 then -1 else 0

theorem gV_odd : ∀ y : GZ, gV (y + (3, 0)) = - gV y := by decide

theorem gV_boundary : gV (0, 0) + gV (2, 0) + gV (4, 0) = 1 := by decide

/-- **The finite check.**  For every tile type, the `b`- and `c`-coefficients of `gV` cancel. -/
theorem coef_bc : ∀ t : Fin 3 → Fin 3, Function.Injective t → ∀ (o : Bool) (x : GZ),
    coef gV t (pk o t x) 1 + coef gV t (pk o t x) 2 = 0 := by
  decide +kernel

/-- **The irrational split with a `b`/`c`-cancelling weight.**  An integer identity `P a + Q b + R c = S w` with
`R = -Q` forces `P = Q` and `3 P = m₁ w`, when `D = (m₁+m₂)² - 16 N` is not a square. -/
theorem splitV {N : ℕ} {a b c S : ℝ} (m₁ m₂ : ℤ) (hN : 0 < N)
    (h1 : (m₁ : ℝ) * (a + b - c) = 3 * S) (h2 : (m₂ : ℝ) * (a + b + c) = 3 * S)
    (harea : S ^ 2 = N * a * b) (hprod : m₁ * m₂ = 3 * (N : ℤ)) (hS0 : 0 < S)
    (hD : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)))
    (P Q R w : ℤ) (hR : R = -Q) (h : (P : ℝ) * a + Q * b + R * c = S * w) :
    P = Q ∧ 3 * P = m₁ * w := by
  have hprodR : (m₁ : ℝ) * m₂ = 3 * N := by exact_mod_cast hprod
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : 2 * (N : ℝ) * (a + b) = S * (m₁ + m₂) := by
    have : 3 * ((2 * (N : ℝ) * (a + b)) - S * (m₁ + m₂)) = 0 := by
      linear_combination (m₂ : ℝ) * h1 + (m₁ : ℝ) * h2 - 2 * (a + b) * hprodR
    linarith
  have e2 : 2 * (N : ℝ) * c = S * (m₁ - m₂) := by
    have : 3 * ((2 * (N : ℝ) * c) - S * (m₁ - m₂)) = 0 := by
      linear_combination (m₁ : ℝ) * h2 - (m₂ : ℝ) * h1 - 2 * c * hprodR
    linarith
  have hX : (2 * (N : ℝ) * (a - b)) ^ 2 = S ^ 2 * (((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ) : ℝ) := by
    push_cast
    linear_combination ((2 * (N : ℝ) * (a + b) + S * (m₁ + m₂))) * e1 + 16 * (N : ℝ) * harea
  have hK : ((P : ℝ) - Q) * (2 * (N : ℝ) * (a - b)) =
      S * (((4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ)) : ℝ) := by
    push_cast
    linear_combination (4 * (N : ℝ)) * h - ((P : ℝ) + Q) * e1 - 2 * (R : ℝ) * e2
  have hnn : 0 ≤ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) := by
    by_contra hneg
    have hnegR : ((((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ)) : ℝ) < 0 := by
      exact_mod_cast not_le.mp hneg
    have : S ^ 2 * ((((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ)) : ℝ) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hnegR
    nlinarith [sq_nonneg (2 * (N : ℝ) * (a - b))]
  have hPQ : P = Q := by
    by_contra hpq
    apply hD
    have hpq' : P - Q ≠ 0 := sub_ne_zero.mpr hpq
    have hL : ((P - Q : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hpq'
    refine isSquare_of_rat_sq _ (4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂)) (P - Q) hpq' ?_
    have hS2 : S ^ 2 ≠ 0 := by positivity
    have hX' : 2 * (N : ℝ) * (a - b) =
        S * ((((4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ)) : ℝ) / ((P - Q : ℤ) : ℝ)) := by
      push_cast at hL hK ⊢
      field_simp
      linear_combination hK
    rw [hX'] at hX
    have : S ^ 2 * (((((4 * (N : ℤ) * w - (P + Q) * (m₁ + m₂) - 2 * R * (m₁ - m₂) : ℤ)) : ℝ) /
          ((P - Q : ℤ) : ℝ))) ^ 2 = S ^ 2 * (((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ) : ℝ) := by
      rw [← hX]; ring
    exact mul_left_cancel₀ hS2 this
  refine ⟨hPQ, ?_⟩
  subst hPQ
  subst hR
  have h4 : S * ((4 * (N : ℤ) * w - (P + P) * (m₁ + m₂) - 2 * (-P) * (m₁ - m₂) : ℤ) : ℝ) = 0 := by
    rw [← hK]; ring
  rcases mul_eq_zero.mp h4 with h0 | h0
  · exact absurd h0 hS0.ne'
  · have hz : (4 * (N : ℤ) * w - (P + P) * (m₁ + m₂) - 2 * (-P) * (m₁ - m₂) : ℤ) = 0 := by
      exact_mod_cast h0
    have hm2 : m₂ ≠ 0 := by
      intro h0'
      rw [h0', mul_zero] at hprod
      have : (0 : ℤ) < 3 * (N : ℤ) := by positivity
      omega
    have hz4 : 4 * (m₂ * (m₁ * w - 3 * P)) = 0 := by
      linear_combination (3 : ℤ) * hz + (4 * w) * hprod
    have hz2 : m₂ * (m₁ * w - 3 * P) = 0 := by linarith
    rcases mul_eq_zero.mp hz2 with h5 | h5
    · exact absurd h5 hm2
    · linarith

/-- **`E60Pair N m₁ m₂` for every pair with `3 ∤ m₁` and non-square `D`.**  () -/
theorem e60Pair_of_not_three_dvd (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℤ) (hprod : m₁ * m₂ = 3 * (N : ℤ))
    (hD : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ))) (h3 : ¬ (3 : ℤ) ∣ m₁) : E60Pair N m₁ m₂ := by
  intro D α a b c hα h hE hS1 hS2
  have hP : ∀ k, D.target.angleAt k = Real.pi / 3 := hE
  set anc := (D.target.leftUnit 0).angle with hanc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, harea, -⟩ := Row5.theoremE_sixty D hα h hP
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hmem : ∀ i k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L :=
    fun i => Row5Hr0.tile_angles_mem D hα h i
  have hdata : ∀ i, ∃ t : Fin 3 → Fin 3, Function.Injective t ∧ ∃ (o : Bool) (x : GZ), ∀ g : GZ → ℤ,
      (D.tile i).flux (fW α hα anc g) =
        a * (coef g t (pk o t x) 0 : ℝ) + b * (coef g t (pk o t x) 1 : ℝ)
          + c * (coef g t (pk o t x) 2 : ℝ) := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    have hS : (D.tile i).SixtyData α a b c := by
      obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
      refine ⟨σ.symm * τ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Equiv.Perm.mul_apply, (hσ _).1, (hσ _).2, Equiv.apply_symm_apply] <;> assumption
    exact tile_flux_coef α hα anc (D.tile i) hS (hmem i)
  choose t ht o x hflux using hdata
  have hcancel : ∀ g : GZ → ℤ, (∀ y, g (y + (3, 0)) = - g y) →
      ∑ i, (D.tile i).flux (fW α hα anc g) = D.target.flux (fW α hα anc g) :=
    fun g hg => D.flux_cancel (fW α hα anc g) (fW_odd α hα anc g hg)
  have hI : ((∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 0 : ℤ) : ℝ) * a
        + ((∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 1 : ℤ) : ℝ) * b
        + ((∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 2 : ℤ) : ℝ) * c
        = D.target.oppLen 0 * ((gV (0, 0) + gV (2, 0) + gV (4, 0) : ℤ) : ℝ) := by
    have := hcancel gV gV_odd
    rw [target_flux_W D hα h hP gV] at this
    rw [← this, Finset.sum_congr rfl fun i _ => hflux i gV]
    push_cast
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hR : (∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 2 : ℤ) =
      - (∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 1 : ℤ) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => coef_bc (t i) (ht i) (o i) (x i)
  have hS1' : (m₁ : ℝ) * (a + b - c) = 3 * D.target.oppLen 0 := hS1
  have hS2' : (m₂ : ℝ) * (a + b + c) = 3 * D.target.oppLen 0 := hS2
  obtain ⟨-, h3P⟩ := splitV (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) m₁ m₂ hN hS1' hS2'
    (by exact_mod_cast harea) hprod hS0 hD
    (∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 0) (∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 1)
    (∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 2) (gV (0, 0) + gV (2, 0) + gV (4, 0)) hR hI
  rw [gV_boundary] at h3P
  exact h3 ⟨∑ i, coef gV (t i) (pk (o i) (t i) (x i)) 0, by linarith⟩

/-- **`GapE60 N` from the pair table, with the mod-3 kill.**  As `gapE60_of_pairs`, but a pair with non-square `D`
and `3 ∤ m₁` is also admitted (killed by `e60Pair_of_not_three_dvd`). -/
theorem gapE60_of_pairs_mod3 (N : ℕ) (hN : 11 ≤ N)
    (hpairs : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ N → 1 ≤ m₂ → m₂ ≤ N → m₁ * m₂ = 3 * (N : ℤ) → m₂ < m₁ →
      (m₁ = N ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧ ¬ (3 : ℤ) ∣ m₁) ∨
        (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧
        (0 ≤ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) →
          ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (N : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂)))) : GapE60 N := by
  intro D α a b c hα h hE
  obtain ⟨m₁, m₂, -, -, hm1, hm1N, hm2, hm2N, hS1, hS2, harea, hprod, hlt, -⟩ := Row5.theoremE_sixty D hα h hE
  rcases hpairs m₁ m₂ hm1 hm1N hm2 hm2N hprod hlt with ⟨e1, e2⟩ | ⟨hD, h3⟩ | ⟨hD, hno⟩
  · subst e1; subst e2
    exact sixty_pinned_false D hα h hE hN (by exact_mod_cast hS1) (by exact_mod_cast hS2) harea
  · exact e60Pair_of_not_three_dvd N (by omega) m₁ m₂ hprod hD h3 D α a b c hα h hE hS1 hS2
  · obtain ⟨p, q, r, hpqr⟩ := sixty_side_decomposition D h
    obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
      (fun k => D.model.sixty_angles_mem hα h 0 _ k) hE
    have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
      rw [← e2]; unfold Tri.oppLen; rfl
    rw [hd] at hpqr
    exact sixty_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) m₁ m₂ (by omega)
      hS1 hS2 harea hprod (D.target.oppLen_pos 0) (p : ℤ) (q : ℤ) (r : ℤ)
      (by rw [hpqr]; push_cast; ring) hD (fun hnn => hno hnn (p : ℤ) (r : ℤ) (by positivity) (by positivity))

end Erdos634.Draft.E60V

#print axioms Erdos634.Draft.E60V.coef_bc
#print axioms Erdos634.Draft.E60V.splitV
#print axioms Erdos634.Draft.E60V.e60Pair_of_not_three_dvd
#print axioms Erdos634.Draft.E60V.gapE60_of_pairs_mod3
