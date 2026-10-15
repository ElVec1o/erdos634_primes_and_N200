/-
Draft/E60Irr.lean -- the irrational `π/3` pairs, for every `N`.

`E60Graph.sixty_has_a_relation` (`Draft/E60Count.lean`): a tile with an angle `π/3` and an irrational angle that
tiles an equilateral triangle satisfies `j a = p b + q c`.  Consequences:

* `sixty_has_b_relation`, `sixty_ratio_rational`: `a/b ∈ ℚ` (the first half of Laczkovich's Theorem 3.3,
  Discrete Comput. Geom. 48 (2012); the proof is the degree count of Beeson and Zhang, arXiv:2604.01314, Lemma 3.5
  and Lemma 3.6, transposed to the angle `π/3`).
* `e60Pair_of_not_isSquare`: for every `N` and every pair `(m₁, m₂)` of `Row5.theoremE_sixty` whose discriminant
  `(m₁ + m₂)² − 16N` is not a square, `E60Pair N m₁ m₂`: no dissection has that pair.  (The pair gives
  `(a + b)/c ∈ ℚ` and `ab = S²/N`; with `j a = p b + q c` both `a` and `b` are rational multiples of `S`, and the
  discriminant is a square.)  This replaces, for all `N` at once, the conjugate-kill certificates of the irrational
  pairs (`ReflS<K>/MP*`), which remain as independent kernel checks of single instances.
* `Pairs60ChkSq`, `gapE60_of_chk_sq`: `GapE60 N` from the pair table in which a pair is listed (to be certified),
  the pin, of the wrong parity, or has a non-square discriminant.
* `witness_relation`: non-vacuity.  The hypotheses of `sixty_has_a_relation` hold on a real dissection (the
  certified 1440-tiling of the equilateral triangle by the tile `(5, 8, 7)`, `G3CSixtyControl.D`), and its conclusion
  there is a true relation (`3·5 = 8 + 7`). not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.E60Count
import Erdos634.Draft.E60Parity

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.E60Irr

open Erdos634.Draft.AllNExclusion

/-- the pair table: a pair is listed, the pin `(N, 3)`, of the wrong parity, or has a non-square discriminant -/
def Pairs60ChkSq (N : ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ m ≤ N, 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N → 3 * N / m < m →
    L.contains (m, 3 * N / m) = true ∨ (m = N ∧ 3 * N / m = 3) ∨
    (m % 2 ≠ N % 2 ∨ (3 * N / m) % 2 ≠ N % 2) ∨
    (16 * N ≤ (m + 3 * N / m) ^ 2 → ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N))

instance (N : ℕ) (L : List (ℕ × ℕ)) : Decidable (Pairs60ChkSq N L) := by
  unfold Pairs60ChkSq sqChk; infer_instance

/-- counterexample to the empty table: at `N = 105` the two rational pairs `(45, 7)`, `(35, 9)` survive, so the table
with no listed pair is false -/
example : ¬ Pairs60ChkSq 105 [] := by decide +kernel

end Erdos634.Draft.E60Irr

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.AllNExclusion Erdos634.Draft.E60Graph Erdos634.Pi3Tile

namespace Erdos634.Draft.E60Irr

variable {N : ℕ}

/-- the two irrational angles of a `π/3` tile can be exchanged -/
theorem sixtyData_swap {T : Erdos634.Geometry.Tri} {α a b c : ℝ} (h : T.SixtyData α a b c) :
    T.SixtyData (2 * Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  refine ⟨(Equiv.swap (0 : Fin 3) 1).trans σ, ?_⟩
  have e0 : ((Equiv.swap (0 : Fin 3) 1).trans σ) 0 = σ 1 := by
    show σ (Equiv.swap (0 : Fin 3) 1 0) = σ 1
    rw [Equiv.swap_apply_left]
  have e1 : ((Equiv.swap (0 : Fin 3) 1).trans σ) 1 = σ 0 := by
    show σ (Equiv.swap (0 : Fin 3) 1 1) = σ 0
    rw [Equiv.swap_apply_right]
  have e2 : ((Equiv.swap (0 : Fin 3) 1).trans σ) 2 = σ 2 := by
    show σ (Equiv.swap (0 : Fin 3) 1 2) = σ 2
    rw [show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide]
  rw [e0, e1, e2]
  exact ⟨h1, o1, by rw [h0]; ring, o0, h2, o2⟩

theorem irr_swap {α : ℝ} (h : Irr α) : Irr (2 * Real.pi / 3 - α) := by
  rintro ⟨r, hr⟩
  exact h ⟨2 / 3 - r, by push_cast; linarith⟩

/-- the relation for the other side -/
theorem sixty_has_b_relation (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hE : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * b = p * a + q * c :=
  sixty_has_a_relation D (irr_swap hirr) (sixtyData_swap hS) hE

/-- **`a/b` is rational** for a tile with an angle `π/3` and an irrational angle that tiles an equilateral
triangle. -/
theorem sixty_ratio_rational (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hE : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ r : ℚ, a = (r : ℝ) * b := by
  obtain ⟨j, p, q, hj, h1⟩ := sixty_has_a_relation D hirr hS hE
  obtain ⟨J, P, Q, hJ, h2⟩ := sixty_has_b_relation D hirr hS hE
  have hS' := hS
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hS'
  have ha : 0 < a := by rw [← o0]; exact D.model.oppLen_pos _
  have hb : 0 < b := by rw [← o1]; exact D.model.oppLen_pos _
  have hc : 0 < c := by rw [← o2]; exact D.model.oppLen_pos _
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have key : ((j : ℝ) * Q + q * P) * a = ((J : ℝ) * q + p * Q) * b := by
    linear_combination (Q : ℝ) * h1 - (q : ℝ) * h2
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    refine ⟨(p : ℚ) / j, ?_⟩
    push_cast
    field_simp
    simp only [Nat.cast_zero, zero_mul, add_zero] at h1
    linarith
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hpos : (0 : ℝ) < (j : ℝ) * Q + q * P ∨ ((Q : ℝ) = 0 ∧ (P : ℝ) = 0) := by
      rcases Nat.eq_zero_or_pos Q with hQ | hQ
      · rcases Nat.eq_zero_or_pos P with hP | hP
        · right; exact ⟨by exact_mod_cast hQ, by exact_mod_cast hP⟩
        · left
          have : (0 : ℝ) < P := by exact_mod_cast hP
          have : (0 : ℝ) ≤ (j : ℝ) * Q := by positivity
          nlinarith
      · left
        have : (0 : ℝ) < Q := by exact_mod_cast hQ
        have : (0 : ℝ) ≤ (q : ℝ) * P := by positivity
        nlinarith
    rcases hpos with hpos | ⟨hQ0, hP0⟩
    · refine ⟨((J : ℚ) * q + p * Q) / ((j : ℚ) * Q + q * P), ?_⟩
      push_cast
      rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
      linarith
    · exfalso
      rw [hQ0, hP0] at h2
      nlinarith

/-- **Commensurable sides** (Laczkovich's Theorem 3.3 for the equilateral triangle and the angle `π/3`): a tile
with an angle `π/3` and an irrational angle that tiles an equilateral triangle has pairwise commensurable sides. -/
theorem sixty_commensurable (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hE : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ r s : ℚ, a = (r : ℝ) * b ∧ c = (s : ℝ) * b := by
  obtain ⟨r, hr⟩ := sixty_ratio_rational D hirr hS hE
  obtain ⟨m₁, m₂, -, -, hm1, -, hm2, -, hT1, hT2, -, -, -, -⟩ := Row5.theoremE_sixty D hirr hS hE
  refine ⟨r, (r + 1) * (((m₁ - m₂ : ℤ) : ℚ)) / (((m₁ + m₂ : ℤ) : ℚ)), hr, ?_⟩
  have h1 : c * ((m₁ : ℝ) + m₂) = (a + b) * ((m₁ : ℝ) - m₂) := by linear_combination hT2 - hT1
  have hpos : (0 : ℝ) < (m₁ : ℝ) + m₂ := by
    have e1 : (1 : ℝ) ≤ m₁ := by exact_mod_cast hm1
    have e2 : (1 : ℝ) ≤ m₂ := by exact_mod_cast hm2
    linarith
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  rw [hr] at h1
  linear_combination h1

/-- **Every irrational `π/3` pair is excluded, for every `N`.**  If the discriminant `(m₁ + m₂)² − 16N` of the
pair is not a square, no dissection has that pair. -/
theorem e60Pair_of_not_isSquare (N : ℕ) (m₁ m₂ : ℤ)
    (hD : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ))) : E60Pair N m₁ m₂ := by
  intro D α a b c hα hS hE hS1 hS2
  obtain ⟨n₁, n₂, -, -, -, -, -, -, hT1, hT2, harea, hprod, -, -⟩ := Row5.theoremE_sixty D hα hS hE
  have hSpos : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have e1 : m₁ = n₁ := by
    have hne : a + b - c ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hT1; linarith
    have : (m₁ : ℝ) = n₁ := mul_right_cancel₀ hne (hS1.trans hT1.symm)
    exact_mod_cast this
  have e2 : m₂ = n₂ := by
    have hne : a + b + c ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hT2; linarith
    have : (m₂ : ℝ) = n₂ := mul_right_cancel₀ hne (hS2.trans hT2.symm)
    exact_mod_cast this
  rw [← e1, ← e2] at hprod
  obtain ⟨j, p, q, hj, hrel⟩ := sixty_has_a_relation D hα hS hE
  apply hD
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = D.target.oppLen 0 := ⟨_, rfl⟩
  rw [← hSdef] at hS1 hS2 harea hSpos
  have hN : (0 : ℝ) < N := by exact_mod_cast D.toDissection.pos
  have hprodR : (m₁ : ℝ) * m₂ = 3 * N := by exact_mod_cast hprod
  have key1 : 2 * (N : ℝ) * (a + b) = S * ((m₁ : ℝ) + m₂) := by
    have h3 : (m₁ : ℝ) * m₂ * (2 * (a + b)) = 3 * S * (m₁ + m₂) := by
      linear_combination (m₂ : ℝ) * hS1 + (m₁ : ℝ) * hS2
    rw [hprodR] at h3; linarith
  have key2 : 2 * (N : ℝ) * c = S * ((m₁ : ℝ) - m₂) := by
    have h3 : (m₁ : ℝ) * m₂ * (2 * c) = 3 * S * (m₁ - m₂) := by
      linear_combination (m₁ : ℝ) * hS2 - (m₂ : ℝ) * hS1
    rw [hprodR] at h3; linarith
  -- `a` and `b` as rational multiples of `S`
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, J = (j : ℤ) + p := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = (p : ℤ) * (m₁ + m₂) + q * (m₁ - m₂) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = (m₁ + m₂) * J - A := ⟨_, rfl⟩
  have hJpos : 0 < J := by rw [hJ]; positivity
  have hJR : (J : ℝ) = (j : ℝ) + p := by rw [hJ]; push_cast; ring
  have hAR : (A : ℝ) = (p : ℝ) * (m₁ + m₂) + q * (m₁ - m₂) := by rw [hA]; push_cast; ring
  have hCR : (C : ℝ) = ((m₁ : ℝ) + m₂) * J - A := by rw [hC]; push_cast; ring
  have ha : a * (2 * N * J) = S * A := by
    rw [hJR, hAR]
    linear_combination (2 * (N : ℝ)) * hrel + (p : ℝ) * key1 + (q : ℝ) * key2
  have hb : b * (2 * N * J) = S * C := by
    rw [hCR]
    linear_combination (J : ℝ) * key1 - ha
  have h3 : (N : ℝ) * S ^ 2 * ((A : ℝ) * C) = (N : ℝ) * S ^ 2 * (4 * N * (J : ℝ) ^ 2) := by
    linear_combination (-(N : ℝ) * (b * (2 * N * J))) * ha + (-(N : ℝ) * (S * A)) * hb
      + (-(4 * (N : ℝ) ^ 2 * (J : ℝ) ^ 2)) * harea
  have hACR : (A : ℝ) * C = 4 * N * (J : ℝ) ^ 2 :=
    mul_left_cancel₀ (ne_of_gt (by positivity)) h3
  have hAC : A * C = 4 * N * J ^ 2 := by exact_mod_cast hACR
  have hsq : (A - C) ^ 2 = J ^ 2 * ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) := by
    linear_combination (-4 : ℤ) * hAC + (A + C + (m₁ + m₂) * J) * hC
  have hdvd : J ∣ A - C := (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp ⟨_, hsq⟩
  obtain ⟨K, hK⟩ := hdvd
  refine ⟨K, ?_⟩
  have hJ2 : J ^ 2 ≠ 0 := pow_ne_zero 2 hJpos.ne'
  apply mul_left_cancel₀ hJ2
  rw [← hsq, hK]; ring

/-- **`GapE60 N` from the pair table**: only the listed pairs (rational, of the right parity) need a proof. -/
theorem gapE60_of_chk_sq {N : ℕ} (hN : 11 ≤ N) (L : List (ℕ × ℕ)) (h : Pairs60ChkSq N L)
    (hL : ∀ p ∈ L, E60Pair N (p.1 : ℤ) (p.2 : ℤ)) : GapE60 N := by
  intro D α a b c hα hd hE
  obtain ⟨m₁, m₂, hp1, hp2, hm1, hm1N, hm2, hm2N, hS1, hS2, harea, hprod, hlt, -⟩ :=
    Row5.theoremE_sixty D hα hd hE
  lift m₁ to ℕ using (by omega)
  lift m₂ to ℕ using (by omega)
  have hp' : m₁ * m₂ = 3 * N := by exact_mod_cast hprod
  have h1 : 1 ≤ m₁ := by exact_mod_cast hm1
  have h1N : m₁ ≤ N := by exact_mod_cast hm1N
  have h2N : m₂ ≤ N := by exact_mod_cast hm2N
  have hlt' : m₂ < m₁ := by exact_mod_cast hlt
  have hdvd : m₁ ∣ 3 * N := ⟨m₂, hp'.symm⟩
  have hdiv : 3 * N / m₁ = m₂ := by rw [← hp']; exact Nat.mul_div_cancel_left _ h1
  have hall := h m₁ h1N h1 hdvd (by rw [hdiv]; exact h2N) (by rw [hdiv]; exact hlt')
  rw [hdiv] at hall
  rcases hall with hmem | ⟨e1, e2⟩ | hpar | hsq
  · exact hL (m₁, m₂) (List.contains_iff_mem.mp hmem) D α a b c hα hd hE hS1 hS2
  · subst e1; subst e2
    exact sixty_pinned_false D hα hd hE hN (by exact_mod_cast hS1) (by exact_mod_cast hS2) harea
  · exfalso
    rcases hpar with h | h <;> omega
  · refine e60Pair_of_not_isSquare N m₁ m₂ ?_ D α a b c hα hd hE hS1 hS2
    by_cases hle : 16 * N ≤ (m₁ + m₂) ^ 2
    · exact not_isSquare_of_chk ((m₁ + m₂) ^ 2 - 16 * N) _ (by rw [Nat.cast_sub hle]; push_cast; ring)
        (hsq hle)
    · rintro ⟨r, hr⟩
      have h0 : (0 : ℤ) ≤ r * r := mul_self_nonneg r
      have h16 : ((m₁ : ℤ) + m₂) ^ 2 < 16 * N := by exact_mod_cast (not_le.mp hle)
      linarith

/-- **Non-vacuity.**  On the certified 1440-tiling of the equilateral triangle by the tile `(5, 8, 7)`
(`G3CSixtyControl.D`) every hypothesis of `sixty_has_a_relation` holds; its conclusion there is a true relation
(for instance `3·5 = 1·8 + 1·7`). -/
theorem witness_relation :
    ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * (3360 * 5) = p * (3360 * 8) + q * (3360 * 7) :=
  sixty_has_a_relation Erdos634.Draft.G3CSixtyControl.D Erdos634.Draft.G3CSixtyControl.α_irr
    Erdos634.Draft.G3CSixtyControl.data Erdos634.Draft.G3CSixtyControl.t_angle

end Erdos634.Draft.E60Irr

#print axioms Erdos634.Draft.E60Irr.sixty_ratio_rational
#print axioms Erdos634.Draft.E60Irr.sixty_commensurable
#print axioms Erdos634.Draft.E60Irr.e60Pair_of_not_isSquare
#print axioms Erdos634.Draft.E60Irr.gapE60_of_chk_sq
#print axioms Erdos634.Draft.E60Irr.witness_relation
