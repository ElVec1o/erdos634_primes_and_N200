/-
Draft/NSQCaseB.lean -- Case B (target similar to the tile) WITHOUT `Squarefree N`.
`FluxERow2SqfreeEven` uses `Squarefree N` for (i) `¬ IsSquare N`, (ii) Lemma Q at `p = N`, (iii) `p ∣ m² → p ∣ m` inside
Lemma Q.  For `N = s₀² n` (`n` squarefree) the irrationality field is `ℚ(√N) = ℚ(√n)` and Lemma Q applies at `p = n`
(`lemmaQ_sqfree`, `n ≡ 3 mod 4`; `lemmaQ_sqfreeE`, `n ≥ 17` or `n ≡ 2 mod 4`).  Everything else (Lemma W/E-abstract/K/D/R,
`sideCount` algebra) is N-free given `¬ IsSquare N`.  Conclusion: `∃ x y, N = x² + y²` (= `HBSimilar N`).
Hypothesis `NQ N`: `N = s₀² n`, `n` squarefree, `7 ≤ n`, and `17 ≤ n` or `n ≡ 2, 3 (mod 4)`.
`NQ N` holds at N = 56 (n = 14), 76 (n = 19), 60 (n = 15); fails e.g. for N = 52 (n = 13), 20 (n = 5), 45 (n = 5).  No sorry, no native_decide.
-/
import Erdos634.Draft.FluxERow2SqfreeEven

open scoped Classical
open Real

namespace Erdos634.Geometry

variable {N : ℕ}

/-- The arithmetic hypothesis replacing `Squarefree N ∧ 7 ≤ N ∧ (17 ≤ N ∨ N ≡ 2 mod 4)`: `N = s² n`, `n` squarefree,
`7 ≤ n`, and `17 ≤ n` or `n ≡ 2, 3 (mod 4)` (the range of Lemma Q, `lemmaQ_sqfree` / `lemmaQ_sqfreeE`, at `p = n`). -/
def NQ (N : ℕ) : Prop :=
  ∃ s n : ℕ, 0 < s ∧ Squarefree n ∧ N = s ^ 2 * n ∧ 7 ≤ n ∧ (17 ≤ n ∨ n % 4 = 2 ∨ n % 4 = 3)

theorem notSq_of_NQ {N : ℕ} (h : NQ N) : ¬ IsSquare N := by
  obtain ⟨s, n, hs, hn, hNs, h7, -⟩ := h
  rintro ⟨m, hm⟩
  have h1 : s ^ 2 ∣ m ^ 2 := ⟨n, by rw [sq m, ← hm, hNs]⟩
  have h2 : s ∣ m := (Nat.pow_dvd_pow_iff (by norm_num)).mp h1
  obtain ⟨t, ht⟩ := h2
  have h3 : n = t * t := by
    have : s ^ 2 * n = s ^ 2 * (t * t) := by rw [← hNs, hm, ht]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  exact Row2.sqfree_not_square hn h7 ⟨t, h3⟩

/-- **Lemma Q (row 2), non-squarefree `N`.**  `s² = N = s₀² n`, `n` squarefree in the range of Lemma Q;
`θ ∈ (0, π)` a rational multiple of `π` with `cos θ ∈ ℚ + ℚ s` ⇒ `θ ∈ {π/3, π/2, 2π/3}`.  (`ℚ + ℚ s = ℚ + ℚ (s/s₀)`.) -/
theorem Row2.lemmaQ_nsq {N : ℕ} (hNQ : NQ N) {s : ℝ}
    (hs : s ^ 2 = N) {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * π) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hc : Row2.QMu s (Real.cos θ)) :
    θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3) := by
  obtain ⟨s0, n, hs0, hn, hNs, h7, hQ⟩ := hNQ
  have hs0R : (s0 : ℝ) ≠ 0 := by exact_mod_cast hs0.ne'
  set s' : ℝ := s / s0 with hs'
  have hss : s = s0 * s' := by rw [hs']; field_simp
  have hs'2 : s' ^ 2 = (n : ℝ) := by
    have h1 : (N : ℝ) = (s0 : ℝ) ^ 2 * n := by exact_mod_cast hNs
    have : (s0 : ℝ) ^ 2 * s' ^ 2 = (s0 : ℝ) ^ 2 * n := by
      rw [← h1, ← hs, hss]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hs0R) this
  have hc' : Row2.QMu s' (Real.cos θ) := by
    obtain ⟨q₁, q₂, h⟩ := hc
    refine ⟨q₁, q₂ * s0, ?_⟩
    rw [h, hss]; push_cast; ring
  rcases hQ with h17 | h2 | h3
  · exact Row2.lemmaQ_sqfreeE hn h7 (Or.inl h17) hs'2 hθ hθ0 hθπ hc'
  · exact Row2.lemmaQ_sqfreeE hn h7 (Or.inr h2) hs'2 hθ hθ0 hθπ hc'
  · exact Row2.lemmaQ_sqfree hn h3 h7 hs'2 hθ hθ0 hθπ hc'

/-- **Lemma E (row 2).**  A real `N`-tiling (`N` prime, `N ≡ 3 mod 4`, `N ≥ 7`) of a target
similar to the model with ratio `μ`, with `π ∈ 2Λ`, `Λ = ⟨θ₀, θ₁, π⟩`: no model angle is a natural
multiple of another (in particular the angles are distinct), and the model is scalene. -/
theorem Row2.lemmaE_nsq (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hNQ : NQ N)
    (hπ : ∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, π} : Set ℝ),
      π = 2 * y) :
    (∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i) ∧
      (∀ i j : Fin 3, i ≠ j → D.model.oppLen i ≠ D.model.oppLen j) := by
  have hsq : ¬ IsSquare N := notSq_of_NQ hNQ
  obtain ⟨hμ2, hknot, hcos⟩ := Row2.lemmaK_general D μ hside hsq
  have hsum := D.model.angleAt_sum
  have hQ : ∀ k, (∃ r : ℚ, D.model.angleAt k = r * π) →
      D.model.angleAt k = π / 3 ∨ D.model.angleAt k = π / 2 ∨ D.model.angleAt k = π * (2 / 3) := by
    intro k hr
    have hk0 := D.model.angleAt_pos' k
    have hkπ : D.model.angleAt k < π := by
      have h0 := D.model.angleAt_pos' 0
      have h1 := D.model.angleAt_pos' 1
      have h2 := D.model.angleAt_pos' 2
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by fin_cases k <;> simp) with rfl | rfl | rfl <;>
        linarith
    exact Row2.lemmaQ_nsq hNQ hμ2 hr hk0 hkπ (hcos k)
  have hneq : ¬ ∀ k, D.model.angleAt k = π / 3 := by
    intro hall
    have hsin : Real.sin (π / 3) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
    have hs : ∀ i j, D.model.oppLen i = D.model.oppLen j := by
      intro i j
      have h := D.model.lawSin i j
      rw [hall i, hall j] at h
      exact (mul_left_cancel₀ hsin h).symm
    exact hknot ⟨⟨1, by rw [hs 0 2]; simp⟩, ⟨1, by rw [hs 1 2]; simp⟩⟩
  have hE : ∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i :=
    fun i j hij k => Row2.lemmaE_abs D.model.angleAt hsum hQ hneq hπ hij k
  refine ⟨hE, fun i j hij hl => ?_⟩
  have := D.model.angle_eq_of_oppLen_eq hij hl
  exact hE i j hij 1 (by rw [this]; simp)


/-- **Theorem S, sorted core.**  A tile-similar `N`-tiling (same labels, ratio `μ`), `N` prime,
`N ≡ 3 (mod 4)`, with a scalene model whose angles satisfy `angleAt 0 < angleAt 1 < angleAt 2` and
`angleAt 1 ∉ ℕ·angleAt 0`, does not exist. -/
theorem Row2.theoremS_sorted_nsq (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hNQ : NQ N)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hmult : ∀ k : ℕ, D.model.angleAt 1 ≠ k * D.model.angleAt 0)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') : ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  have hsq : ¬ IsSquare N := notSq_of_NQ hNQ
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  have hang : ∀ k, D.target.angleAt k = D.model.angleAt k := fun k => (hsim k).1
  have hA := Row2.cornerA D hang h01 h12
  have hB := Row2.cornerB D hang h01 h12 hmult
  obtain ⟨-, -, -, -, h22, -⟩ := Row2.lemmaD_tiling D μ hside hscal hsq hA hB
  have hR := Row2.lemmaR D hang h01 h12 (Row2.noc_of_sideCount D h22)
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hsq
  obtain ⟨e0, e1, -⟩ := Row2.lemmaD_scale D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp
    (Row2.sideCount_eigen D μ hside hscal) (Row2.sideCount_rows D hscal) hA hB
  have hμ2 : μ ^ 2 = N := by rw [hp]; push_cast; ring
  -- Lemma R: `γ = π/2`, so Pythagoras
  have hcos : Real.cos (D.model.angleAt 2) = 0 := by
    rw [show D.model.angleAt 2 = π / 2 by linarith]; exact Real.cos_pi_div_two
  have hl := D.model.lawCos 2
  rw [hcos] at hl
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at hl
  have hc := D.model.oppLen_pos 2
  have hpy : D.model.oppLen 2 ^ 2 = D.model.oppLen 0 ^ 2 + D.model.oppLen 1 ^ 2 := by
    linarith [hl]
  -- `N c² = (μa)² + (μb)² = (A² + B²) c²`
  have key : (N : ℝ) * D.model.oppLen 2 ^ 2
      = (((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2)
        * D.model.oppLen 2 ^ 2 := by
    have h1 : (N : ℝ) * D.model.oppLen 2 ^ 2
        = (μ * D.model.oppLen 0) ^ 2 + (μ * D.model.oppLen 1) ^ 2 := by
      rw [← hμ2, hpy]; ring
    rw [h1, e0, e1]; ring
  have hN' : (N : ℝ) = ((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hc.ne') key
  have hNnat : N = D.sideCount 0 2 ^ 2 + D.sideCount 1 2 ^ 2 := by exact_mod_cast hN'
  exact ⟨_, _, hNnat⟩


/-- **Theorem S (row 2).**  Let `D` be a dissection of a triangle into `N` congruent copies of a
tile (reflections allowed, not necessarily edge-to-edge) whose target is similar to the tile with
ratio `μ` (same vertex labels: `target.angleAt k = model.angleAt k`,
`target.oppLen k = μ · model.oppLen k`).  If `N` is prime, then `N ≢ 3 (mod 4)` or `N = 3`. -/
theorem Row2.theoremS_nsq (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hNQ : NQ N) : ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  -- Lemma W: `π ∈ 2Λ`
  have hπ : ∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, π} : Set ℝ),
      π = 2 * y := by
    by_contra hc
    push Not at hc
    exact Row2.lemmaW_not_sq D μ hsim hc (notSq_of_NQ hNQ)
  -- Lemma E
  obtain ⟨hE, hscal⟩ := Row2.lemmaE_nsq D μ hside hNQ hπ
  have hdist : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j := fun i j hij h =>
    hE i j hij 1 (by rw [h]; simp)
  -- sort the angles
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (D.model.angleAt ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  have h01 : D.model.angleAt (σ 0) < D.model.angleAt (σ 1) :=
    lt_of_le_of_ne (hmono (show (0 : Fin 3) ≤ 1 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  have h12 : D.model.angleAt (σ 1) < D.model.angleAt (σ 2) :=
    lt_of_le_of_ne (hmono (show (1 : Fin 3) ≤ 2 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  -- relabel target and model by `σ`
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
      model := D.model.relabel σ
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σ }
  have hTa := Row2.angleAt_comp D.target D'.target σ (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σ (fun k => rfl)
  have hsim' : ∀ k, D'.target.angleAt k = D'.model.angleAt k ∧
      D'.target.oppLen k = μ * D'.model.oppLen k := by
    intro k
    rw [(hTa k).1, (hMa k).1, (hTa k).2, (hMa k).2]
    exact hsim (σ k)
  refine Row2.theoremS_sorted_nsq D' μ hsim' hNQ ?_ ?_ ?_ ?_
  · rw [(hMa 0).1, (hMa 1).1]; exact h01
  · rw [(hMa 1).1, (hMa 2).1]; exact h12
  · intro k
    rw [(hMa 1).1, (hMa 0).1]
    exact hE (σ 0) (σ 1) (σ.injective.ne (by decide)) k
  · intro k k' hkk'
    rw [(hMa k).2, (hMa k').2]
    exact hscal _ _ (σ.injective.ne hkk')


/-- **Theorem S, any vertex correspondence** `τ` between target and model. -/
theorem Row2.theoremS_perm_nsq (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3))
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
      D.target.oppLen k = μ * D.model.oppLen (τ k))
    (hNQ : NQ N) : ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  refine Row2.theoremS_nsq (D.relabelModel τ) μ (fun k => ?_) hNQ
  rw [(hMa k).1, (hMa k).2]
  exact hsim k


end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.lemmaQ_nsq
#print axioms Erdos634.Geometry.Row2.theoremS_perm_nsq
