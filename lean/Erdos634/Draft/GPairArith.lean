/-
Draft/GPairArith.lean -- the arithmetic kill of the `γ = 2α` leaf, PAIR BY PAIR.

`NSQLegs.Row4.not_gammaArith` needs `Coprime ((M' − M)/2) N` for every admissible pair `(M, M')` of `N`, but uses it only
for the pair of the dissection at hand (`Row4.P5`).  Here the two theorems are restated with the hypothesis restricted
to that pair (text of `NSQLegs.lean`, one hypothesis changed), which gives

* `gPair_of_coprime`: `GPair N M M'` whenever `Coprime ((M' − M)/2) N`;
* with `GPairCert.caseG_of_pairs`, `gPair_of_leafG`, `gPair_of_cert`: the `γ = 2α` leaf of an `N` whose pairs are closed by
  different arguments (e.g. `N = 171`: `(1,171)` by coprimality, `(3,57)` by a certificate).

Composite-N leaf work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQLegs
import Erdos634.Draft.GPairCert

open scoped Classical

namespace Erdos634.Draft.GPairArith

open Erdos634.Geometry Erdos634.Draft.ChainComposite Erdos634.Draft.NSQLegs Erdos634.Draft.GPairCert
open Erdos634.Draft.TheoremPConditional

/-- `Row4.nsq_legs` with the coprimality hypothesis asked only of the pair `(M, M')` of the dissection itself. -/
theorem nsq_legs_pair {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α)
    (hG : ∀ M M' : ℕ, 0 < M → M * M' = N → 3 * M < M' → M % 2 = N % 2 → M' % 2 = N % 2 →
      (M : ℝ) * (a + c) = D.target.oppLen 0 → Nat.Coprime ((M' - M) / 2) N) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ p q r : ℕ, D.target.oppLen 0 = p * a + q * b + r * c →
      (q = k ∧ p = 0 ∧ r = 0) ∨ q = 0 := by
  obtain ⟨κ, -, -, ha, -, -, -, -, hX1⟩ := Row4.sides D h hA hC
  obtain ⟨M, M', hM0, hM'0, hM, hM', hNM, hM2, hM'2, hlt, -, -, hab⟩ := Row4.P5 D hα h hA hC
  lift M to ℕ using hM0.le
  lift M' to ℕ using hM'0.le
  have hNn : N = M * M' := by exact_mod_cast hNM
  push_cast at hM hM'
  have hMpos : 0 < M := by exact_mod_cast hM0
  have hlt' : 3 * M < M' := by exact_mod_cast hlt
  have hMp : M % 2 = N % 2 := by
    have : (2 : ℤ) ∣ (M : ℤ) - N := hM2
    omega
  have hM'p : M' % 2 = N % 2 := by
    have : (2 : ℤ) ∣ (M' : ℤ) - N := hM'2
    omega
  obtain ⟨k, hk⟩ : ∃ k, M' = M + 2 * k := ⟨(M' - M) / 2, by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hcopk : Nat.Coprime k (M * M') := by
    have := hG M M' hMpos hNn.symm hlt' hMp hM'p hM
    have hkdef : (M' - M) / 2 = k := by omega
    rw [hkdef] at this
    rwa [← hNn]
  refine ⟨k, hk2, fun p q r hw => ?_⟩
  set X := D.target.oppLen 0 with hXdef
  have hkR : (M' : ℝ) = M + 2 * k := by exact_mod_cast hk
  have hNR : (N : ℝ) = M * M' := by exact_mod_cast hNn
  have hkc : (k : ℝ) * c = (M + k) * a := by
    have : 2 * ((k : ℝ) * c - (M + k) * a) = 0 := by
      linear_combination hM' - hM - (c - a) * hkR
    linarith
  have hkb : (k : ℝ) ^ 2 * b = N * a := by
    have e : a * ((k : ℝ) ^ 2 * b - N * a) = 0 := by
      rw [hNR, hkR]
      linear_combination (k : ℝ) ^ 2 * hab + ((k : ℝ) * c + (M + k) * a) * hkc
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
  have hkX : (k : ℝ) * X = N * a := by
    rw [hNR, hkR]
    linear_combination (k : ℝ) * (-hM) + (M : ℝ) * hkc
  have hword : (M * M') * k = p * k ^ 2 + q * (M * M') + r * k * (M + k) := by
    have e : a * (((N : ℝ)) * k - (p * (k : ℝ) ^ 2 + q * N + r * k * (M + k))) = 0 := by
      linear_combination (-(k : ℝ)) * hkX + (k : ℝ) ^ 2 * hw + (q : ℝ) * hkb + (r : ℝ) * k * hkc
    have e2 := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
    rw [hNR] at e2
    exact_mod_cast e2
  have := leg_words_cop M M' k (M + k) hMpos hcopk hlt' (by omega) (by omega) p q r hword
  rcases this with h1 | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

/-- `Row4.not_gammaArith` with the coprimality hypothesis asked only of the pair of the dissection itself. -/
theorem not_gammaArith_pair {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α)
    (hG : ∀ M M' : ℕ, 0 < M → M * M' = N → 3 * M < M' → M % 2 = N % 2 → M' % 2 = N % 2 →
      (M : ℝ) * (a + c) = D.target.oppLen 0 → Nat.Coprime ((M' - M) / 2) N) : False := by
  obtain ⟨k, hk2, hwords⟩ := nsq_legs_pair D hα h hA hC hG
  obtain ⟨-, -, -, -, -, -, -, -, hX1⟩ := Row4.sides D h hA hC
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hB : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; rw [hA, hC] at this; linarith
  obtain ⟨hBγ, -⟩ := Row4.corner_B D hα h hα0 hα3 hB
  have hne : ∀ i j : Fin 3, i ≠ j → D.target.pts i ≠ D.target.pts j := fun i j hij e =>
    hij (D.target.indep.injective e)
  have hw : ∀ i : Fin 3, (i = 0 ∨ i = 1) →
      (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = a)).card = 0 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = k ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = c)).card = 0) ∨
      ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = 0 := by
    intro i hi
    have := hwords _ _ _ (by
      rw [← Row4.side_word_counts D hα h i]
      rcases hi with rfl | rfl
      · rfl
      · exact hX1.symm)
    rcases this with ⟨h1, h2, h3⟩ | h1
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr h1
  have hbk : ∀ j : Fin 3,
      ((D.sideEdges j).filter (fun e => D.eLen e = a)).card = 0 →
      ((D.sideEdges j).filter (fun e => D.eLen e = c)).card = 0 →
      ∀ e ∈ D.sideEdges j, D.eLen e = b := by
    intro j h1 h3 e he
    rcases Row4.eLen_abc D h e with e1 | e1 | e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h1] at this; simp at this
    · exact e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h3] at this; simp at this
  have hnob : ∀ j : Fin 3, ((D.sideEdges j).filter (fun e => D.eLen e = b)).card = 0 →
      ∀ e ∈ D.sideEdges j, D.eLen e ≠ b := by
    intro j hj e he heq
    have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = b) := Finset.mem_filter.mpr ⟨he, heq⟩
    rw [Finset.card_eq_zero.mp hj] at this; simp at this
  rcases hw 0 (Or.inl rfl) with ⟨h1, h2, h3⟩ | h0
  · refine Row4.bk_leg D hα h (hne 1 2 (by decide)) rfl rfl ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hC i).2) hBγ hk2 h2 (hbk 1 h1 h3)
    intro v hv
    have h3' : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3' with rfl | rfl | rfl
    · exact absurd hv (Row4.third_not_on_side D.target 1)
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hw 1 (Or.inr rfl) with ⟨h1', h2', h3'⟩ | h1
  · have hsAB : D.target.edge 2 = segment ℝ (D.target.pts 0) (D.target.pts 2) := by
      show segment ℝ (D.target.pts 2) (D.target.pts (2 + 1)) = _
      rw [show (2 : Fin 3) + 1 = 0 from rfl, segment_symm]
    refine Row4.bk_leg D hα h (hne 0 2 (by decide)) hsAB (by rw [dist_comm]; rfl) ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hA i).2) hBγ hk2 h2' (hbk 2 h1' h3')
    intro v hv
    have h3'' : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3'' with rfl | rfl | rfl
    · exact Or.inl rfl
    · rw [segment_symm] at hv
      exact absurd hv (Row4.third_not_on_side D.target 2)
    · exact Or.inr rfl
  · exact Row4.L8_nob D hα h hA hC (hnob 2 h1) (hnob 1 h0)

/-- **A coprime pair is dead.** -/
theorem gPair_of_coprime (N : ℕ) (M M' : ℕ) (hM : 0 < M) (hN : M * M' = N)
    (hcop : Nat.Coprime ((M' - M) / 2) N) : GPair N (M : ℤ) (M' : ℤ) := by
  intro D α a b c hα h hA hB hX1 hX2
  obtain ⟨κ, -, -, ha, hXpos, hcκ, -, -, -⟩ := Row4.sides D h hA hB
  have hac : 0 < a + c := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have : (0 : ℝ) < (M : ℝ) * (a + c) := by
      have e : ((M : ℤ) : ℝ) * (a + c) = D.target.oppLen 0 := hX1
      push_cast at e
      rw [e]; exact hXpos
    exact (mul_pos_iff_of_pos_left hM0).mp this
  refine not_gammaArith_pair D hα h hA hB ?_
  intro M1 M1' hM1 hN1 _ _ _ hX
  have e : ((M : ℤ) : ℝ) * (a + c) = D.target.oppLen 0 := hX1
  push_cast at e
  have hMM : (M1 : ℝ) = M := by
    have : ((M1 : ℝ) - M) * (a + c) = 0 := by linear_combination hX - e
    have := (mul_eq_zero.mp this).resolve_right hac.ne'
    linarith
  have hMeq : M1 = M := by exact_mod_cast hMM
  subst hMeq
  have hM'eq : M1' = M' := by
    have : M1 * M1' = M1 * M' := by rw [hN1, hN]
    exact Nat.eq_of_mul_eq_mul_left hM1 this
  subst hM'eq
  exact hcop

end Erdos634.Draft.GPairArith

#print axioms Erdos634.Draft.GPairArith.gPair_of_coprime
