/-
Draft/NSQLegs.lean — `γ = 2α` base-α target WITHOUT `Squarefree N`.

`G2AAssembly.Row4.sqfree_legs` uses `Squarefree N` for exactly one thing: `gcd(M, M') = 1` for `N = M M'`, which feeds
`leg_words_gen` through `gcd(k, M M') = 1` (`k = (M'−M)/2`).  The word equation `N k = p k² + q N + r k m` forces
`k ∣ q N`, hence `k ∣ q` (so `q ∈ {0, k}`) as soon as `Coprime k N`; coprimality of `M, M'` is not needed.
Here the squarefree hypothesis is replaced by the decidable arithmetic condition

    GammaArith N :  ∀ M M', M M' = N, 3M < M', M ≡ M' ≡ N (mod 2)  →  Coprime ((M'−M)/2) N.

* `gammaArith_of_squarefree`  : `Squarefree N → GammaArith N` (so this strictly generalises `Row4.not_squarefree`).
* `Row4.not_gammaArith`       : the analogue of `Row4.not_squarefree` under `GammaArith N`.
* `caseG_of_gammaArith`       : `GammaArith N → CaseGClosed N` (any-label form).
* decidable bounded form `GammaChk`, `gammaArith_of_chk`, `caseG_56`: see `NSQGammaChk.lean`.
Conditional at the geometric level exactly as `Row4.not_squarefree` (no Lean witness tiling of the base-α target).  No sorry, no native_decide.
-/
import Erdos634.Draft.G2AFinal
import Erdos634.Draft.CompositeFinal10

open scoped Classical

namespace Erdos634.Draft.NSQLegs

open Erdos634.Geometry Erdos634.Draft.ChainComposite

/-- **Leg words under `gcd(k, N) = 1`** (`leg_words_gen` with the coprimality hypothesis it actually uses). -/
theorem leg_words_cop (M M' k m : ℕ) (hM : 0 < M) (hkN : Nat.Coprime k (M * M')) (hlt : 3 * M < M')
    (hk : 2 * k + M = M') (hm : 2 * m = M' + M) (p q r : ℕ)
    (h : (M * M') * k = p * k ^ 2 + q * (M * M') + r * k * m) :
    (q = k ∧ p = 0 ∧ r = 0) ∨ (q = 0 ∧ p * k + r * m = M * M') := by
  have hk2 : 2 ≤ k := by omega
  have hN0 : 0 < M * M' := Nat.mul_pos hM (by omega)
  have hqk : q ≤ k := by
    by_contra hlt'
    push Not at hlt'
    have : (M * M') * k < q * (M * M') := by nlinarith
    omega
  have hdvd : k ∣ q * (M * M') := by
    have hle : p * k + r * m ≤ M * M' := by
      by_contra hcon
      push Not at hcon
      have : k * (p * k + r * m) > k * (M * M') := Nat.mul_lt_mul_of_pos_left hcon (by omega)
      nlinarith
    refine ⟨(M * M') - (p * k + r * m), ?_⟩
    have e1 : k * ((M * M') - (p * k + r * m)) = k * (M * M') - k * (p * k + r * m) := by
      rw [Nat.mul_sub]
    rw [e1]
    have : k * (M * M') = k * (p * k + r * m) + q * (M * M') := by nlinarith
    omega
  have hkq : k ∣ q := hkN.dvd_of_dvd_mul_right hdvd
  obtain ⟨t, ht⟩ := hkq
  have ht1 : t ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have : q ≥ 2 * k := by rw [ht]; nlinarith
    omega
  interval_cases t
  · right
    refine ⟨by omega, ?_⟩
    have hq0 : q = 0 := by omega
    subst hq0
    have : k * (p * k + r * m) = k * (M * M') := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · left
    have hq : q = k := by omega
    subst hq
    have h0 : p * q ^ 2 + r * q * m = 0 := by linarith [h, mul_comm (M * M') q]
    have hpq : p * q ^ 2 = 0 := by omega
    have hrq : r * q * m = 0 := by omega
    have hm0 : 0 < m := by omega
    refine ⟨rfl, ?_, ?_⟩
    · rcases Nat.mul_eq_zero.mp hpq with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    · rcases Nat.mul_eq_zero.mp hrq with h1 | h1
      · rcases Nat.mul_eq_zero.mp h1 with h2 | h2
        · exact h2
        · omega
      · omega

/-- **The arithmetic condition replacing `Squarefree N` in the `γ = 2α` branch.** -/
def GammaArith (N : ℕ) : Prop :=
  ∀ M M' : ℕ, 0 < M → M * M' = N → 3 * M < M' → M % 2 = N % 2 → M' % 2 = N % 2 →
    Nat.Coprime ((M' - M) / 2) N

/-- Squarefree `N` satisfies `GammaArith N` (so the theorem below generalises `Row4.not_squarefree`). -/
theorem gammaArith_of_squarefree {N : ℕ} (hsq : Squarefree N) : GammaArith N := by
  intro M M' hM hNM hlt hMp hM'p
  have hcop : Nat.Coprime M M' := (Nat.squarefree_mul_iff.mp (hNM ▸ hsq)).1
  obtain ⟨k, hk⟩ : ∃ k, M' = M + 2 * k := ⟨(M' - M) / 2, by omega⟩
  have hkdef : (M' - M) / 2 = k := by omega
  rw [hkdef, ← hNM]
  have hkM : Nat.Coprime k M := by
    have h1 : Nat.gcd k M ∣ k := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd k M ∣ M := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd k M ∣ M' := by
      rw [hk]; exact dvd_add h2 (dvd_mul_of_dvd_right h1 2)
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h2 h3)
  have hkM' : Nat.Coprime k M' := by
    have h1 : Nat.gcd k M' ∣ k := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd k M' ∣ M' := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd k M' ∣ M := by
      have : Nat.gcd k M' ∣ M + 2 * k := hk ▸ h2
      exact (Nat.dvd_add_left (dvd_mul_of_dvd_right h1 2)).mp this
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h3 h2)
  exact Nat.Coprime.mul_right hkM hkM'

/-- **A2 (non-squarefree).**  Under `GammaArith N`, every leg word has `q ∈ {0, k}` (`k ≥ 2`). -/
theorem Row4.nsq_legs (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) (hG : GammaArith N) :
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
    have := hG M M' hMpos hNn.symm hlt' hMp hM'p
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

/-- **`γ = 2α`, base-α target, `GammaArith N`**: no tiling.  Copy of `Row4.not_squarefree` with `Row4.nsq_legs`. -/
theorem Row4.not_gammaArith (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) (hG : GammaArith N) : False := by
  obtain ⟨k, hk2, hwords⟩ := Row4.nsq_legs D hα h hA hC hG
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

private theorem cA4 (p q r : Plane) : cornerAngle p q r = cornerAngle r q p :=
  EuclideanGeometry.angle_comm (V := Plane) p q r

/-- **`γ = 2α` under `GammaArith N`, any-label form** (`CaseGClosed N`). -/
theorem caseG_of_gammaArith (N : ℕ) (hG : GammaArith N) : CaseGClosed N := by
  intro D α a b c hα h i j hij hi hj
  have key : ∀ σ : Equiv.Perm (Fin 3),
      (D.relabelTarget' σ).target.angleAt 0 = α → (D.relabelTarget' σ).target.angleAt 1 = α → False :=
    fun σ h0 h1 => Row4.not_gammaArith (D.relabelTarget' σ) hα h h0 h1 hG
  have p01 : D.target.angleAt 0 = α → D.target.angleAt 1 = α → False := fun h0 h1 =>
    key 1 (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h0)
      (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h1)
  have p02 : D.target.angleAt 0 = α → D.target.angleAt 2 = α → False := fun h0 h2 =>
    key (Equiv.swap 1 2)
      (by
        have := h0; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA4]; simpa using this)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA4]; simpa using this)
  have p12 : D.target.angleAt 1 = α → D.target.angleAt 2 = α → False := fun h1 h2 =>
    key (Equiv.swap 0 2)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA4]; simpa using this)
      (by
        have := h1; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA4]; simpa using this)
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact p01 hi hj | exact p01 hj hi | exact p02 hi hj | exact p02 hj hi
    | exact p12 hi hj | exact p12 hj hi

end Erdos634.Draft.NSQLegs

#print axioms Erdos634.Draft.NSQLegs.leg_words_cop
#print axioms Erdos634.Draft.NSQLegs.gammaArith_of_squarefree
#print axioms Erdos634.Draft.NSQLegs.Row4.nsq_legs
#print axioms Erdos634.Draft.NSQLegs.Row4.not_gammaArith
#print axioms Erdos634.Draft.NSQLegs.caseG_of_gammaArith
