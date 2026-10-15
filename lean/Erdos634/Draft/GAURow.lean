/-
From the sine identity with rational coefficients to one rational equation per integer row.

* `ev_G30`, `ev_G60`: the cyclotomic polynomials `Φ₆₀`, `Φ₁₂₀` (as explicit integer lists) vanish at `zx 30`, `zx 60`
  (from `X³⁰ + 1 = Φ₄Φ₁₂Φ₂₀Φ₆₀`, `X⁶⁰ + 1 = Φ₈Φ₂₄Φ₄₀Φ₁₂₀` and the primitivity of the root; no computation of
  cyclotomic polynomials in Mathlib is needed).
* `IdQ d n a A B C m`: the identity
  `(Σ_k m_k sin(a_k π/n))² sin(Bπ/n) sin(Cπ/n) = d sin(Aπ/n) Π_k sin(a_k π/n)` with `m ∈ ℚ³`.
* `colV`, `rV`: the lists of `T_i T_j T_B T_C` and `T_A T_0 T_1 T_2` in `ℤ[x]/(xⁿ + 1)`, `T_u = x^u + x^{n−u}`.
* `row_eq`: for every integer row `ℓ` on the power basis,
  `Σ_{i,j} m_i m_j ⟨colV i j, λ⟩ = d ⟨rV, λ⟩`, `λ = red.map ⟨ℓ, ·⟩`.

No sorry, no native_decide.
-/
import Erdos634.Draft.GAUCore

open Finset

namespace Erdos634.Draft.GAU

def G30 : List ℤ := [1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1]

def G60 : List ℤ :=
  [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]

theorem ev_G30 : ev (zx 30) G30 = 0 := by
  have hx := zx_pow_n (n := 30) (by norm_num)
  have hprim := zx_primitive (n := 30) (by norm_num)
  obtain ⟨x, hxdef⟩ : ∃ x : ℂ, x = zx 30 := ⟨_, rfl⟩
  rw [← hxdef] at hx hprim ⊢
  have h4 : x ^ 2 + 1 ≠ 0 := by
    intro h
    have e : x ^ 4 = 1 := by linear_combination (x ^ 2 - 1) * h
    exact absurd ((hprim.pow_eq_one_iff_dvd 4).mp e) (by decide)
  have h12 : x ^ 4 - x ^ 2 + 1 ≠ 0 := by
    intro h
    have e : x ^ 12 = 1 := by linear_combination ((x ^ 6 - 1) * (x ^ 2 + 1)) * h
    exact absurd ((hprim.pow_eq_one_iff_dvd 12).mp e) (by decide)
  have h20 : x ^ 8 - x ^ 6 + x ^ 4 - x ^ 2 + 1 ≠ 0 := by
    intro h
    have e : x ^ 20 = 1 := by linear_combination ((x ^ 10 - 1) * (x ^ 2 + 1)) * h
    exact absurd ((hprim.pow_eq_one_iff_dvd 20).mp e) (by decide)
  have hprod : ev x G30 * ((x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) * (x ^ 8 - x ^ 6 + x ^ 4 - x ^ 2 + 1))
      = x ^ 30 + 1 := by
    simp only [G30, ev]
    push_cast
    ring
  rw [hx] at hprod
  have h0 : ev x G30 * ((x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) * (x ^ 8 - x ^ 6 + x ^ 4 - x ^ 2 + 1)) = 0 := by
    rw [hprod]; ring
  exact (mul_eq_zero.mp h0).resolve_right (mul_ne_zero (mul_ne_zero h4 h12) h20)

theorem ev_G60 : ev (zx 60) G60 = 0 := by
  have hx := zx_pow_n (n := 60) (by norm_num)
  have hprim := zx_primitive (n := 60) (by norm_num)
  obtain ⟨x, hxdef⟩ : ∃ x : ℂ, x = zx 60 := ⟨_, rfl⟩
  rw [← hxdef] at hx hprim ⊢
  have h8 : x ^ 4 + 1 ≠ 0 := by
    intro h
    have e : x ^ 8 = 1 := by linear_combination (x ^ 4 - 1) * h
    exact absurd ((hprim.pow_eq_one_iff_dvd 8).mp e) (by decide)
  have h24 : x ^ 8 - x ^ 4 + 1 ≠ 0 := by
    intro h
    have e : x ^ 24 = 1 := by linear_combination ((x ^ 12 - 1) * (x ^ 4 + 1)) * h
    exact absurd ((hprim.pow_eq_one_iff_dvd 24).mp e) (by decide)
  have h40 : x ^ 16 - x ^ 12 + x ^ 8 - x ^ 4 + 1 ≠ 0 := by
    intro h
    have e : x ^ 40 = 1 := by linear_combination ((x ^ 20 - 1) * (x ^ 4 + 1)) * h
    exact absurd ((hprim.pow_eq_one_iff_dvd 40).mp e) (by decide)
  have hprod : ev x G60 * ((x ^ 4 + 1) * (x ^ 8 - x ^ 4 + 1) * (x ^ 16 - x ^ 12 + x ^ 8 - x ^ 4 + 1))
      = x ^ 60 + 1 := by
    simp only [G60, ev]
    push_cast
    ring
  rw [hx] at hprod
  have h0 : ev x G60 * ((x ^ 4 + 1) * (x ^ 8 - x ^ 4 + 1) * (x ^ 16 - x ^ 12 + x ^ 8 - x ^ 4 + 1)) = 0 := by
    rw [hprod]; ring
  exact (mul_eq_zero.mp h0).resolve_right (mul_ne_zero (mul_ne_zero h8 h24) h40)

/-! ## The identity and its lists -/

/-- the identity with rational coefficients `m` and the constant `d` -/
def IdQ (d n : ℕ) (a : Fin 3 → ℕ) (A B C : ℕ) (m : Fin 3 → ℚ) : Prop :=
  (∑ k, (m k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
    = (d : ℝ) * Real.sin (A * Real.pi / n) * ∏ k, Real.sin (a k * Real.pi / n)

/-- the list of `x^u + x^{n−u}` -/
def tvN (n u : ℕ) : List ℤ := mulT n u (oneL n)

/-- the list of `T_i T_j T_B T_C` -/
def colV (n : ℕ) (a : Fin 3 → ℕ) (B C : ℕ) (i j : Fin 3) : List ℤ :=
  mulT n (a i) (mulT n (a j) (mulT n B (tvN n C)))

/-- the list of `T_A T_0 T_1 T_2` -/
def rV (n : ℕ) (a : Fin 3 → ℕ) (A : ℕ) : List ℤ :=
  mulT n A (mulT n (a 0) (mulT n (a 1) (tvN n (a 2))))

/-- `2 i sin(uπ/n)` -/
noncomputable def sC (n u : ℕ) : ℂ := 2 * Complex.I * ((Real.sin ((u : ℝ) * Real.pi / n) : ℝ) : ℂ)

theorem length_tvN {n u : ℕ} (hn : 0 < n) (hu : u ≤ n) : (tvN n u).length = n :=
  length_mulT (length_oneL hn) hu

theorem ev_tvN {n u : ℕ} (hn : 0 < n) (hu : u ≤ n) : ev (zx n) (tvN n u) = sC n u := by
  unfold tvN
  rw [ev_mulT (zx_pow_n hn) hu (length_oneL hn), ev_oneL, mul_one, zx_T hn hu]
  rfl

theorem ev_mulT' {n u : ℕ} (hn : 0 < n) (hu : u ≤ n) {v : List ℤ} (hv : v.length = n) :
    ev (zx n) (mulT n u v) = sC n u * ev (zx n) v := by
  rw [ev_mulT (zx_pow_n hn) hu hv, zx_T hn hu]
  rfl

theorem length_colV {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} (ha : ∀ k, a k ≤ n) {B C : ℕ} (hB : B ≤ n)
    (hC : C ≤ n) (i j : Fin 3) : (colV n a B C i j).length = n :=
  length_mulT (length_mulT (length_mulT (length_tvN hn hC) hB) (ha j)) (ha i)

theorem ev_colV {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} (ha : ∀ k, a k ≤ n) {B C : ℕ} (hB : B ≤ n)
    (hC : C ≤ n) (i j : Fin 3) :
    ev (zx n) (colV n a B C i j) = sC n (a i) * (sC n (a j) * (sC n B * sC n C)) := by
  unfold colV
  rw [ev_mulT' hn (ha i) (length_mulT (length_mulT (length_tvN hn hC) hB) (ha j)),
    ev_mulT' hn (ha j) (length_mulT (length_tvN hn hC) hB), ev_mulT' hn hB (length_tvN hn hC), ev_tvN hn hC]

theorem length_rV {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} (ha : ∀ k, a k ≤ n) {A : ℕ} (hA : A ≤ n) :
    (rV n a A).length = n :=
  length_mulT (length_mulT (length_mulT (length_tvN hn (ha 2)) (ha 1)) (ha 0)) hA

theorem ev_rV {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} (ha : ∀ k, a k ≤ n) {A : ℕ} (hA : A ≤ n) :
    ev (zx n) (rV n a A) = sC n A * (sC n (a 0) * (sC n (a 1) * sC n (a 2))) := by
  unfold rV
  rw [ev_mulT' hn hA (length_mulT (length_mulT (length_tvN hn (ha 2)) (ha 1)) (ha 0)),
    ev_mulT' hn (ha 0) (length_mulT (length_tvN hn (ha 2)) (ha 1)), ev_mulT' hn (ha 1) (length_tvN hn (ha 2)),
    ev_tvN hn (ha 2)]

/-- **One rational equation per row.** -/
theorem row_eq {n : ℕ} (hn : 0 < n) {red : List (List ℤ)} (hredlen : red.length = n)
    (hred : ∀ e, e < n → zx n ^ e = ev (zx n) (red.getD e []) ∧
      (red.getD e []).length ≤ Nat.totient (2 * n))
    {d : ℕ} {a : Fin 3 → ℕ} {A B C : ℕ} (ha : ∀ k, a k ≤ n) (hA : A ≤ n) (hB : B ≤ n) (hC : C ≤ n)
    {m : Fin 3 → ℚ} (hid : IdQ d n a A B C m) (ℓ : List ℤ) :
    ∑ i, ∑ j, m i * m j * ((dotL (colV n a B C i j) (red.map (dotL ℓ)) : ℤ) : ℚ)
      = (d : ℚ) * ((dotL (rV n a A) (red.map (dotL ℓ)) : ℤ) : ℚ) := by
  -- the identity over `ℂ`
  have hC' : ((∑ k, (m k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n)
      * Real.sin (C * Real.pi / n) : ℝ)
      = (((d : ℝ) * Real.sin (A * Real.pi / n) * ∏ k, Real.sin (a k * Real.pi / n) : ℝ)) := hid
  have hcx := congrArg (fun r : ℝ => (r : ℂ)) hC'
  simp only [Fin.sum_univ_three, Fin.prod_univ_three] at hcx
  push_cast at hcx
  -- the combination
  obtain ⟨q, hq⟩ : ∃ q : Option (Fin 3 × Fin 3) → ℚ,
      q = fun t => match t with
        | none => -(d : ℚ)
        | some ij => m ij.1 * m ij.2 := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : Option (Fin 3 × Fin 3) → List ℤ,
      V = fun t => match t with
        | none => rV n a A
        | some ij => colV n a B C ij.1 ij.2 := ⟨_, rfl⟩
  have hVlen : ∀ t, (V t).length ≤ n := by
    intro t
    rw [hVd]
    cases t with
    | none => exact (length_rV hn ha hA).le
    | some ij => exact (length_colV hn ha hB hC ij.1 ij.2).le
  have hzero : ∑ t, (q t : ℂ) * ev (zx n) (V t) = 0 := by
    rw [Fintype.sum_option, Fintype.sum_prod_type, hq, hVd]
    simp only [Fin.sum_univ_three, ev_rV hn ha hA, ev_colV hn ha hB hC, sC]
    push_cast
    linear_combination (16 * Complex.I ^ 4) * hcx
  have hk := key hn red hredlen hred q V hVlen hzero ℓ
  rw [Fintype.sum_option, Fintype.sum_prod_type, hq, hVd] at hk
  simp only at hk
  linarith

end Erdos634.Draft.GAU

#print axioms Erdos634.Draft.GAU.ev_G30
#print axioms Erdos634.Draft.GAU.ev_G60
#print axioms Erdos634.Draft.GAU.row_eq
