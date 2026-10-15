/-
Algebraic core of the uniform commensurable-angle kill (`N = d s²`).

Integer polynomials are lists (`ev x` is Horner evaluation).  For `x = zx n = e^{iπ/n}`:
* `zx_T`: `x^u + x^{n−u} = 2 i sin(uπ/n)`;
* `ev_mulT`: multiplication by `x^u + x^{n−u}` on lists of length `n` (the ring `ℤ[x]/(xⁿ + 1)`: two negacyclic
  rotations);
* `zx_coeffs`: `1, x, …, x^{φ(2n)−1}` are linearly independent over `ℚ` (Mathlib: the minimal polynomial of a
  primitive root is the cyclotomic polynomial);
* `RedOK`, `red_sound`: a table `red` with `x^e = Σ_r red[e][r] x^r` (`e < n`), checked from quotients `quo` by the
  polynomial identities `quo[e] · G + red[e] = X^e`, `G` a monic integer polynomial with `G(x) = 0`;
* `key`: if `Σ_t q_t · ev x (V_t) = 0` with rational `q_t` and integer lists `V_t` of length `≤ n`, then for every
  integer row `ℓ`: `Σ_t q_t · ⟨V_t, red.map ⟨ℓ, ·⟩⟩ = 0` (apply the `ℚ`-linear functional given by `ℓ` on the power
  basis).

No sorry, no native_decide.
-/
import Mathlib

open Finset

namespace Erdos634.Draft.GAU

/-! ## Integer polynomials as lists -/

/-- Horner evaluation of an integer coefficient list -/
noncomputable def ev (x : ℂ) : List ℤ → ℂ
  | [] => 0
  | a :: v => (a : ℂ) + x * ev x v

def addL : List ℤ → List ℤ → List ℤ
  | [], w => w
  | a :: v, [] => a :: v
  | a :: v, b :: w => (a + b) :: addL v w

def negL (v : List ℤ) : List ℤ := v.map (fun a => -a)

def scaleL (c : ℤ) (v : List ℤ) : List ℤ := v.map (fun a => c * a)

def dotL : List ℤ → List ℤ → ℤ
  | a :: v, b :: w => a * b + dotL v w
  | [], _ => 0
  | _ :: _, [] => 0

/-- plain product -/
def mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: v, w => addL (scaleL a w) (0 :: mulL v w)

/-- equality of polynomials given as lists (trailing zeros ignored) -/
def eqPoly (v w : List ℤ) : Bool := (addL v (negL w)).all (fun a => a == 0)

variable {x : ℂ}

theorem ev_addL (v w : List ℤ) : ev x (addL v w) = ev x v + ev x w := by
  induction v generalizing w with
  | nil => simp [addL, ev]
  | cons a v ih =>
    cases w with
    | nil => simp [addL, ev]
    | cons b w => simp only [addL, ev, ih]; push_cast; ring

theorem ev_negL (v : List ℤ) : ev x (negL v) = - ev x v := by
  induction v with
  | nil => simp [negL, ev]
  | cons a v ih =>
    have : negL (a :: v) = (-a) :: negL v := rfl
    rw [this]; simp only [ev, ih]; push_cast; ring

theorem ev_scaleL (c : ℤ) (v : List ℤ) : ev x (scaleL c v) = (c : ℂ) * ev x v := by
  induction v with
  | nil => simp [scaleL, ev]
  | cons a v ih =>
    have : scaleL c (a :: v) = (c * a) :: scaleL c v := rfl
    rw [this]; simp only [ev, ih]; push_cast; ring

theorem ev_mulL (v w : List ℤ) : ev x (mulL v w) = ev x v * ev x w := by
  induction v with
  | nil => simp [mulL, ev]
  | cons a v ih =>
    simp only [mulL, ev_addL, ev_scaleL, ev, ih]; push_cast; ring

theorem ev_append (v w : List ℤ) : ev x (v ++ w) = ev x v + x ^ v.length * ev x w := by
  induction v with
  | nil => simp [ev]
  | cons a v ih =>
    simp only [List.cons_append, ev, ih, List.length_cons]; ring

theorem ev_all_zero (v : List ℤ) (h : v.all (fun a => a == 0) = true) : ev x v = 0 := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [ev, h.1, ih h.2]; simp

theorem ev_of_eqPoly {v w : List ℤ} (h : eqPoly v w = true) : ev x v = ev x w := by
  have := ev_all_zero (x := x) _ h
  rw [ev_addL, ev_negL] at this
  linear_combination this

theorem ev_replicate_zero (k : ℕ) : ev x (List.replicate k (0 : ℤ)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ev, ih]

/-- the monomial `X^e` -/
def monoL (e : ℕ) : List ℤ := List.replicate e 0 ++ [1]

theorem ev_monoL (e : ℕ) : ev x (monoL e) = x ^ e := by
  unfold monoL
  rw [ev_append, ev_replicate_zero, List.length_replicate]
  simp [ev]

theorem ev_sum (v : List ℤ) (N : ℕ) (h : v.length ≤ N) :
    ev x v = ∑ i ∈ range N, ((v.getD i 0 : ℤ) : ℂ) * x ^ i := by
  induction v generalizing N with
  | nil => simp [ev]
  | cons a v ih =>
    cases N with
    | zero => simp at h
    | succ N =>
      rw [Finset.sum_range_succ', ev, ih N (by simpa using h), Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem dotL_sum (v w : List ℤ) (N : ℕ) (h : v.length ≤ N) :
    dotL v w = ∑ i ∈ range N, v.getD i 0 * w.getD i 0 := by
  induction v generalizing w N with
  | nil => simp [dotL]
  | cons a v ih =>
    cases N with
    | zero => simp at h
    | succ N =>
      cases w with
      | nil => simp [dotL]
      | cons b w =>
        rw [Finset.sum_range_succ', dotL, ih w N (by simpa using h)]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        ring

theorem dotL_comm (v w : List ℤ) : dotL v w = dotL w v := by
  induction v generalizing w with
  | nil => cases w <;> simp [dotL]
  | cons a v ih =>
    cases w with
    | nil => simp [dotL]
    | cons b w => simp only [dotL, ih w]; ring

theorem length_addL (v w : List ℤ) : (addL v w).length = max v.length w.length := by
  induction v generalizing w with
  | nil => simp [addL]
  | cons a v ih =>
    cases w with
    | nil => simp [addL]
    | cons b w => simp only [addL, List.length_cons, ih w]; omega

/-! ## The ring `ℤ[x]/(xⁿ + 1)` on lists of length `n` -/

/-- multiplication by `x^u` -/
def rotN (n u : ℕ) (v : List ℤ) : List ℤ := negL (v.drop (n - u)) ++ v.take (n - u)

theorem length_rotN {n u : ℕ} {v : List ℤ} (hv : v.length = n) (hu : u ≤ n) : (rotN n u v).length = n := by
  unfold rotN negL
  simp only [List.length_append, List.length_map, List.length_drop, List.length_take, hv]
  omega

theorem ev_rotN {n u : ℕ} (hx : x ^ n = -1) (hu : u ≤ n) {v : List ℤ} (hv : v.length = n) :
    ev x (rotN n u v) = x ^ u * ev x v := by
  have hsplit : v = v.take (n - u) ++ v.drop (n - u) := (List.take_append_drop _ _).symm
  have h1 : ev x v = ev x (v.take (n - u)) + x ^ (n - u) * ev x (v.drop (n - u)) := by
    have hmin : min (n - u) v.length = n - u := by rw [hv]; omega
    conv_lhs => rw [hsplit]
    rw [ev_append, List.length_take, hmin]
  have hlen : (negL (v.drop (n - u))).length = u := by
    unfold negL; simp only [List.length_map, List.length_drop, hv]; omega
  unfold rotN
  rw [ev_append, ev_negL, hlen, h1]
  have h2 : x ^ u * x ^ (n - u) = -1 := by rw [← pow_add, show u + (n - u) = n by omega, hx]
  linear_combination (- ev x (v.drop (n - u))) * h2

/-- multiplication by `x^u + x^{n−u}` -/
def mulT (n u : ℕ) (v : List ℤ) : List ℤ := addL (rotN n u v) (rotN n (n - u) v)

theorem length_mulT {n u : ℕ} {v : List ℤ} (hv : v.length = n) (hu : u ≤ n) : (mulT n u v).length = n := by
  unfold mulT
  rw [length_addL, length_rotN hv hu, length_rotN hv (Nat.sub_le n u)]
  simp

theorem ev_mulT {n u : ℕ} (hx : x ^ n = -1) (hu : u ≤ n) {v : List ℤ} (hv : v.length = n) :
    ev x (mulT n u v) = (x ^ u + x ^ (n - u)) * ev x v := by
  unfold mulT
  rw [ev_addL, ev_rotN hx hu hv, ev_rotN hx (Nat.sub_le n u) hv]
  ring

/-- the constant `1` as a list of length `n` -/
def oneL (n : ℕ) : List ℤ := 1 :: List.replicate (n - 1) 0

theorem length_oneL {n : ℕ} (hn : 0 < n) : (oneL n).length = n := by
  unfold oneL; simp; omega

theorem ev_oneL (n : ℕ) : ev x (oneL n) = 1 := by
  unfold oneL; simp [ev, ev_replicate_zero]

/-! ## The root of unity `e^{iπ/n}` -/

/-- `e^{iπ/n}` -/
noncomputable def zx (n : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / n)

theorem zx_pow {n : ℕ} (hn : 0 < n) (u : ℕ) :
    zx n ^ u = Complex.exp ((((u : ℝ) * Real.pi / n : ℝ) : ℂ) * Complex.I) := by
  unfold zx
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

theorem zx_pow_n {n : ℕ} (hn : 0 < n) : zx n ^ n = -1 := by
  rw [zx_pow hn n]
  have : ((n : ℝ) * Real.pi / n : ℝ) = Real.pi := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- `x^u + x^{n−u} = 2 i sin(uπ/n)` -/
theorem zx_T {n : ℕ} (hn : 0 < n) {u : ℕ} (hu : u ≤ n) :
    zx n ^ u + zx n ^ (n - u) = 2 * Complex.I * ((Real.sin ((u : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  rw [zx_pow hn u, zx_pow hn (n - u)]
  have h1 : (((n - u : ℕ) : ℝ) * Real.pi / n : ℝ) = Real.pi - (u : ℝ) * Real.pi / n := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Nat.cast_sub hu]
    field_simp
  rw [h1, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_pi_sub, Complex.sin_pi_sub]
  ring

theorem zx_primitive {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (zx n) (2 * n) := by
  have h := Complex.isPrimitiveRoot_exp (2 * n) (by omega)
  have e : Complex.exp (2 * Real.pi * Complex.I / ((2 * n : ℕ) : ℂ)) = zx n := by
    unfold zx
    congr 1
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  rwa [e] at h

/-- **Linear independence of the first `φ(2n)` powers.** -/
theorem zx_coeffs {n : ℕ} (hn : 0 < n) (c : ℕ → ℚ)
    (h : ∑ r ∈ range (Nat.totient (2 * n)), (c r : ℂ) * zx n ^ r = 0) :
    ∀ r, r < Nat.totient (2 * n) → c r = 0 := by
  have hprim := zx_primitive hn
  have hmin : Polynomial.cyclotomic (2 * n) ℚ = minpoly ℚ (zx n) :=
    Polynomial.cyclotomic_eq_minpoly_rat hprim (by omega)
  have hdeg : (minpoly ℚ (zx n)).natDegree = Nat.totient (2 * n) := by
    rw [← hmin, Polynomial.natDegree_cyclotomic]
  have hli := linearIndependent_pow (K := ℚ) (zx n)
  rw [Fintype.linearIndependent_iff] at hli
  intro r hr
  have h2 : ∑ i : Fin (minpoly ℚ (zx n)).natDegree, (c (i : ℕ)) • (zx n ^ (i : ℕ)) = 0 := by
    simp only [Rat.smul_def]
    rw [Fin.sum_univ_eq_sum_range (fun i => (c i : ℂ) * zx n ^ i), hdeg]
    exact h
  exact hli (fun i => c (i : ℕ)) h2 ⟨r, by rw [hdeg]; exact hr⟩

/-! ## The reduction table -/

/-- the table `red` is correct modulo the polynomial `G`: `quo[e] · G + red[e] = X^e` for `e < n`, and the rows of
`red` have length at most `φ` -/
def RedOK (n φ : ℕ) (G : List ℤ) (red quo : List (List ℤ)) : Bool :=
  (List.range n).all fun e =>
    eqPoly (addL (mulL (quo.getD e []) G) (red.getD e [])) (monoL e) && decide ((red.getD e []).length ≤ φ)

theorem red_sound {n φ : ℕ} {G : List ℤ} {red quo : List (List ℤ)} (hok : RedOK n φ G red quo = true)
    (hG : ev x G = 0) {e : ℕ} (he : e < n) :
    x ^ e = ev x (red.getD e []) ∧ (red.getD e []).length ≤ φ := by
  unfold RedOK at hok
  rw [List.all_eq_true] at hok
  have h := hok e (List.mem_range.mpr he)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  have h1 := ev_of_eqPoly (x := x) h.1
  rw [ev_addL, ev_mulL, hG, mul_zero, zero_add, ev_monoL] at h1
  exact h1.symm

/-- **The key step.**  A rational combination of integer lists that vanishes at `zx n` vanishes under every
functional given by an integer row on the power basis. -/
theorem key {n : ℕ} (hn : 0 < n) (red : List (List ℤ)) (hredlen : red.length = n)
    (hred : ∀ e, e < n → zx n ^ e = ev (zx n) (red.getD e []) ∧
      (red.getD e []).length ≤ Nat.totient (2 * n))
    {ι : Type*} [Fintype ι] (q : ι → ℚ) (V : ι → List ℤ) (hV : ∀ t, (V t).length ≤ n)
    (h : ∑ t, (q t : ℂ) * ev (zx n) (V t) = 0) (ℓ : List ℤ) :
    ∑ t, q t * ((dotL (V t) (red.map (dotL ℓ)) : ℤ) : ℚ) = 0 := by
  classical
  -- coordinates
  have hpow : ∀ e, e < n → zx n ^ e
      = ∑ r ∈ range (Nat.totient (2 * n)), (((red.getD e []).getD r 0 : ℤ) : ℂ) * zx n ^ r := by
    intro e he
    obtain ⟨h1, h2⟩ := hred e he
    rw [h1]
    exact ev_sum _ _ h2
  have hev : ∀ t, ev (zx n) (V t) = ∑ r ∈ range (Nat.totient (2 * n)),
      ((∑ e ∈ range n, (V t).getD e 0 * (red.getD e []).getD r 0 : ℤ) : ℂ) * zx n ^ r := by
    intro t
    rw [ev_sum _ n (hV t)]
    have : ∀ e ∈ range n, (((V t).getD e 0 : ℤ) : ℂ) * zx n ^ e
        = ∑ r ∈ range (Nat.totient (2 * n)),
          (((V t).getD e 0 * (red.getD e []).getD r 0 : ℤ) : ℂ) * zx n ^ r := by
      intro e he
      rw [hpow e (Finset.mem_range.mp he), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_mul]
    congr 1
    exact (Int.cast_sum _ _).symm
  -- the coefficient of `x^r`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℚ, ∀ r, c r = ∑ t, q t *
      ((∑ e ∈ range n, (V t).getD e 0 * (red.getD e []).getD r 0 : ℤ) : ℚ) := ⟨fun r => _, fun r => rfl⟩
  have hsum : ∑ r ∈ range (Nat.totient (2 * n)), (c r : ℂ) * zx n ^ r = 0 := by
    rw [← h]
    have : ∀ t, (q t : ℂ) * ev (zx n) (V t) = ∑ r ∈ range (Nat.totient (2 * n)),
        ((q t * ((∑ e ∈ range n, (V t).getD e 0 * (red.getD e []).getD r 0 : ℤ) : ℚ) : ℚ) : ℂ)
          * zx n ^ r := by
      intro t
      rw [hev t, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      push_cast; ring
    rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_mul, hc r]
    congr 1
    rw [Rat.cast_sum]
  have hzero := zx_coeffs hn c hsum
  -- apply the row
  have hlam : ∀ e, e < n → (red.map (dotL ℓ)).getD e 0
      = ∑ r ∈ range (Nat.totient (2 * n)), ℓ.getD r 0 * (red.getD e []).getD r 0 := by
    intro e he
    have he' : e < red.length := by rw [hredlen]; exact he
    have e1 : (red.map (dotL ℓ)).getD e 0 = dotL ℓ (red.getD e []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem he']
      simp
    rw [e1, dotL_comm, dotL_sum _ _ _ (hred e he).2]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hgoal : ∀ t, ((dotL (V t) (red.map (dotL ℓ)) : ℤ) : ℚ)
      = ∑ r ∈ range (Nat.totient (2 * n)), (ℓ.getD r 0 : ℚ) *
        ((∑ e ∈ range n, (V t).getD e 0 * (red.getD e []).getD r 0 : ℤ) : ℚ) := by
    intro t
    rw [dotL_sum _ _ n (hV t)]
    have : ∀ e ∈ range n, (V t).getD e 0 * (red.map (dotL ℓ)).getD e 0
        = ∑ r ∈ range (Nat.totient (2 * n)), ℓ.getD r 0 * ((V t).getD e 0 * (red.getD e []).getD r 0) := by
      intro e he
      rw [hlam e (Finset.mem_range.mp he), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    push_cast
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  calc ∑ t, q t * ((dotL (V t) (red.map (dotL ℓ)) : ℤ) : ℚ)
      = ∑ t, ∑ r ∈ range (Nat.totient (2 * n)), (ℓ.getD r 0 : ℚ) *
          (q t * ((∑ e ∈ range n, (V t).getD e 0 * (red.getD e []).getD r 0 : ℤ) : ℚ)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hgoal t, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ = ∑ r ∈ range (Nat.totient (2 * n)), (ℓ.getD r 0 : ℚ) * c r := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [hc r, Finset.mul_sum]
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        rw [hzero r (Finset.mem_range.mp hr), mul_zero]

end Erdos634.Draft.GAU

#print axioms Erdos634.Draft.GAU.zx_coeffs
#print axioms Erdos634.Draft.GAU.key
