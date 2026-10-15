import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Order.Round
import Erdos634.Draft.FDBMod12Converse
import Erdos634.ThinHole

/-!
# The area ratio cannot exclude primes

Main content:
1. `ℤ[√3]` is a Euclidean domain (hence PID, UFD).
2. An element of prime absolute-norm is irreducible.
3. Infinitely many primes ≡ 11 (mod 12) (Dirichlet).
4. Exactly 144 distinct primes of the form `3f²−e²`, gcd 1, `1 ≤ e < f < 40`.
5. `prop_norm_structural` wrapper.

All theorems are sorry-free.

Axioms: `[propext, Classical.choice, Quot.sound]` for all except `count_144`, which uses
`native_decide` (kernel primality checks hit ~100K recursion depth; adds `Lean.ofReducible`).
-/

open Zsqrtd

namespace Erdos634.PropNorm

abbrev Z3 : Type := Zsqrtd (3 : ℤ)

/-! ## Step 1: 3 is not a perfect square -/

lemma three_not_sq : ∀ n : ℤ, (3 : ℤ) ≠ n * n := fun n => by
  intro h
  have hnn : n ^ 2 = 3 := by linarith [show n * n = n ^ 2 from by ring]
  have hge : (-2 : ℤ) < n := by nlinarith [sq_nonneg n, sq_nonneg (n + 2)]
  have hlt : n < (2 : ℤ) := by nlinarith [sq_nonneg n, sq_nonneg (n - 2)]
  interval_cases n <;> omega

lemma Z3_norm_eq_zero_iff (z : Z3) : Zsqrtd.norm z = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero three_not_sq z

lemma Z3_norm_ne_zero {z : Z3} (hz : z ≠ 0) : Zsqrtd.norm z ≠ 0 := by
  rwa [ne_eq, Z3_norm_eq_zero_iff]

/-! ## Step 2: Div and Mod instances for ℤ[√3] -/

private noncomputable instance instDivZ3 : Div Z3 :=
  ⟨fun x y =>
    let n := (Zsqrtd.norm y : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩

lemma Z3_div_def (x y : Z3) :
    x / y = ⟨round ((x * star y).re / (Zsqrtd.norm y : ℚ)),
             round ((x * star y).im / (Zsqrtd.norm y : ℚ))⟩ := by
  show Zsqrtd.mk _ _ = _; simp [div_eq_mul_inv]

private noncomputable instance instModZ3 : Mod Z3 :=
  ⟨fun x y => x - y * (x / y)⟩

lemma Z3_mod_def (x y : Z3) : x % y = x - y * (x / y) := rfl

/-! ## Step 3: Arithmetic bound for the Euclidean property -/

/-- For rationals `|α|, |β| ≤ 1/2`: `|α²−3β²| < 1`. -/
lemma indef_form_lt_one {α β : ℚ} (hα : |α| ≤ 1/2) (hβ : |β| ≤ 1/2) :
    |α ^ 2 - 3 * β ^ 2| < 1 := by
  have hα_pos : (0 : ℚ) ≤ (1/2 + α) * (1/2 - α) := by
    apply mul_nonneg
    · linarith [neg_abs_le α, hα]
    · linarith [(abs_le.mp hα).2]
  have hβ_pos : (0 : ℚ) ≤ (1/2 + β) * (1/2 - β) := by
    apply mul_nonneg
    · linarith [neg_abs_le β, hβ]
    · linarith [(abs_le.mp hβ).2]
  have hα2 : α ^ 2 ≤ 1/4 := by nlinarith
  have hβ2 : β ^ 2 ≤ 1/4 := by nlinarith
  rw [abs_lt]; constructor <;> nlinarith

/-! ## Step 4: Euclidean norm bound -/

/-- The remainder satisfies `|norm(r)| < |norm(y)|`. -/
theorem natAbs_norm_mod_lt (x : Z3) {y : Z3} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have hN_ne : Zsqrtd.norm y ≠ 0 := Z3_norm_ne_zero hy
  have hN_q : (Zsqrtd.norm y : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN_ne
  set N : ℚ := (Zsqrtd.norm y : ℚ) with hN_def
  set P : Z3 := x * star y with hP_def
  set qr : ℤ := round ((P.re : ℚ) / N)
  set qi : ℤ := round ((P.im : ℚ) / N)
  set α : ℚ := (P.re : ℚ) / N - ↑qr
  set β : ℚ := (P.im : ℚ) / N - ↑qi
  have hα_bound : |α| ≤ 1/2 := abs_sub_round _
  have hβ_bound : |β| ≤ 1/2 := abs_sub_round _
  have herr : |α ^ 2 - 3 * β ^ 2| < 1 := indef_form_lt_one hα_bound hβ_bound
  -- y * star y = ⟨norm y, 0⟩
  have hconj : y * star y = ⟨Zsqrtd.norm y, 0⟩ := by
    ext
    · simp [Zsqrtd.norm]; ring
    · simp; ring
  -- x / y = ⟨qr, qi⟩
  have hq_eq : x / y = (⟨qr, qi⟩ : Z3) := Z3_div_def x y
  -- r * star y = ⟨P.re - qr * norm y, P.im - qi * norm y⟩
  have hrstar : (x % y) * star y =
      ⟨P.re - qr * Zsqrtd.norm y, P.im - qi * Zsqrtd.norm y⟩ := by
    rw [Z3_mod_def, hq_eq, sub_mul, ← hP_def,
        show y * (⟨qr, qi⟩ : Z3) * star y = ⟨qr, qi⟩ * (y * star y) by ring,
        hconj]
    ext <;> simp
  -- norm(r) * norm(y) = a^2 - 3*b^2
  have hident : (Zsqrtd.norm (x % y) : ℤ) * Zsqrtd.norm y =
      (P.re - qr * Zsqrtd.norm y) ^ 2 - 3 * (P.im - qi * Zsqrtd.norm y) ^ 2 := by
    have := congr_arg Zsqrtd.norm hrstar
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj] at this
    simp only [Zsqrtd.norm] at this ⊢
    linear_combination this
  -- Cast to ℚ
  have hident_q : (Zsqrtd.norm (x % y) : ℚ) * N =
      (↑P.re - ↑qr * N) ^ 2 - 3 * (↑P.im - ↑qi * N) ^ 2 := by
    have := congr_arg (Int.cast (R := ℚ)) hident; push_cast [hN_def] at this ⊢; linarith
  -- P.re - qr*N = N*α and P.im - qi*N = N*β
  have hαN : (↑P.re - ↑qr * N) = N * α := by
    simp only [α, mul_sub, mul_div_cancel₀ _ hN_q, mul_comm (↑qr) N]
  have hβN : (↑P.im - ↑qi * N) = N * β := by
    simp only [β, mul_sub, mul_div_cancel₀ _ hN_q, mul_comm (↑qi) N]
  -- norm(r) = N * (α^2 - 3β^2)
  have hkey : (Zsqrtd.norm (x % y) : ℚ) = N * (α ^ 2 - 3 * β ^ 2) :=
    mul_right_cancel₀ hN_q (by rw [hident_q, hαN, hβN]; ring)
  -- |(norm r : ℚ)| < |N|
  have hlt_q : |(Zsqrtd.norm (x % y) : ℚ)| < |N| := by
    rw [hkey, abs_mul]
    calc |N| * |α ^ 2 - 3 * β ^ 2|
        < |N| * 1 := mul_lt_mul_of_pos_left herr (abs_pos.mpr hN_q)
      _ = |N| := mul_one _
  -- natAbs comparison: reduce to ℤ-abs comparison then cast to ℕ
  have hlt_int : |(Zsqrtd.norm (x % y))| < |(Zsqrtd.norm y)| := by
    exact_mod_cast (show |(Zsqrtd.norm (x % y) : ℚ)| < |(Zsqrtd.norm y : ℚ)| by
      rwa [hN_def] at hlt_q)
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hlt_int
  exact_mod_cast hlt_int

/-! ## Step 5: EuclideanDomain instance -/

private lemma Z3_norm_le_norm_mul_left (x : Z3) {y : Z3} (hy : y ≠ 0) :
    (Zsqrtd.norm x).natAbs ≤ (Zsqrtd.norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by
    intro h; exact hy ((Z3_norm_eq_zero_iff y).mp (Int.natAbs_eq_zero.mp h))))

noncomputable instance instEuclideanDomainZ3 : EuclideanDomain Z3 :=
  { Zsqrtd.commRing,
    show Nontrivial Z3 from ⟨⟨0, 1, by decide⟩⟩ with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun x => by
      ext <;> simp [Z3_div_def, Zsqrtd.norm]
    quotient_mul_add_remainder_eq := fun x y => by rw [Z3_mod_def]; ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a {b} hb => not_lt_of_ge (Z3_norm_le_norm_mul_left a hb) }

/-! ## PID and UFD -/

example : IsPrincipalIdealRing Z3 := inferInstance
example : UniqueFactorizationMonoid Z3 := inferInstance

/-! ## Step 6: Prime absolute-norm implies irreducible -/

theorem natAbsNorm_prime_isIrreducible {z : Z3} (h : Nat.Prime (Zsqrtd.norm z).natAbs) :
    Irreducible z := by
  constructor
  · intro hunit
    rw [← norm_eq_one_iff] at hunit
    exact Nat.not_prime_one (hunit ▸ h)
  · intro a b hab
    have hn : (Zsqrtd.norm z).natAbs = (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs := by
      rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    rcases h.eq_one_or_self_of_dvd (Zsqrtd.norm a).natAbs
        ⟨(Zsqrtd.norm b).natAbs, hn⟩ with ha | ha
    · left; rwa [← norm_eq_one_iff]
    · right
      rw [← norm_eq_one_iff]
      -- ha : (norm a).natAbs = (norm z).natAbs
      -- hn : (norm z).natAbs = (norm a).natAbs * (norm b).natAbs
      -- → (norm z).natAbs = (norm z).natAbs * (norm b).natAbs
      -- → (norm b).natAbs = 1  (by left cancellation, since prime > 0)
      have heq : (Zsqrtd.norm z).natAbs =
                 (Zsqrtd.norm z).natAbs * (Zsqrtd.norm b).natAbs := ha ▸ hn
      have h' : (Zsqrtd.norm z).natAbs * 1 =
                (Zsqrtd.norm z).natAbs * (Zsqrtd.norm b).natAbs := by
        rw [Nat.mul_one]; exact heq
      exact (mul_left_cancel₀ h.pos.ne' h').symm

/-! ## Step 7: Infinitely many primes ≡ 11 (mod 12) -/

theorem primes_11_mod_12_infinite :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ 11 [MOD 12]} :=
  Nat.infinite_setOf_prime_and_modEq (by decide) (by decide)

/-! ## Step 8: Count-144 -/

-- biUnion over f avoids building the 39×39 Cartesian product in the kernel.
-- Each inner filter is over Finset.Icc 1 f (≤39 elements), staying under recursion depth.
private def normPairs : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 39).biUnion fun f =>
    (Finset.Icc 1 f).filter (fun e => e < f ∧ Nat.Coprime e f ∧ (3 * f ^ 2 - e ^ 2 : ℕ).Prime)
      |>.image (fun e => (e, f))

private def normPrimes : Finset ℕ :=
  normPairs.image (fun ef => 3 * ef.2 ^ 2 - ef.1 ^ 2)

-- kernel `decide` exceeds recursion depth for the primality checks (~100K nested calls).
-- `native_decide` works (Python-confirmed: exactly 144 pairs give 144 distinct primes).
-- This adds Lean.ofReducible to the axiom closure of count_144 only.
set_option maxHeartbeats 800000 in
theorem count_144 : normPrimes.card = 144 := by native_decide

/-! ## Assembly -/

/-- **prop:norm** (obstructions paper): the area ratio `3f²−e²` is a norm form, so it cannot
exclude primes.  Four-clause assembly matching the paper's statement.

(A) ℤ[√3] is an EuclideanDomain (hence PID, UFD); an element of prime absolute-norm is irreducible
(= prime element in a UFD).
(B) Uniqueness: a prime has at most one admissible base-β representation
    `p = 3f²−e²` with `gcd(e,f) = 1`, `1 ≤ e < f` (Proposition M-prop:repunique,
    `ThinHole.rep_unique`).
(C) Infinitely many primes ≡ 11 (mod 12) (Dirichlet, Mathlib).
(D) Exactly 144 distinct primes occur with `gcd(e,f)=1`, `1 ≤ e < f < 40`
    (`count_144`, via `native_decide`; adds `Lean.ofReducible` to axiom closure only here).  -/
theorem prop_norm_structural :
    -- (A)
    (∀ z : Z3, Nat.Prime (Zsqrtd.norm z).natAbs → Irreducible z) ∧
    -- (B) uniqueness of representation (ThinHole.rep_unique)
    (∀ (p e1 f1 e2 f2 : ℤ), Prime p →
        3 * f1 ^ 2 - e1 ^ 2 = p → 1 ≤ e1 → e1 < f1 → IsCoprime e1 f1 →
        3 * f2 ^ 2 - e2 ^ 2 = p → 1 ≤ e2 → e2 < f2 → IsCoprime e2 f2 →
        e1 = e2 ∧ f1 = f2) ∧
    -- (C)
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ 11 [MOD 12]} ∧
    -- (D)
    normPrimes.card = 144 :=
  ⟨fun _z h => natAbsNorm_prime_isIrreducible h,
   fun p e1 f1 e2 f2 hp h1 he1 hlt1 hc1 h2 he2 hlt2 hc2 =>
     ThinHole.rep_unique p e1 f1 e2 f2 hp h1 h2 he1 hlt1 hc1 he2 hlt2 hc2,
   primes_11_mod_12_infinite,
   count_144⟩

end Erdos634.PropNorm
