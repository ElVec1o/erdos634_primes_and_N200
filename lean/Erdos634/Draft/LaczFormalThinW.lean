import Erdos634.Draft.LaczFormalW2Arith

/-!
# Thin-W Base Lemma

Erdős #634, base-`β` row.  Credit: the project's AI assistant (Thin-W proposal, internal working notes P1),
Beeson–Roșu (Lemma 28: relation lattice), Beeson, Laczkovich, Paliy.  NOTE/UNAUDITED.  Axiom-clean; no `sorry`.

`thinW_base`: let `2 ≤ e < f` coprime, `M ≥ 1`, `M e < f`.  If `p a + q b + r c = M e (3f² − e²)` with `r ≥ f`
(`a = ef, b = f²−e², c = f²`), then `q = M e` and there is `ξ` with `p = ξ f`, `r = 2Me − ξ e`, `ξ e + f ≤ 2Me`.
The hypothesis `f ≤ 2Me` of the proposal is not needed (if `2Me < f` then `r ≥ f` is already impossible:
the conclusion `ξ e + f ≤ 2Me` then yields the contradiction itself).  `2 ≤ e` is not used either (`1 ≤ e`).
Hand proof: `(p, q−Me, r−2Me) = η(e,f,−f) + ζ(−f,0,e)`; `q ≥ 0`, `Me < f` force `η ≥ 0`; `p ≥ 0`, `r ≥ f`,
`2Me < 2f` force `η ≤ 0`; so `η = 0`, `ξ = −ζ`.
-/

namespace Erdos634.LaczJunction

theorem thinW_base (e f M p q r : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hM : 1 ≤ M) (hMe : M * e < f)
    (h : p * ta e f + q * tb e f + r * tc e f = M * e * (3 * f ^ 2 - e ^ 2)) (hr : f ≤ r) :
    q = M * e ∧ ∃ ξ : ℕ, p = ξ * f ∧ r + ξ * e = 2 * M * e ∧ ξ * e + f ≤ 2 * M * e := by
  have hb := tb_cast e f hef
  have hf2 : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
  have hZ : (p : ℤ) * (e * f) + ((q : ℤ) - M * e) * ((f:ℤ)^2 - (e:ℤ)^2) +
      ((r : ℤ) - 2 * M * e) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast [Nat.cast_sub hf2] at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hp, hq, hr'⟩ := relation_lattice e f he hef hcop (p : ℤ) ((q : ℤ) - M * e)
    ((r : ℤ) - 2 * M * e) hZ
  have heZ : (1:ℤ) ≤ e := by exact_mod_cast he
  have hefZ : (e:ℤ) < f := by exact_mod_cast hef
  have hMZ : (1:ℤ) ≤ M := by exact_mod_cast hM
  have hMeZ : (M:ℤ) * e < f := by exact_mod_cast hMe
  have hrZ : (f:ℤ) ≤ r := by exact_mod_cast hr
  have hp0 : (0:ℤ) ≤ p := by positivity
  have hq0 : (0:ℤ) ≤ q := by positivity
  have hη : 0 ≤ η := by
    by_contra hneg
    have : η ≤ -1 := by omega
    nlinarith
  have hη0 : η = 0 := by
    by_contra hne
    have hη1 : 1 ≤ η := by omega
    have hζ : ζ ≤ η - 1 := by
      by_contra hz
      have h1 : η ≤ ζ := by omega
      have h2 : η * f ≤ ζ * f := mul_le_mul_of_nonneg_right h1 (by omega)
      have h3 : η * e < η * f := mul_lt_mul_of_pos_left hefZ (by omega)
      linarith
    have h1 : ζ * e ≤ (η - 1) * e := mul_le_mul_of_nonneg_right hζ (by omega)
    have h2 : 0 ≤ (η - 1) * (f - e) := mul_nonneg (by omega) (by omega)
    nlinarith
  subst hη0
  have hζ0 : ζ ≤ 0 := by
    by_contra hz
    have : 1 ≤ ζ := by omega
    have h2 : f ≤ ζ * f := by nlinarith
    linarith
  refine ⟨?_, (-ζ).toNat, ?_, ?_, ?_⟩
  · have : (q:ℤ) = M * e := by rw [show (q:ℤ) = ((q:ℤ) - M * e) + M * e by ring, hq]; ring
    exact_mod_cast this
  · have hz : (((-ζ).toNat : ℕ) : ℤ) = -ζ := Int.toNat_of_nonneg (by omega)
    have : (p:ℤ) = ((-ζ).toNat : ℕ) * f := by rw [hz, hp]; ring
    exact_mod_cast this
  · have hz : (((-ζ).toNat : ℕ) : ℤ) = -ζ := Int.toNat_of_nonneg (by omega)
    have : (r:ℤ) + ((-ζ).toNat : ℕ) * e = 2 * M * e := by
      rw [hz]; have := hr'; linarith
    exact_mod_cast this
  · have hz : (((-ζ).toNat : ℕ) : ℤ) = -ζ := Int.toNat_of_nonneg (by omega)
    have : (((-ζ).toNat : ℕ) : ℤ) * e + f ≤ 2 * M * e := by
      rw [hz]; have := hr'; linarith
    exact_mod_cast this

/-- Corollary: the base word has exactly `M e` tokens of type `b`, and its `a`- and `c`-counts are
`ξ f` and `2Me − ξ e`. -/
theorem thinW_base_bcount (e f M p q r : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hM : 1 ≤ M) (hMe : M * e < f)
    (h : p * ta e f + q * tb e f + r * tc e f = M * e * (3 * f ^ 2 - e ^ 2)) (hr : f ≤ r) :
    q = M * e :=
  (thinW_base e f M p q r he hef hcop hM hMe h hr).1

/-! ### Witnesses (V4): hypotheses fire on real data. -/

-- (e,f,M) = (2,5,2): Me = 4 < 5 ≤ 8; base 284; the decompositions with r ≥ f are (5,4,6) and (0,4,8).
example : (5 : ℕ) * ta 2 5 + 4 * tb 2 5 + 6 * tc 2 5 = 2 * 2 * (3 * 5 ^ 2 - 2 ^ 2) := by
  simp [ta, tb, tc]
example : (0 : ℕ) * ta 2 5 + 4 * tb 2 5 + 8 * tc 2 5 = 2 * 2 * (3 * 5 ^ 2 - 2 ^ 2) := by
  simp [ta, tb, tc]

theorem thinW_wit_2_5_2 :
    ∃ ξ : ℕ, 5 = ξ * 5 ∧ 6 + ξ * 2 = 2 * 2 * 2 ∧ ξ * 2 + 5 ≤ 2 * 2 * 2 :=
  (thinW_base 2 5 2 5 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp [ta, tb, tc]) (by norm_num)).2

theorem thinW_wit_2_5_2' :
    ∃ ξ : ℕ, 0 = ξ * 5 ∧ 8 + ξ * 2 = 2 * 2 * 2 ∧ ξ * 2 + 5 ≤ 2 * 2 * 2 :=
  (thinW_base 2 5 2 0 4 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp [ta, tb, tc]) (by norm_num)).2

-- (3,7,2): Me = 6 < 7 ≤ 12; base 2·3·(147−9) = 828; decompositions with r ≥ 7: (7,6,9), (0,6,12).
theorem thinW_wit_3_7_2 :
    ∃ ξ : ℕ, 7 = ξ * 7 ∧ 9 + ξ * 3 = 2 * 2 * 3 ∧ ξ * 3 + 7 ≤ 2 * 2 * 3 :=
  (thinW_base 3 7 2 7 6 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp [ta, tb, tc]) (by norm_num)).2

-- (3,8,2): Me = 6 < 8 ≤ 12; decompositions with r ≥ 8: (8,6,9), (0,6,12).
theorem thinW_wit_3_8_2 :
    ∃ ξ : ℕ, 8 = ξ * 8 ∧ 9 + ξ * 3 = 2 * 2 * 3 ∧ ξ * 3 + 8 ≤ 2 * 2 * 3 :=
  (thinW_base 3 8 2 8 6 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp [ta, tb, tc]) (by norm_num)).2

/-! ### Negative control: `M e < f` cannot be dropped.
At `(e,f,M) = (2,5,3)` (`Me = 6 ≥ 5`) the triple `(28,1,5)` decomposes the base `6·71 = 426` with `r = 5 ≥ f`
but `q = 1 ≠ Me = 6`. (Also `(3,5,2)`: `(17,1,5)`.)  The hypothesis `f ≤ 2Me` is not needed (see header). -/

theorem thinW_negctl_decomp :
    (28 : ℕ) * ta 2 5 + 1 * tb 2 5 + 5 * tc 2 5 = 3 * 2 * (3 * 5 ^ 2 - 2 ^ 2) ∧ 5 ≤ 5 ∧ (1 : ℕ) ≠ 3 * 2 := by
  refine ⟨by simp [ta, tb, tc], by norm_num, by norm_num⟩

theorem thinW_negctl_decomp2 :
    (17 : ℕ) * ta 3 5 + 1 * tb 3 5 + 5 * tc 3 5 = 2 * 3 * (3 * 5 ^ 2 - 3 ^ 2) ∧ (1 : ℕ) ≠ 2 * 3 := by
  refine ⟨by simp [ta, tb, tc], by norm_num⟩

#print axioms thinW_base
#print axioms thinW_wit_2_5_2
#print axioms thinW_negctl_decomp

end Erdos634.LaczJunction
