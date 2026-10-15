import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Brick-interior obstruction for e ≥ 2 (arithmetic kernel)

For the base-β tile `(a,b,c) = (ef, f²−e², f²)` with `e ≥ 2`,
the de Bruijn–Klarner brick criterion for a strip tiling is never satisfied.

The strip (in the sheared basis) is an `s × fb` rectangle tiled by `ef × b` bricks.
The criterion requires `ef ∣ fb` OR `ef ∣ s` (for admissible `s ≡ −e³ mod ef`).

**Neither branch can hold:**

* `ef ∣ f(f²−e²)` cancels f to give `e ∣ f²−e²`, hence `e ∣ f²`. But `IsCoprime e f`
  gives `IsCoprime e (f²)`; then `e ∣ f²` forces `e ∣ 1`, contradicting `e ≥ 2`.

* `ef ∣ e³` gives `f ∣ e³`. But `IsCoprime e f` gives `IsCoprime f (e³)`; then
  `f ∣ e³` forces `f ∣ 1`, contradicting `f ≥ 3`.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.E2StripArith

private theorem dvd_one_of_coprime_dvd {e x : ℤ}
    (hco : IsCoprime e x) (hdvd : e ∣ x) : e ∣ 1 := by
  obtain ⟨u, v, huv⟩ := hco
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨u + v * k,
    calc 1 = u * e + v * x       := huv.symm
      _ = u * e + v * (e * k)    := by rw [hk]
      _ = e * (u + v * k)        := by ring⟩

/-- Key fact 1: e ≥ 2, IsCoprime e f → e ∤ f². Closes the ef∣fb branch of rem:e2strip. -/
theorem coprime_ge2_not_dvd_sq (e f : ℤ) (he : 2 ≤ e) (hco : IsCoprime e f) :
    ¬ (e ∣ f ^ 2) := by
  intro hdvd
  have hco2 : IsCoprime e (f ^ 2) := hco.pow_right
  exact absurd (Int.le_of_dvd one_pos (dvd_one_of_coprime_dvd hco2 hdvd)) (by omega)

/-- Key fact 2: f ≥ 2, IsCoprime e f → f ∤ e³. Closes the ef∣e³ branch of rem:e2strip. -/
theorem coprime_f_not_dvd_ecube (e f : ℤ) (hf : 2 ≤ f) (hco : IsCoprime e f) :
    ¬ (f ∣ e ^ 3) := by
  intro hdvd
  have hco3 : IsCoprime f (e ^ 3) := hco.symm.pow_right
  exact absurd (Int.le_of_dvd one_pos (dvd_one_of_coprime_dvd hco3 hdvd)) (by omega)

/-- rem:e2strip, branch 1: ef ∤ f(f²−e²) for e ≥ 2, f > 0, IsCoprime e f. -/
theorem e2strip_ef_not_dvd_fb (e f : ℤ) (he : 2 ≤ e) (hf : 0 < f)
    (hco : IsCoprime e f) :
    ¬ (e * f ∣ f * (f ^ 2 - e ^ 2)) := by
  intro hdvd
  -- f * e ∣ f * (f²-e²) → e ∣ (f²-e²)
  rw [mul_comm e f] at hdvd
  have he_dvd_diff : e ∣ f ^ 2 - e ^ 2 :=
    (mul_dvd_mul_iff_left (ne_of_gt hf)).mp hdvd
  -- e ∣ (f²-e²) and e ∣ e² → e ∣ (f²-e²)+e² = f²
  have he_dvd_fsq : e ∣ f ^ 2 := by
    have h := dvd_add he_dvd_diff (dvd_pow_self e (by norm_num : 2 ≠ 0))
    rwa [sub_add_cancel] at h
  exact coprime_ge2_not_dvd_sq e f he hco he_dvd_fsq

/-- rem:e2strip, branch 2: ef ∤ e³ for e ≥ 2, f ≥ 3, IsCoprime e f. -/
theorem e2strip_ef_not_dvd_ecube (e f : ℤ) (he : 2 ≤ e) (hf : 3 ≤ f)
    (hco : IsCoprime e f) :
    ¬ (e * f ∣ e ^ 3) := by
  intro hdvd
  exact coprime_f_not_dvd_ecube e f (by omega) hco (dvd_trans (dvd_mul_left f e) hdvd)

/-- Combined statement: both obstructions hold simultaneously. -/
theorem e2strip_no_brick_interior (e f : ℤ) (he : 2 ≤ e) (hf : 3 ≤ f)
    (hco : IsCoprime e f) :
    ¬ (e * f ∣ f * (f ^ 2 - e ^ 2)) ∧ ¬ (e * f ∣ e ^ 3) :=
  ⟨e2strip_ef_not_dvd_fb e f he (by omega) hco,
   e2strip_ef_not_dvd_ecube e f he hf hco⟩

/-- Non-vacuity: at (e,f) = (2,3), tile (6,5,9): 6 ∤ 3·5=15 and 6 ∤ 8. -/
theorem e2strip_witness_23 :
    ¬ ((2 : ℤ) * 3 ∣ 3 * (3 ^ 2 - 2 ^ 2)) ∧ ¬ ((2 : ℤ) * 3 ∣ 2 ^ 3) :=
  ⟨by decide, by decide⟩

#print axioms coprime_ge2_not_dvd_sq
#print axioms coprime_f_not_dvd_ecube
#print axioms e2strip_ef_not_dvd_fb
#print axioms e2strip_ef_not_dvd_ecube
#print axioms e2strip_no_brick_interior
#print axioms e2strip_witness_23

end Erdos634.Draft.E2StripArith
