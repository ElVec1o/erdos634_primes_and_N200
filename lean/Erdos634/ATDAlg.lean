import Erdos634.BADAlgebra

/-!
# Atom divisibility, layer A: the algebraic core  Pure algebra over `ℤ[T;T⁻¹]`, no geometry.
Tile `(ef, f²-e², f²)`, `Φ = f t² - e t + f`.  The atom (isosceles, base angles `α+β`, legs `X = f μ`,
base `Y = e μ`) has boundary polynomial `Ba = e μ - f μ (t + t⁻¹)`, which is exactly `-μ t⁻¹ Φ`
(`Ba_eq`).  If `Ba` is a signed sum of shifted tile polynomials, then `(f²-e²) ∣ μ`.
-/

open LaurentPolynomial

namespace ATD

noncomputable section
open BAD

/-- boundary polynomial of the atom target with free `(X, Y)`: `Y - X (t + t⁻¹)`. -/
def BaXY (X Y : ℤ) : L := C Y - C X * T 1 - C X * T (-1)

/-- the atom boundary polynomial `e μ - f μ (t + t⁻¹)`. -/
def Ba (e f μ : ℤ) : L := BaXY (f * μ) (e * μ)

theorem Ba_eq (e f μ : ℤ) : Ba e f μ = Phi e f * (-(C μ * T (-1))) := by
  have h2 : (T 1 : L) * T (-1) = 1 := by rw [← T_add]; simp
  have hx : (T 2 : L) = T 1 * T 1 := by rw [← T_add]; norm_num
  unfold Ba BaXY Phi
  simp only [map_mul, map_sub, map_neg]
  rw [hx]
  linear_combination (C f * C μ * T 1 - C e * C μ) * h2

theorem atomdiv_of_poly (e f μ : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcb : IsCoprime e (f ^ 2 - e ^ 2))
    (l : List (ℤ × ℤ × Bool)) (h : Ba e f μ = tsum e f l) : (f ^ 2 - e ^ 2) ∣ μ := by
  have hG : -(C μ * T (-1) : L) = gsum e f l := by
    apply mul_left_cancel₀ (Phi_ne_zero e f h0 hef)
    rw [← Ba_eq, h, tsum_eq]
  obtain ⟨u, v, huv⟩ := hcb
  set b : ℤ := f ^ 2 - e ^ 2 with hbdef
  set n : ℕ := b.natAbs with hn
  have hb0 : ((b : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b n).2 (Int.natAbs_dvd_self)
  have hF2 : ((f : ℤ) : ZMod n) ^ 2 = ((e : ℤ) : ZMod n) ^ 2 := by
    have := hb0
    rw [hbdef] at this
    push_cast at this
    exact sub_eq_zero.1 this
  have hEU : ((e : ℤ) : ZMod n) * (u : ZMod n) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod n)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, hb0, mul_zero, add_zero] at this
    rw [mul_comm]; exact this
  set τ : ZMod n := -((f : ℤ) : ZMod n) * (u : ZMod n) with hτ
  have hττ : τ * τ = 1 := by
    have : τ * τ = (((f : ℤ) : ZMod n) ^ 2) * (u : ZMod n) ^ 2 := by rw [hτ]; ring
    rw [this, hF2]
    calc ((e : ℤ) : ZMod n) ^ 2 * (u : ZMod n) ^ 2 = (((e : ℤ) : ZMod n) * (u : ZMod n)) ^ 2 := by ring
      _ = 1 := by rw [hEU]; norm_num
  let τu : (ZMod n)ˣ := ⟨τ, τ, hττ, hττ⟩
  have hinv : τu⁻¹ = τu := inv_eq_of_mul_eq_one_right (Units.ext hττ)
  have hτe : ((e : ℤ) : ZMod n) * τ + ((f : ℤ) : ZMod n) = 0 := by
    rw [hτ]
    calc _ = ((f : ℤ) : ZMod n) * (1 - ((e : ℤ) : ZMod n) * (u : ZMod n)) := by ring
      _ = 0 := by rw [hEU]; ring
  have hτf : ((f : ℤ) : ZMod n) * τ + ((e : ℤ) : ZMod n) = 0 := by
    rw [hτ]
    calc _ = ((e : ℤ) : ZMod n) * (1 - ((e : ℤ) : ZMod n) * (u : ZMod n)) +
        (((e : ℤ) : ZMod n) ^ 2 - ((f : ℤ) : ZMod n) ^ 2) * (u : ZMod n) := by ring
      _ = 0 := by rw [hEU, hF2]; ring
  have hφe : LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (C e * T 1 + C f) = 0 := by
    simpa [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, τu] using hτe
  have hφf : LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (C f * T 1 + C e) = 0 := by
    simpa [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, τu] using hτf
  have hgs : ∀ l' : List (ℤ × ℤ × Bool),
      LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (gsum e f l') = 0 := by
    intro l'
    induction l' with
    | nil => simp [gsum]
    | cons x l' ih =>
      simp only [gsum, List.map_cons, List.sum_cons, map_add] at ih ⊢
      rw [ih, add_zero]
      unfold gterm
      rw [map_mul]
      split_ifs
      · rw [hφe, mul_zero]
      · rw [hφf, mul_zero]
  have hL : LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (-(C μ * T (-1) : L))
      = -((μ : ZMod n) * τ) := by
    simp only [map_neg, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
      zpow_neg, zpow_one, hinv]
    simp [τu]
  have key : ((μ : ℤ) : ZMod n) = 0 := by
    have h1 : -((μ : ZMod n) * τ) = 0 := by rw [← hL, hG, hgs]
    have h2 : (μ : ZMod n) = (μ : ZMod n) * (τ * τ) := by rw [hττ, mul_one]
    rw [h2, ← mul_assoc]
    have h3 : (μ : ZMod n) * τ = 0 := neg_eq_zero.1 h1
    rw [h3, zero_mul]
  have hd : (n : ℤ) ∣ μ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 key
  exact Int.natAbs_dvd_natAbs.1 (Int.natCast_dvd.1 hd)

/-- sanity (witness): `A_4` at `(1,2)` has `μ = 12`, and `3 ∣ 12`; the polynomial identity holds. -/
theorem Ba_eq_12 : Ba 1 2 12 = Phi 1 2 * (-(C 12 * T (-1))) := Ba_eq 1 2 12

end

end ATD

#print axioms ATD.atomdiv_of_poly
