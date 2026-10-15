import Erdos634.BADAlgebra

/-!
# BAD layer L3 witness / control, and layer L4 (arithmetic corollary)  Built on `BADAlgebra.basealpha_div_of_poly`.

* witness: `(e,f)=(1,2)`, `w=6`, `b=3`: the hypothesis `Bdry = tsum` of the core lemma is satisfiable
  (algebraic witness `6 t⁻¹ q + 8 t⁻² p - 4 t⁻² q`, a 3-term combination; this is not the 84-tile
  geometric sum, it only shows the hypothesis is not vacuous and `b ∣ w` holds there).
* control: `(e,f)=(1,3)`, `w=4`, `b=8`: no signed shifted-tile sum equals the boundary.
* L4: the seven instances of the base-α divisibility corollary: `b ∤ w` yet `b ∣ w²`, `N b = w² Q`.
-/

open LaurentPolynomial

namespace BAD

noncomputable section

theorem witness_84 :
    Bdry 1 2 6 = tsum 1 2 [(6, -1, false), (8, -2, true), (-4, -2, false)] := by
  have h : (T 1 : L) * T (-1) = 1 := by rw [← T_add]; simp
  rw [Bdry_eq, tsum_eq]
  congr 1
  have hy : (T (-2) : L) = T (-1) * T (-1) := by rw [← T_add]; norm_num
  simp only [Bq, gsum, gterm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    if_true, Bool.false_eq_true, if_false, hy]
  simp only [map_neg, map_one, map_ofNat, map_mul]
  linear_combination (-12) * h

theorem witness_84_div : ((2 : ℤ) ^ 2 - 1 ^ 2) ∣ 6 := by norm_num

theorem control_34 (l : List (ℤ × ℤ × Bool)) : Bdry 1 3 4 ≠ tsum 1 3 l := by
  intro h
  have := basealpha_div_of_poly 1 3 4 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num [Int.isCoprime_iff_gcd_eq_one]) l h
  norm_num at this

/-- the shared arithmetic: `b ∣ w` and `N b = w² Q` give `N = r² b Q`. -/
theorem N_form (b Q w N : ℤ) (hb : b ≠ 0) (hdiv : b ∣ w) (hN : N * b = w ^ 2 * Q) :
    ∃ r : ℤ, N = r ^ 2 * b * Q := by
  obtain ⟨r, rfl⟩ := hdiv
  refine ⟨r, ?_⟩
  apply mul_right_cancel₀ hb
  rw [hN]; ring

/-- the seven rows `(e, f, w, N)` of `cor:basealphadiv` -/
def rows : List (ℤ × ℤ × ℤ × ℤ) :=
  [(1, 3, 4, 34), (3, 5, 8, 164), (5, 7, 12, 438), (1, 5, 12, 294), (3, 7, 20, 890),
   (1, 7, 12, 291), (7, 9, 8, 226)]

def good (x : ℤ × ℤ × ℤ × ℤ) : Prop :=
  let e := x.1; let f := x.2.1; let w := x.2.2.1; let N := x.2.2.2
  N * (f ^ 2 - e ^ 2) = w ^ 2 * (2 * f ^ 2 - e ^ 2) ∧ (f ^ 2 - e ^ 2) ∣ w ^ 2 ∧
    ¬ (f ^ 2 - e ^ 2) ∣ w ∧ Int.gcd e f = 1 ∧ 0 < e ∧ e < f

instance (x : ℤ × ℤ × ℤ × ℤ) : Decidable (good x) := by unfold good; infer_instance

theorem seven_rows : ∀ x ∈ rows, good x := by decide

end

end BAD
