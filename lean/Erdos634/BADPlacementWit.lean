import Erdos634.BADPlacementGeo

/-!
# BAD layer L1: packaged lemma, witnesses, control  See `BADPlacement`, `BADPlacementGeo`.
-/

open LaurentPolynomial

namespace BAD

noncomputable section

section Pack
variable {ζ ω : ℂ} (hζ : ζ ≠ 0) (hω : ω ≠ 0) (hrel : ζ ^ 3 * ω ^ 2 = -1)
  (hcζ : (starRingEnd ℂ) ζ = ζ⁻¹) (hcω : (starRingEnd ℂ) ω = ω⁻¹)

include hζ hω in
/-- L1, rotated copy: the three ccw side vectors have coordinates `(i,j)`, `(i+3,j+1)`, `(i-2,j-2)` and the
boundary polynomial is `± t^s p`. -/
theorem placed_rot (e f i j : ℤ) (A B D v : ℂ) (h1 : B - A = ((f ^ 2 : ℤ) : ℂ))
    (h2 : D - B = ((e * f : ℤ) : ℂ) * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - D = ((f ^ 2 - e ^ 2 : ℤ) : ℂ) * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    ((HasCoord ζ ω ((ζ ^ i * ω ^ j * B + v) - (ζ ^ i * ω ^ j * A + v)) (f ^ 2, i, j)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * D + v) - (ζ ^ i * ω ^ j * B + v)) (e * f, i + 3, j + 1)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * A + v) - (ζ ^ i * ω ^ j * D + v)) (f ^ 2 - e ^ 2, i - 2, j - 2))) ∧
    bp [(f ^ 2, i, j), (e * f, i + 3, j + 1), (f ^ 2 - e ^ 2, i - 2, j - 2)]
      = C (ee i j) * T (kk i j) * pTile e f := by
  obtain ⟨a, b, c⟩ := rot_sides hζ hω (e * f) (f ^ 2 - e ^ 2) (f ^ 2) i j A B D v h1 h2 h3
  exact ⟨⟨b, a, c⟩, bp_rot e f i j⟩

include hζ hω hrel hcζ hcω in
/-- L1, reflected copy: boundary polynomial `-ε t^{k-3} q`. -/
theorem placed_mir (e f i j : ℤ) (A B D v : ℂ) (h1 : B - A = ((f ^ 2 : ℤ) : ℂ))
    (h2 : D - B = ((e * f : ℤ) : ℂ) * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - D = ((f ^ 2 - e ^ 2 : ℤ) : ℂ) * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    ((HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) D + v) - (ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v))
        (f ^ 2 - e ^ 2, i + 5, j + 4)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v) - (ζ ^ i * ω ^ j * (starRingEnd ℂ) D + v))
        (e * f, i, j + 1)) ∧
     (HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v) - (ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v))
        (f ^ 2, i + 3, j + 2))) ∧
    bp [(f ^ 2 - e ^ 2, i + 5, j + 4), (e * f, i, j + 1), (f ^ 2, i + 3, j + 2)]
      = C (-ee i j) * T (kk i j - 3) * qTile e f := by
  obtain ⟨a, b, c⟩ := mir_sides hζ hω hrel hcζ hcω (e * f) (f ^ 2 - e ^ 2) (f ^ 2) i j A B D v h1 h2 h3
  exact ⟨⟨a, b, c⟩, bp_mir e f i j⟩
end Pack

/-- witness, `(e,f) = (1,2)` tile `(2,3,4)`, rotation `(1,-2)`: `-t^8 (4 + 3t² + 2t³)`. -/
theorem wit_rot : bp [(2 ^ 2, 1, -2), (1 * 2, 1 + 3, -2 + 1), (2 ^ 2 - 1 ^ 2, 1 - 2, -2 - 2)]
    = -(4 * T 8 + 3 * T 10 + 2 * T 11) := by
  have h : ee 1 (-2) = -1 := by decide
  have hk : kk 1 (-2) = 8 := by norm_num [kk]
  have e1 : (T 8 : L) * T 2 = T 10 := by rw [← T_add]; norm_num
  have e2 : (T 8 : L) * T 3 = T 11 := by rw [← T_add]; norm_num
  rw [bp_rot, ← p_form, h, hk]
  norm_num
  linear_combination (-(3 : L)) * e1 + (-(2 : L)) * e2

/-- witness, mirrored copy, rotation `(2,1)`: `t^{-2} q = 4t + 3t^{-1} + 2t^{-2}`. -/
theorem wit_mir : bp [(2 ^ 2 - 1 ^ 2, 2 + 5, 1 + 4), (1 * 2, 2, 1 + 1), (2 ^ 2, 2 + 3, 1 + 2)]
    = 3 * T (-1) + 2 * T (-2) + 4 * T 1 := by
  have h : ee 2 1 = -1 := by decide
  have hk : kk 2 1 - 3 = -2 := by norm_num [kk]
  have f1 : (T (-2) : L) * T 3 = T 1 := by rw [← T_add]; norm_num
  have f2 : (T (-2) : L) * T 1 = T (-1) := by rw [← T_add]; norm_num
  rw [bp_mir, ← q_form, h, hk]
  norm_num
  linear_combination (4 : L) * f1 + (3 : L) * f2

/-- control: a tile of the wrong shape (sides `4,2,4` instead of `4,2,3`, same directions) is not
`σ t^s p` or `σ t^s q` for any integer `σ` and `s` (value at `t = 1` is `10`, but `p(1) = q(1) = 9`). -/
theorem control_wrong_shape :
    ¬ ∃ σ s : ℤ, (bp [(4, 0, 0), (2, 3, 1), (4, -2, -2)] = C σ * T s * pTile 1 2 ∨
                  bp [(4, 0, 0), (2, 3, 1), (4, -2, -2)] = C σ * T s * qTile 1 2) := by
  rintro ⟨σ, s, h⟩
  have hb : bp [(4, 0, 0), (2, 3, 1), (4, -2, -2)] = 4 + 2 * T 3 + 4 * T 2 := by
    simp [bp, sideTerm, kk, ee00, ee32, ee22]; ring
  rcases h with h | h
  · have := congrArg (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (1 : ℤˣ)) h
    rw [hb] at this
    simp [pTile, Phi, map_ofNat (LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ))] at this
    omega
  · have := congrArg (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (1 : ℤˣ)) h
    rw [hb] at this
    simp [qTile, Phi, map_ofNat (LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ))] at this
    omega

end

end BAD
