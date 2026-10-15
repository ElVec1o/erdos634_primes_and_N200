import Erdos634.BADPlacement

/-!
# BAD layer L1 (geometric link, witness, control)  Links complex-plane placements of the model tile to the directed-side lists
of `BADPlacement` (`bp_rot`, `bp_mir`), proves the polynomial is `± t^s p` / `± t^s q`, gives a
numeric witness `(e,f)=(1,2)` and a control (wrong tile shape).

Setting: `ζ = e^{iα}`, `ω = e^{iβ}` abstractly: nonzero, `ζ³ω² = -1`, unit modulus (`conj ζ = ζ⁻¹`).
Model tile `A,B,C` (ccw): `B-A = c`, `C-B = a ζ³ ω`, `A-C = b ζ⁻² ω⁻²`.
Rotation placement `z ↦ ζ^i ω^j z + v`; reflected placement `z ↦ ζ^i ω^j conj z + v`
(its ccw order is `A'→C'→B'`).
-/

open LaurentPolynomial

namespace BAD

noncomputable section

section Geo
variable (ζ ω : ℂ)

/-- the side vector `z` is `len · ζ^i ω^j`. -/
def HasCoord (z : ℂ) (x : Side) : Prop := z = (x.1 : ℂ) * (ζ ^ x.2.1 * ω ^ x.2.2)

variable {ζ ω}
variable (hζ : ζ ≠ 0) (hω : ω ≠ 0) (hrel : ζ ^ 3 * ω ^ 2 = -1)
  (hcζ : (starRingEnd ℂ) ζ = ζ⁻¹) (hcω : (starRingEnd ℂ) ω = ω⁻¹)

include hζ hω in
theorem rot_sides (a b c i j : ℤ) (A B C v : ℂ) (h1 : B - A = c) (h2 : C - B = a * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - C = b * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    HasCoord ζ ω ((ζ ^ i * ω ^ j * C + v) - (ζ ^ i * ω ^ j * B + v)) (a, i + 3, j + 1) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * B + v) - (ζ ^ i * ω ^ j * A + v)) (c, i, j) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * A + v) - (ζ ^ i * ω ^ j * C + v)) (b, i - 2, j - 2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold HasCoord
    rw [show ζ ^ i * ω ^ j * C + v - (ζ ^ i * ω ^ j * B + v) = ζ ^ i * ω ^ j * (C - B) by ring, h2]
    simp only [zpow_add₀ hζ, zpow_add₀ hω]; ring
  · unfold HasCoord
    rw [show ζ ^ i * ω ^ j * B + v - (ζ ^ i * ω ^ j * A + v) = ζ ^ i * ω ^ j * (B - A) by ring, h1]
    ring
  · unfold HasCoord
    rw [show ζ ^ i * ω ^ j * A + v - (ζ ^ i * ω ^ j * C + v) = ζ ^ i * ω ^ j * (A - C) by ring, h3]
    simp only [sub_eq_add_neg, zpow_add₀ hζ, zpow_add₀ hω]; ring

include hζ hω hrel hcζ hcω in
theorem mir_sides (a b c i j : ℤ) (A B C v : ℂ) (h1 : B - A = c) (h2 : C - B = a * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ)))
    (h3 : A - C = b * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) :
    HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) C + v) - (ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v)) (b, i + 5, j + 4) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v) - (ζ ^ i * ω ^ j * (starRingEnd ℂ) C + v)) (a, i, j + 1) ∧
    HasCoord ζ ω ((ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v) - (ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v)) (c, i + 3, j + 2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold HasCoord
    have hh : C - A = -(b * (ζ ^ (-2 : ℤ) * ω ^ (-2 : ℤ))) := by rw [← neg_sub, h3]
    rw [show ζ ^ i * ω ^ j * (starRingEnd ℂ) C + v - (ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v)
      = ζ ^ i * ω ^ j * ((starRingEnd ℂ) C - (starRingEnd ℂ) A) by ring, ← map_sub, hh]
    simp only [map_neg, map_mul, map_zpow₀, hcζ, hcω, map_intCast]
    simp only [zpow_add₀ hζ, zpow_add₀ hω, zpow_neg, inv_inv, zpow_ofNat, inv_pow]
    linear_combination (-((b : ℂ) * ζ ^ i * ω ^ j * ζ ^ 2 * ω ^ 2)) * hrel
  · unfold HasCoord
    have hh : B - C = -(a * (ζ ^ (3 : ℤ) * ω ^ (1 : ℤ))) := by rw [← neg_sub, h2]
    rw [show ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v - (ζ ^ i * ω ^ j * (starRingEnd ℂ) C + v)
      = ζ ^ i * ω ^ j * ((starRingEnd ℂ) B - (starRingEnd ℂ) C) by ring, ← map_sub, hh]
    simp only [map_neg, map_mul, map_zpow₀, hcζ, hcω, map_intCast]
    simp only [zpow_add₀ hζ, zpow_add₀ hω, zpow_neg, inv_inv, zpow_ofNat, zpow_one, inv_pow]
    field_simp
    linear_combination (-(a : ℂ)) * hrel
  · unfold HasCoord
    have hh : A - B = -(c : ℂ) := by rw [← neg_sub, h1]
    rw [show ζ ^ i * ω ^ j * (starRingEnd ℂ) A + v - (ζ ^ i * ω ^ j * (starRingEnd ℂ) B + v)
      = ζ ^ i * ω ^ j * ((starRingEnd ℂ) A - (starRingEnd ℂ) B) by ring, ← map_sub, hh]
    simp only [map_neg, map_intCast, zpow_add₀ hζ, zpow_add₀ hω, zpow_ofNat]
    linear_combination (-((c : ℂ) * ζ ^ i * ω ^ j)) * hrel
end Geo

end

end BAD
