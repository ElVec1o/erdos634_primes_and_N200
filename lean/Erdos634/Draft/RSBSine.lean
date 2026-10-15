import Mathlib
import Erdos634.Draft.FDDShapes

/-!
# RSB, part 1: sines of the corner types, in tile coordinates.

For a tile `(a,b,c)` with `cos α · c = b + a/2`, `sin α · c = (√3/2) a` (this is the trigonometric relation of the tile, since
`(2b+a)/(2c) = (b + a/2)/c`), the corner type `(m,k)` has angle `mα + kπ/3`, and

  `sin(mα + kπ/3) · c^|m| = (√3/2) · W(m,k)`,   `W(m,k) ∈ ℤ[a,b]`,

where `W` is read off the Eisenstein integer `ω^k (b + aω)^m` (`ω = e^{iπ/3}`; `m < 0` uses the
conjugate `(a+b) - aω`): `ω`-coefficient.  `ratio_table` then proves, for each of the eleven shapes of
`FDDShapes.Shape` in the order of `Shape.triple`, that the sines of its three corner types are in the
ratio of the `sideVec` entries.  All polynomial identities hold WITHOUT using `c² = a²+ab+b²`.
-/

open Real

namespace Erdos634.Draft.RSBSine

/-- Powers of `p + qω` (`ω² = ω − 1`): `(p + qω)^n = P + Qω`, `(P,Q) = eis p q n`. -/
def eis (p q : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => ((eis p q n).1 * p - (eis p q n).2 * q,
              (eis p q n).1 * q + (eis p q n).2 * p + (eis p q n).2 * q)

theorem cos_sin_mul (θ r p q : ℝ) (hc : Real.cos θ * r = p + q / 2)
    (hs : Real.sin θ * r = Real.sqrt 3 / 2 * q) (n : ℕ) :
    Real.cos (n * θ) * r ^ n = (eis p q n).1 + (eis p q n).2 / 2 ∧
    Real.sin (n * θ) * r ^ n = Real.sqrt 3 / 2 * (eis p q n).2 := by
  induction n with
  | zero => simp [eis]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : ((n + 1 : ℕ) : ℝ) * θ = n * θ + θ := by push_cast; ring
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    rw [e, Real.cos_add, Real.sin_add, pow_succ]
    simp only [eis]
    constructor
    · calc (Real.cos (n * θ) * Real.cos θ - Real.sin (n * θ) * Real.sin θ) * (r ^ n * r)
          = (Real.cos (n * θ) * r ^ n) * (Real.cos θ * r)
            - (Real.sin (n * θ) * r ^ n) * (Real.sin θ * r) := by ring
        _ = _ := by
          rw [h1, h2, hc, hs]
          linear_combination (-(eis p q n).2 * q / 4) * h3
    · calc (Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ) * (r ^ n * r)
          = (Real.sin (n * θ) * r ^ n) * (Real.cos θ * r)
            + (Real.cos (n * θ) * r ^ n) * (Real.sin θ * r) := by ring
        _ = _ := by
          rw [h1, h2, hc, hs]
          ring

/-- Coefficient of `ω` in `ω^k (P + Qω)`, `k = 0,1,2,3`. -/
def Wn (p q : ℝ) (n k : ℕ) : ℝ :=
  match k with
  | 0 => (eis p q n).2
  | 1 => (eis p q n).1 + (eis p q n).2
  | 2 => (eis p q n).1
  | _ => -(eis p q n).2

theorem sin_nθ_add (θ r p q : ℝ) (hc : Real.cos θ * r = p + q / 2)
    (hs : Real.sin θ * r = Real.sqrt 3 / 2 * q) (n k : ℕ) (hk : k ≤ 3) :
    Real.sin (n * θ + k * (Real.pi / 3)) * r ^ n = Real.sqrt 3 / 2 * Wn p q n k := by
  obtain ⟨h1, h2⟩ := cos_sin_mul θ r p q hc hs n
  have c3 := Real.cos_pi_div_three
  have s3 := Real.sin_pi_div_three
  have c23 : Real.cos (2 * (Real.pi / 3)) = -(1 / 2) := by
    rw [show 2 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, c3]
  have s23 : Real.sin (2 * (Real.pi / 3)) = Real.sqrt 3 / 2 := by
    rw [show 2 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, s3]
  have cpi : Real.cos (3 * (Real.pi / 3)) = -1 := by
    rw [show 3 * (Real.pi / 3) = Real.pi by ring, Real.cos_pi]
  have spi : Real.sin (3 * (Real.pi / 3)) = 0 := by
    rw [show 3 * (Real.pi / 3) = Real.pi by ring, Real.sin_pi]
  interval_cases k
  · simp only [Wn, Nat.cast_zero, zero_mul, add_zero]; exact h2
  · simp only [Wn, Nat.cast_one, one_mul, Real.sin_add, c3, s3]
    linear_combination (1 / 2) * h2 + (Real.sqrt 3 / 2) * h1
  · simp only [Wn, Nat.cast_ofNat, Real.sin_add, c23, s23]
    linear_combination (-(1 / 2)) * h2 + (Real.sqrt 3 / 2) * h1
  · simp only [Wn, Nat.cast_ofNat, Real.sin_add, cpi, spi]
    linear_combination (-1) * h2

/-- `W(m,k)`: nonnegative `m` uses `b + aω`, negative `m` uses the conjugate `(a+b) − aω`. -/
def Wz (a b : ℝ) (m k : ℤ) : ℝ :=
  if 0 ≤ m then Wn b a m.toNat k.toNat else Wn (a + b) (-a) m.natAbs k.toNat

/-- **Sine of a corner type.**  With `cos α · c = b + a/2` and `sin α · c = (√3/2) a`, for `0 ≤ k ≤ 3`:
`sin(mα + kπ/3) · c^|m| = (√3/2) · W(m,k)`. -/
theorem sin_corner (α a b c : ℝ) (hcos : Real.cos α * c = b + a / 2)
    (hsin : Real.sin α * c = Real.sqrt 3 / 2 * a) (m k : ℤ) (hk0 : 0 ≤ k) (hk3 : k ≤ 3) :
    Real.sin (m * α + k * (Real.pi / 3)) * c ^ m.natAbs = Real.sqrt 3 / 2 * Wz a b m k := by
  have hk : (k.toNat : ℝ) = (k : ℝ) := by
    have : ((k.toNat : ℤ) : ℝ) = (k : ℝ) := by rw [Int.toNat_of_nonneg hk0]
    exact_mod_cast this
  have hk3' : k.toNat ≤ 3 := by omega
  by_cases hm : 0 ≤ m
  · have hmm : (m.toNat : ℝ) = (m : ℝ) := by
      have : ((m.toNat : ℤ) : ℝ) = (m : ℝ) := by rw [Int.toNat_of_nonneg hm]
      exact_mod_cast this
    have := sin_nθ_add α c b a hcos hsin m.toNat k.toNat hk3'
    rw [hmm, hk] at this
    have hna : m.natAbs = m.toNat := by omega
    rw [hna]; simp only [Wz, if_pos hm]; exact this
  · have hneg : m.natAbs = (-m).toNat := by omega
    have hmm : ((-m).toNat : ℝ) = -(m : ℝ) := by
      have : (((-m).toNat : ℤ) : ℝ) = -(m : ℝ) := by
        rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
      exact_mod_cast this
    have hc' : Real.cos (-α) * c = (a + b) + (-a) / 2 := by rw [Real.cos_neg]; linarith
    have hs' : Real.sin (-α) * c = Real.sqrt 3 / 2 * (-a) := by rw [Real.sin_neg]; linarith
    have := sin_nθ_add (-α) c (a + b) (-a) hc' hs' (-m).toNat k.toNat hk3'
    rw [hmm, hk, ← hneg, neg_mul_neg] at this
    simp only [Wz, if_neg hm]
    exact this

/-! ## The ordered corner triples and positional side vectors of the table -/

end Erdos634.Draft.RSBSine

namespace Erdos634.Draft.FDDShapes

/-- The corner-type triple of a shape, in the order matching `Shape.sideVec` (the `j`-th entry of
`sideVec` is proportional to the sine of the `j`-th corner, i.e. is the side opposite it). -/
def Shape.triple : Shape → Fin 3 → Corner
  | .equilateral => ![(0, 1), (0, 1), (0, 1)]
  | .isoAlpha => ![(1, 0), (1, 0), (-2, 3)]
  | .isoBeta => ![(-1, 1), (-1, 1), (2, 1)]
  | .F1 => ![(1, 0), (0, 1), (-1, 2)]
  | .F1' => ![(-1, 1), (0, 1), (1, 1)]
  | .F2 => ![(2, 0), (-2, 2), (0, 1)]
  | .F3 => ![(1, 0), (2, 0), (-3, 3)]
  | .F3' => ![(-1, 1), (-2, 2), (3, 0)]
  | .F4 => ![(1, 0), (-2, 2), (1, 1)]
  | .F4' => ![(-1, 1), (2, 0), (-1, 2)]
  | .tileSimilar => ![(1, 0), (-1, 1), (0, 2)]

/-- The positional side vector. -/
def Shape.sideV (s : Shape) (a b c : ℕ) : Fin 3 → ℕ :=
  ![(s.sideVec a b c).1, (s.sideVec a b c).2.1, (s.sideVec a b c).2.2]

end Erdos634.Draft.FDDShapes

namespace Erdos634.Draft.RSBSine

open Erdos634.Draft.FDDShapes

theorem triple_corners : ∀ s : Shape,
    s.corners = {(s.triple 0), (s.triple 1), (s.triple 2)} := by decide

theorem triple_realizable : ∀ s : Shape, ∀ j, Realizable (s.triple j) ∧ 0 ≤ (s.triple j).2 ∧
    (s.triple j).2 ≤ 3 := by
  intro s j; revert s j; decide

/-- **The sines of the corner types of every shape are in the ratio of its side vector.**
`W_j · c^{|m_0|} · D_0 = W_0 · c^{|m_j|} · D_j`, an identity in `ℤ[a,b,c]` (no use of the tile
relation). -/
theorem ratio_table (s : Shape) (a b c : ℕ) (j : Fin 3) :
    Wz a b (s.triple j).1 (s.triple j).2 * (c : ℝ) ^ (s.triple 0).1.natAbs * (s.sideV a b c 0 : ℝ)
      = Wz a b (s.triple 0).1 (s.triple 0).2 * (c : ℝ) ^ (s.triple j).1.natAbs
          * (s.sideV a b c j : ℝ) := by
  fin_cases j
  · rfl
  all_goals
    cases s <;>
    simp [Shape.triple, Shape.sideV, Shape.sideVec, Wz, Wn, eis] <;> ring

end Erdos634.Draft.RSBSine

#print axioms Erdos634.Draft.RSBSine.sin_corner
#print axioms Erdos634.Draft.RSBSine.ratio_table
#print axioms Erdos634.Draft.RSBSine.triple_corners
#print axioms Erdos634.Draft.RSBSine.triple_realizable
