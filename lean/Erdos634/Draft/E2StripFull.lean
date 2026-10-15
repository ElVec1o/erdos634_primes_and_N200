/-
Draft/E2StripFull.lean: no brick interior at `e ≥ 2`.

A *brick interior* of width `s` is a tiling of the `s × f b` grid rectangle by `a × b` bricks in either orientation
(`a = e f`, `b = f² − e²`); admissible widths satisfy `s ≡ −e³ (mod e f)`.

* `no_brick_interior`: for coprime `2 ≤ e < f` and `e f ∣ s + e³` there is none (`DeBruijnKlarner.brick_dvd`, then
  `e f ∣ s` gives `f ∣ e³` and `e f ∣ f b` gives `e ∣ f²`, both impossible).
* `slant_sq`, `cos_theta`, `cos_gamma`, `half_angle`: the identities behind "the slant has length `f b`" and
  "`cos θ = e/(2f) = sin(α/2)`, i.e. `θ = α + β`" (law of cosines for the tile `(ef, f² − e², f²)`).

Five searched strips are treated in `E2StripInstances.e2strip_instances` (kernel-checked certificates).  No sorry, no native_decide.
-/
import Erdos634.Draft.DeBruijnKlarner

namespace Erdos634.Draft.E2StripFull

open Erdos634.Draft.DeBruijnKlarner

/-- **No brick interior at `e ≥ 2`.** -/
theorem no_brick_interior {e f s : ℕ} (he : 2 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hs : e * f ∣ s + e ^ 3) {ι : Type*} (S : Finset ι) (x₀ y₀ w h : ι → ℕ)
    (hshape : ∀ i ∈ S, (w i = e * f ∧ h i = f ^ 2 - e ^ 2) ∨ (w i = f ^ 2 - e ^ 2 ∧ h i = e * f))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (box (x₀ i) (y₀ i) (w i) (h i)) (box (x₀ j) (y₀ j) (w j) (h j)))
    (hcover : S.biUnion (fun i => box (x₀ i) (y₀ i) (w i) (h i)) = box 0 0 s (f * (f ^ 2 - e ^ 2))) :
    False := by
  have hf0 : 0 < f := by omega
  have ha : 0 < e * f := Nat.mul_pos (by omega) hf0
  rcases brick_dvd ha S x₀ y₀ w h hshape hdisj hcover with h1 | h1
  · -- `e f ∣ s`, hence `e f ∣ e³`, hence `f ∣ e³`
    have h2 : e * f ∣ e ^ 3 := (Nat.dvd_add_right h1).mp hs
    have h3 : f ∣ e ^ 3 := dvd_trans (dvd_mul_left f e) h2
    have h4 : f = 1 := (Nat.Coprime.pow_right 3 hcop.symm).eq_one_of_dvd h3
    omega
  · -- `e f ∣ f (f² − e²)`, hence `e ∣ f² − e²`, hence `e ∣ f²`
    have h2 : f * e ∣ f * (f ^ 2 - e ^ 2) := by rwa [mul_comm f e]
    have h3 : e ∣ f ^ 2 - e ^ 2 := Nat.dvd_of_mul_dvd_mul_left hf0 h2
    have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
    have h4 : e ∣ f ^ 2 - e ^ 2 + e ^ 2 := dvd_add h3 (dvd_pow_self e (by norm_num))
    rw [Nat.sub_add_cancel hle] at h4
    have h5 : e = 1 := (Nat.Coprime.pow_right 2 hcop).eq_one_of_dvd h4
    omega

/-- the slant `X₁ w − f a u` of the strip has length `f b`: with `|u| = |w| = 1` and
`u · w = cos β = e (3f² − e²)/(2f³)`, its squared length `X₁² + (f a)² − 2 X₁ (f a) cos β` is `(f b)²`
(`X₁ = f³`, `a = e f`, `b = f² − e²`) -/
theorem slant_sq (e f : ℝ) (hf : f ≠ 0) :
    (f ^ 3) ^ 2 + (f * (e * f)) ^ 2 - 2 * f ^ 3 * (f * (e * f)) * (e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3))
      = (f * (f ^ 2 - e ^ 2)) ^ 2 := by
  field_simp
  ring

/-- the angle `θ` between the base direction `u` and the slant: `cos θ = e/(2f)` -/
theorem cos_theta (e f : ℝ) (hf : f ≠ 0) (hb : f ^ 2 - e ^ 2 ≠ 0) :
    (f ^ 3 * (e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3)) - f * (e * f)) / (f * (f ^ 2 - e ^ 2)) = e / (2 * f) := by
  field_simp
  ring

/-- `cos γ = −e/(2f)` for the tile `(a, b, c) = (ef, f² − e², f²)` (law of cosines, `γ` opposite `c`); so
`cos (α + β) = −cos γ = e/(2f)` -/
theorem cos_gamma (e f : ℝ) (he : e ≠ 0) (hf : f ≠ 0) (hb : f ^ 2 - e ^ 2 ≠ 0) :
    ((e * f) ^ 2 + (f ^ 2 - e ^ 2) ^ 2 - (f ^ 2) ^ 2) / (2 * (e * f) * (f ^ 2 - e ^ 2)) = -(e / (2 * f)) := by
  field_simp
  ring

/-- `sin² (α/2) = (1 − cos α)/2 = (e/(2f))²` (law of cosines, `α` opposite `a`) -/
theorem half_angle (e f : ℝ) (hf : f ≠ 0) (hb : f ^ 2 - e ^ 2 ≠ 0) :
    (1 - ((f ^ 2 - e ^ 2) ^ 2 + (f ^ 2) ^ 2 - (e * f) ^ 2) / (2 * (f ^ 2 - e ^ 2) * f ^ 2)) / 2
      = (e / (2 * f)) ^ 2 := by
  field_simp
  ring

end Erdos634.Draft.E2StripFull

#print axioms Erdos634.Draft.E2StripFull.no_brick_interior
