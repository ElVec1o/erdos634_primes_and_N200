-- Draft/InterfaceFloorSharp.lean — the relation floor `f·min(a,b)` is sharp at EVERY member.
-- `InterfaceFloor.floor_attained` (v₁ = (f,0,−e), one-sided length f·a) attains the floor only when a ≤ b.
-- When a > b, v₁ does not attain it: at (e,f) = (5,6): a = 30, b = 11, floor 66, v₁ = (6,0,−5) has
-- one-sided length 180, while v₁ − v₂ = (f−e, −f, f−e) = (1,−6,1) has 30 + 36 = 66 = f·b.
-- This module proves the sharp form of the statement.
import Erdos634.InterfaceFloor

namespace Erdos634.InterfaceFloor

/-- `v₁ − v₂ = (f−e, −f, f−e)` is a relation: `(f−e)(ef + f²) = f(f²−e²)`. -/
theorem v12_relation (e f : ℤ) :
    (f - e) * (e * f) + (-f) * (f ^ 2 - e ^ 2) + (f - e) * f ^ 2 = 0 := by ring

/-- `(f−e, −f, f−e)` is nonzero. -/
theorem v12_nonzero (e f : ℤ) (hef : e < f) :
    ¬ (f - e = 0 ∧ -f = 0 ∧ f - e = 0) := by
  rintro ⟨h, -, -⟩; omega

/-- One-sided length of `v₁ − v₂`: its positive side is `f−e` `a`-edges and `f−e` `c`-edges, of
total length `f·b`, so it attains `f·b` at every member. -/
theorem floor_attained_b (e f : ℤ) (he : 0 < e) (hef : e < f) :
    oneSided (f - e) (-f) (f - e) (e * f) (f ^ 2 - e ^ 2) (f ^ 2) = f * (f ^ 2 - e ^ 2) := by
  unfold oneSided
  have h1 : max (f - e) 0 = f - e := max_eq_left (by omega)
  have h2 : max (-f) 0 = 0 := max_eq_right (by omega)
  rw [h1, h2]; ring

/-- `v₁` attains the floor when `a ≤ b`. -/
theorem floor_attained_v1_of_le (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : e * f ≤ f ^ 2 - e ^ 2) :
    oneSided f 0 (-e) (e * f) (f ^ 2 - e ^ 2) (f ^ 2) = f * min (e * f) (f ^ 2 - e ^ 2) := by
  rw [floor_attained e f he (by omega), min_eq_left h]

/-- `v₁ − v₂` attains the floor when `b ≤ a`. -/
theorem floor_attained_b_of_le (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : f ^ 2 - e ^ 2 ≤ e * f) :
    oneSided (f - e) (-f) (f - e) (e * f) (f ^ 2 - e ^ 2) (f ^ 2)
      = f * min (e * f) (f ^ 2 - e ^ 2) := by
  rw [floor_attained_b e f he hef, min_eq_right h]

/-- **The floor `f·min(a,b)` is sharp at every member**: attained by `v₁` when `a ≤ b` and by
`v₁ − v₂` when `b ≤ a`. -/
theorem floor_sharp (e f : ℤ) (he : 0 < e) (hef : e < f) :
    ∃ na nb nc : ℤ, na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = 0 ∧
      ¬ (na = 0 ∧ nb = 0 ∧ nc = 0) ∧
      oneSided na nb nc (e * f) (f ^ 2 - e ^ 2) (f ^ 2) = f * min (e * f) (f ^ 2 - e ^ 2) := by
  rcases le_total (e * f) (f ^ 2 - e ^ 2) with h | h
  · refine ⟨f, 0, -e, by ring, ?_, floor_attained_v1_of_le e f he hef h⟩
    rintro ⟨-, -, h3⟩; omega
  · exact ⟨f - e, -f, f - e, v12_relation e f, v12_nonzero e f hef,
      floor_attained_b_of_le e f he hef h⟩

/-- Control at `(e,f) = (5,6)`: the floor is `66`, `v₁` has one-sided length `180 ≠ 66`, and
`v₁ − v₂ = (1,−6,1)` attains `66` — so the sentence "`v₁` attains the floor" is false there. -/
theorem control_5_6 :
    oneSided 6 0 (-5) (5 * 6) (6 ^ 2 - 5 ^ 2) (6 ^ 2) = 180 ∧
    oneSided 1 (-6) 1 (5 * 6) (6 ^ 2 - 5 ^ 2) (6 ^ 2) = 66 ∧
    (6 : ℤ) * min (5 * 6) (6 ^ 2 - 5 ^ 2) = 66 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [oneSided]

end Erdos634.InterfaceFloor

#print axioms Erdos634.InterfaceFloor.floor_attained_b
#print axioms Erdos634.InterfaceFloor.floor_attained_v1_of_le
#print axioms Erdos634.InterfaceFloor.floor_attained_b_of_le
#print axioms Erdos634.InterfaceFloor.floor_sharp
#print axioms Erdos634.InterfaceFloor.control_5_6
