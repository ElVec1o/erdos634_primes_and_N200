/-
GA2M, atom (g1) part: **F4**.  For every ODD primitive character eta2 mod 2^i, i = k+3 >= 3:  eta2(3) != -1.
Proof (new here, uses only F5 = `GA2LGroup.eta2_val`, itself from `two_adic_par_value`):
(-3)^(2^k) = 1 + 2^(k+2) in Z/2^(k+3) (induction: (1+2^(k+2)u)^2 = 1 + 2^(k+3)(u + 2^(k+1) u^2), u odd).
If eta2(3) = -1 and eta2(-1) = -1 then eta2(-3) = 1, so eta2(1+2^(k+2)) = eta2(-3)^(2^k) = 1, contradicting F5.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2LGroup

namespace Erdos634.GA2MF4

open Erdos634.GA2LGroup

theorem neg3_pow (k : ℕ) : ∃ u : ℤ, Odd u ∧ ((-3 : ℤ) ^ (2 ^ k)) = 1 + 2 ^ (k + 2) * u := by
  induction k with
  | zero => exact ⟨-1, by decide, by norm_num⟩
  | succ k ih =>
    obtain ⟨u, ⟨w, hw⟩, h⟩ := ih
    refine ⟨u + 2 ^ (k + 1) * u ^ 2, ?_, ?_⟩
    · exact ⟨w + 2 ^ k * u ^ 2, by rw [hw]; ring⟩
    · rw [pow_succ, pow_mul, h]; ring

theorem neg3_zmod (k : ℕ) : ((-3 : ZMod (2 ^ (k + 3))) ^ (2 ^ k)) = 1 + 2 ^ (k + 2) := by
  obtain ⟨u, ⟨w, hw⟩, h⟩ := neg3_pow k
  have h0 : ((2 : ZMod (2 ^ (k + 3))) ^ (k + 3)) = 0 := by
    have := ZMod.natCast_self (2 ^ (k + 3)); push_cast at this; exact this
  have := congrArg (Int.cast : ℤ → ZMod (2 ^ (k + 3))) h
  push_cast at this
  rw [this, hw]; push_cast
  linear_combination (w : ZMod (2 ^ (k + 3))) * h0

theorem eta2_three_ne (k : ℕ) (η2 : DirichletCharacter ℂ (2 ^ (k + 3))) (hη2 : η2.IsPrimitive)
    (hodd : η2 (-1) = -1) : η2 (3 : ZMod (2 ^ (k + 3))) ≠ -1 := by
  intro h3
  have hm3 : η2 (-3 : ZMod (2 ^ (k + 3))) = 1 := by
    have : (-3 : ZMod (2 ^ (k + 3))) = (-1) * 3 := by ring
    rw [this, map_mul, hodd, h3]; norm_num
  have h := eta2_val k η2 hη2
  rw [← neg3_zmod k, map_pow, hm3, one_pow] at h
  norm_num at h

/-- Non-vacuity: an odd primitive eta2 exists (so the statement is not about the empty set). -/
theorem odd_prim_exists (k : ℕ) :
    ∃ η : DirichletCharacter ℂ (2 ^ (k + 3)), η.IsPrimitive ∧ η (-1) = -1 := by
  obtain ⟨η, hη⟩ := nonempty_par2 k (-1) (Or.inr rfl)
  exact ⟨η, Erdos634.GA2LCore.mem_PrimPar.1 hη⟩

end Erdos634.GA2MF4

#print axioms Erdos634.GA2MF4.eta2_three_ne
#print axioms Erdos634.GA2MF4.odd_prim_exists
