/-
GA2S, atom A: character facts at 5^r, r >= 2, for the Prop K-a bottom step and the Euler factor.

  `psi_sq_ne_one` : psi primitive mod 5^r, r >= 2, g in {2, 3}  =>  psi(g)^2 != 1.
                    (g generates (Z/5^r)^x; psi^2 = 1 would factor through 5^(r-1) since ker has order 5.)
  `psi_two_sq_ne_one`, `psi_three_ne_neg_one` : the two instances used (psi(2)^2 != 1, psi(3) != -1).
  `odd_prim_exists`, `inv_prim_odd` : an odd primitive psi mod 5^r exists, and its inverse is again odd primitive.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NF1
import Erdos634.Draft.GA2QB
import Erdos634.Draft.GA2NR1

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SA

open DirichletCharacter Erdos634.GA2NF1
open Erdos634.LemmaSN (pred_dvd)

theorem ker_pow5 (r : ℕ) (hr : 2 ≤ r) (k : (ZMod (5 ^ r))ˣ)
    (hk : ZMod.unitsMap (pred_dvd 5 r) k = 1) : k ^ 5 = 1 := by
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ (r - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  set K := (ZMod.unitsMap (pred_dvd 5 r)).ker with hK
  have hcard : Nat.card K = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have := Erdos634.GA2QB.card_N5 r hr
    simpa [hK, MonoidHom.mem_ker] using this
  have hmem : k ∈ K := by rw [hK, MonoidHom.mem_ker]; exact hk
  have h := pow_card_eq_one' (G := K) (x := ⟨k, hmem⟩)
  rw [hcard] at h
  have := congrArg (fun x : K => (x : (ZMod (5 ^ r))ˣ)) h
  simpa using this

theorem sq_ne_one_gen (r : ℕ) (hr : 1 ≤ r) (g : ℕ) (a : ℤ) (ha : ¬ (5 : ℤ) ∣ a)
    (hga : (g : ℤ) ^ 4 = 1 + 5 * a)
    (hg5 : ∀ o : ℕ, ((g : ℕ) : ZMod 5) ^ o = 1 → 4 ∣ o) (hcop : Nat.Coprime g 5)
    (ψ : DirichletCharacter ℂ (5 ^ (r + 1))) (hψ : ψ.IsPrimitive) :
    ψ (g : ZMod (5 ^ (r + 1))) ^ 2 ≠ 1 := by
  haveI : NeZero (5 ^ (r + 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro h1
  have hunit : IsUnit (g : ZMod (5 ^ (r + 1))) := by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.Coprime.pow_right _ hcop
  set u : (ZMod (5 ^ (r + 1)))ˣ := hunit.unit with hu
  have hga' : (g : ZMod (5 ^ (r + 1))) ^ 4 = 1 + 5 * (a : ZMod (5 ^ (r + 1))) := by
    have := congrArg (Int.cast : ℤ → ZMod (5 ^ (r + 1))) hga
    push_cast at this
    exact this
  have hg5' : ∀ o : ℕ, (g : ZMod (5 ^ (r + 1))) ^ o = 1 → 4 ∣ o := by
    intro o ho
    apply hg5
    have := congrArg (ZMod.castHom (dvd_pow_self 5 (by omega : r + 1 ≠ 0)) (ZMod 5)) ho
    simpa using this
  have hord : orderOf (g : ZMod (5 ^ (r + 1))) = 4 * 5 ^ r := orderOf_gen r _ a ha hga' hg5'
  have hordu : orderOf u = 4 * 5 ^ r := by
    rw [← hord, ← orderOf_injective (Units.coeHom (ZMod (5 ^ (r + 1)))) Units.coeHom_injective u]
    simp [hu]
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hordu, units_card]
  have hone : ψ * ψ = 1 := by
    apply char_one_of_gen u htop
    rw [MulChar.mul_apply]
    have : ψ (u : ZMod (5 ^ (r + 1))) = ψ (g : ZMod (5 ^ (r + 1))) := by simp [hu]
    rw [this]; linear_combination h1
  have hsq : ∀ x : ZMod (5 ^ (r + 1)), ψ x * ψ x = 1 * (1 : DirichletCharacter ℂ (5 ^ (r + 1))) x := by
    intro x
    have := congrArg (fun χ : DirichletCharacter ℂ (5 ^ (r + 1)) => χ x) hone
    simpa [MulChar.mul_apply] using this
  have hnp := (Erdos634.LemmaSN.isPrimitive_iff_not_factorsThrough (p := 5) (by omega : 1 ≤ r + 1) ψ).1 hψ
  apply hnp
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ψ) (pred_dvd 5 (r + 1))]
  intro k hk
  rw [MonoidHom.mem_ker] at hk ⊢
  have hk5 := ker_pow5 (r + 1) (by omega) k hk
  apply Units.ext
  have e1 : ψ (k : ZMod (5 ^ (r + 1))) * ψ (k : ZMod (5 ^ (r + 1))) = 1 := by
    have := hsq (k : ZMod (5 ^ (r + 1)))
    rw [MulChar.one_apply k.isUnit] at this
    simpa using this
  have e5 : ψ (k : ZMod (5 ^ (r + 1))) ^ 5 = 1 := by
    rw [← map_pow]
    have : (k : ZMod (5 ^ (r + 1))) ^ 5 = 1 := by
      have := congrArg (fun w : (ZMod (5 ^ (r + 1)))ˣ => (w : ZMod (5 ^ (r + 1)))) hk5
      simpa using this
    rw [this, map_one]
  simp only [MulChar.coe_toUnitHom, Units.val_one]
  linear_combination e5 - (ψ (k : ZMod (5 ^ (r + 1))) * (ψ (k : ZMod (5 ^ (r + 1))) ^ 2 + 1)) * e1

theorem psi_two_sq_ne_one (r : ℕ) (hr : 2 ≤ r) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) :
    ψ (2 : ZMod (5 ^ r)) ^ 2 ≠ 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have := sq_ne_one_gen r' (by omega) 2 3 (by norm_num) (by norm_num)
    (fun o ho => four_dvd_of_pow 2 (by decide) (by decide) o (by simpa using ho)) (by norm_num) ψ hψ
  simpa using this

theorem psi_three_sq_ne_one (r : ℕ) (hr : 2 ≤ r) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) :
    ψ (3 : ZMod (5 ^ r)) ^ 2 ≠ 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have := sq_ne_one_gen r' (by omega) 3 16 (by norm_num) (by norm_num)
    (fun o ho => four_dvd_of_pow 3 (by decide) (by decide) o (by simpa using ho)) (by norm_num) ψ hψ
  simpa using this

theorem psi_three_ne_neg_one (r : ℕ) (hr : 2 ≤ r) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) :
    ψ (3 : ZMod (5 ^ r)) ≠ -1 := by
  intro h
  apply psi_three_sq_ne_one r hr ψ hψ
  rw [h]; norm_num

theorem odd_prim_exists (r : ℕ) (hr : 1 ≤ r) :
    ∃ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive ∧ ψ (-1) = -1 := by
  obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 r hr (-1) (Or.inr rfl)
  exact ⟨ψ, (Erdos634.GA2LCore.mem_PrimPar.1 hψ).1, (Erdos634.GA2LCore.mem_PrimPar.1 hψ).2⟩

theorem inv_prim (r : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) : (ψ⁻¹).IsPrimitive := by
  show (ψ⁻¹).conductor = 5 ^ r
  rw [DirichletCharacter.conductor_inv]; exact hψ

theorem inv_neg_one (r : ℕ) (ψ : DirichletCharacter ℂ (5 ^ r)) (h : ψ (-1) = -1) : ψ⁻¹ (-1) = -1 := by
  rw [MulChar.inv_apply_eq_inv', h]; norm_num

end Erdos634.GA2SA

#print axioms Erdos634.GA2SA.ker_pow5
#print axioms Erdos634.GA2SA.psi_two_sq_ne_one
#print axioms Erdos634.GA2SA.psi_three_ne_neg_one
#print axioms Erdos634.GA2SA.odd_prim_exists
#print axioms Erdos634.GA2SA.inv_prim
