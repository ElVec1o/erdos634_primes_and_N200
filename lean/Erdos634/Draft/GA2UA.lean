/-
GA2U, atom A: the characters mod 5 (r = 1) used by Lemma T (D3Lab).
  `exists_psi_odd`, `exists_psi_even` : primitive characters mod 5 of each parity.
  `psi_odd_sq`   : psi odd  =>  psi(2)^2 = -1.
  `psi_even_two` : psi even primitive  =>  psi(2) = -1.
  `psi_odd_inj`  : psi odd, z w nonzero mod 5, psi z = psi w  =>  z = w.
  `five_tri`     : psi odd, the equations of psi and psi^-1 on two units x, y  =>
                   (ex = ey = 0) or (y = x and ex + ey = 0) or (y = -x and ex = ey).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SL
import Erdos634.Draft.GA2SP

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UA

open DirichletCharacter

theorem exists_psi_odd : ∃ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive ∧ ψ (-1) = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 1 le_rfl (-1) (Or.inr rfl)
  exact ⟨ψ, Erdos634.GA2LCore.mem_PrimPar.1 hψ⟩

theorem exists_psi_even : ∃ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive ∧ ψ (-1) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 1 le_rfl 1 (Or.inl rfl)
  exact ⟨ψ, Erdos634.GA2LCore.mem_PrimPar.1 hψ⟩

theorem zmod5_cases : ∀ z : ZMod (5 ^ 1), z ≠ 0 → z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 := by decide

theorem five_two_sq : (2 : ZMod (5 ^ 1)) * 2 = -1 := by decide
theorem five_three : (3 : ZMod (5 ^ 1)) = 2 * 2 * 2 := by decide
theorem five_three_two : (3 : ZMod (5 ^ 1)) * 2 = 1 := by decide
theorem five_four : (4 : ZMod (5 ^ 1)) = 2 * 2 := by decide

theorem psi_odd_sq (ψ : DirichletCharacter ℂ (5 ^ 1)) (h : ψ (-1) = -1) :
    ψ (2 : ZMod (5 ^ 1)) * ψ (2 : ZMod (5 ^ 1)) = -1 := by
  rw [← map_mul, five_two_sq, h]

theorem psi_even_two (ψ : DirichletCharacter ℂ (5 ^ 1)) (hp : ψ.IsPrimitive) (h : ψ (-1) = 1) :
    ψ (2 : ZMod (5 ^ 1)) = -1 := by
  have hsq : ψ (2 : ZMod (5 ^ 1)) * ψ (2 : ZMod (5 ^ 1)) = 1 := by
    rw [← map_mul, five_two_sq, h]
  have h1 : (ψ (2 : ZMod (5 ^ 1)) - 1) * (ψ (2 : ZMod (5 ^ 1)) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exfalso
    have h2' : ψ (2 : ZMod (5 ^ 1)) = 1 := by linear_combination h2
    have hone : ψ = 1 := by
      refine MulChar.ext (fun z => ?_)
      rw [MulChar.one_apply_coe]
      haveI : Fact (1 < 5 ^ 1) := ⟨by norm_num⟩
      have hz0 : (z : ZMod (5 ^ 1)) ≠ 0 := z.ne_zero
      rcases zmod5_cases (z : ZMod (5 ^ 1)) hz0 with h | h | h | h <;> rw [h]
      · simp
      · rw [h2']
      · rw [five_three, map_mul, map_mul, h2']; simp
      · rw [five_four, map_mul, h2']; simp
    have hc : ψ.conductor = 5 ^ 1 := hp
    rw [hone, DirichletCharacter.conductor_one] at hc
    norm_num at hc
  · linear_combination h2

theorem psi_odd_inj (ψ : DirichletCharacter ℂ (5 ^ 1)) (h : ψ (-1) = -1) (z w : ZMod (5 ^ 1))
    (hz : z ≠ 0) (hw : w ≠ 0) (hzw : ψ z = ψ w) : z = w := by
  have hs := psi_odd_sq ψ h
  have v3 : ψ (3 : ZMod (5 ^ 1)) = ψ 2 * ψ 2 * ψ 2 := by rw [five_three, map_mul, map_mul]
  have v4 : ψ (4 : ZMod (5 ^ 1)) = ψ 2 * ψ 2 := by rw [five_four, map_mul]
  have v1 : ψ (1 : ZMod (5 ^ 1)) = 1 := map_one ψ
  set s := ψ (2 : ZMod (5 ^ 1)) with hsdef
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h0; rw [h0] at hs; norm_num at hs
  have hsm : s ≠ -1 := by
    intro h0; rw [h0] at hs; norm_num at hs
  have hs3 : s * s * s = -s := by linear_combination s * hs
  rcases zmod5_cases z hz with rfl | rfl | rfl | rfl <;> rcases zmod5_cases w hw with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso
       simp only [v1, v3, v4, hs] at hzw
       first
       | exact hs1 (by linear_combination hzw)
       | exact hs1 (by linear_combination -hzw)
       | exact hsm (by linear_combination hzw)
       | exact hsm (by linear_combination -hzw)
       | exact hs0 (by linear_combination (1/2 : ℂ) * hzw)
       | exact hs0 (by linear_combination (-1/2 : ℂ) * hzw)
       | exact hs0 (by linear_combination (1/2 : ℂ) * hzw + (1/2 : ℂ) * s * hs)
       | (norm_num at hzw))

theorem five_tri (ψ : DirichletCharacter ℂ (5 ^ 1)) (h : ψ (-1) = -1) (x y : ZMod (5 ^ 1))
    (hx : IsUnit x) (hy : IsUnit y) (ex ey : ℂ)
    (E1 : ex * ψ x + ey * ψ y = 0) (E2 : ex * (ψ x)⁻¹ + ey * (ψ y)⁻¹ = 0) :
    (ex = 0 ∧ ey = 0) ∨ (y = x ∧ ex + ey = 0) ∨ (y = -x ∧ ex = ey) := by
  haveI : Fact (1 < 5 ^ 1) := ⟨by norm_num⟩
  have hx0 : x ≠ 0 := hx.ne_zero
  have hy0 : y ≠ 0 := hy.ne_zero
  have hu : ψ x ≠ 0 := Erdos634.GA2LCore.nz ψ x hx
  have hv : ψ y ≠ 0 := Erdos634.GA2LCore.nz ψ y hy
  by_cases hex : ex = 0
  · left
    refine ⟨hex, ?_⟩
    rw [hex, zero_mul, zero_add] at E1
    exact (mul_eq_zero.1 E1).resolve_right hv
  · right
    set u := ψ x with hudef
    set v := ψ y with hvdef
    have E2' : ex * v + ey * u = 0 := by
      have h2 := E2
      field_simp at h2
      linear_combination h2
    have hk : ex * ((u - v) * (u + v)) = 0 := by linear_combination u * E1 - v * E2'
    have hk' : (u - v) * (u + v) = 0 := (mul_eq_zero.1 hk).resolve_left hex
    rcases mul_eq_zero.1 hk' with h1 | h1
    · left
      have huv : v = u := by linear_combination -h1
      refine ⟨psi_odd_inj ψ h y x hy0 hx0 huv, ?_⟩
      rw [huv] at E1
      have : (ex + ey) * u = 0 := by linear_combination E1
      exact (mul_eq_zero.1 this).resolve_right hu
    · right
      have huv : v = -u := by linear_combination h1
      have hneg : ψ (-x) = -u := by
        rw [show -x = (-1 : ZMod (5 ^ 1)) * x by ring, map_mul, h]; ring
      refine ⟨psi_odd_inj ψ h y (-x) hy0 (neg_ne_zero.2 hx0) (by rw [hneg]; exact huv), ?_⟩
      rw [huv] at E1
      have : (ex - ey) * u = 0 := by linear_combination E1
      have := (mul_eq_zero.1 this).resolve_right hu
      linear_combination this

end Erdos634.GA2UA

#print axioms Erdos634.GA2UA.exists_psi_odd
#print axioms Erdos634.GA2UA.psi_even_two
#print axioms Erdos634.GA2UA.psi_odd_inj
#print axioms Erdos634.GA2UA.five_tri
