/-
GA2N, item (3) support: **F4 for 5^r** (GA2Y_NOTES (F4)): for every primitive psi mod 5^r, r >= 1,
psi(2) != 1 and psi(3) != 1  (2 and 3 are primitive roots mod 5^r).

Proof: g in {2,3} has g^4 = 1 + 5a, 5 !| a (16 = 1 + 5*3, 81 = 1 + 5*16), so ord(g^4) = 5^(r-1)
(`ZMod.orderOf_one_add_mul_prime`), 4 | ord(g) (reduction mod 5), ord(g) | 4*5^(r-1); hence ord(g) = 4*5^(r-1) = phi(5^r)
and g generates the unit group; a character with psi(g) = 1 is trivial; a primitive psi mod 5^r is nontrivial.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NG

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NF1

open DirichletCharacter
open Erdos634.GA2NG

theorem four_dvd_of_pow (g : ZMod 5) (h4 : g ^ 4 = 1) (hg : ∀ m : ℕ, m < 4 → 0 < m → g ^ m ≠ 1)
    (o : ℕ) (ho : g ^ o = 1) : 4 ∣ o := by
  have hr : o % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e : g ^ o = g ^ (o % 4) := by
    conv_lhs => rw [← Nat.div_add_mod o 4, pow_add, pow_mul, h4, one_pow, one_mul]
  rw [e] at ho
  by_contra hn
  have hpos : 0 < o % 4 := by omega
  exact hg _ hr hpos ho

theorem orderOf_gen (r : ℕ) (g : ZMod (5 ^ (r + 1))) (a : ℤ) (ha : ¬ (5 : ℤ) ∣ a)
    (hga : g ^ 4 = 1 + 5 * (a : ZMod (5 ^ (r + 1))))
    (hg5 : ∀ o : ℕ, g ^ o = 1 → 4 ∣ o) : orderOf g = 4 * 5 ^ r := by
  have h1 : orderOf (1 + 5 * (a : ZMod (5 ^ (r + 1)))) = 5 ^ r := by
    have := ZMod.orderOf_one_add_mul_prime (p := 5) (by norm_num) (by norm_num) a ha r
    simpa using this
  rw [← hga] at h1
  have h2 : orderOf g ∣ 4 * 5 ^ r := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, ← h1]
    exact pow_orderOf_eq_one _
  have h3 : 4 ∣ orderOf g := hg5 _ (pow_orderOf_eq_one g)
  have h4 : orderOf (g ^ 4) = orderOf g / 4 := orderOf_pow_of_dvd (by norm_num) h3
  rw [h1] at h4
  obtain ⟨c, hc⟩ := h3
  rw [hc] at h4 ⊢
  have : 4 * c / 4 = c := by omega
  rw [this] at h4
  rw [h4]

theorem units_card (r : ℕ) : Nat.card (ZMod (5 ^ (r + 1)))ˣ = 4 * 5 ^ r := by
  haveI : NeZero (5 ^ (r + 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow (by norm_num) (by omega)]
  simp [Nat.add_sub_cancel]
  ring

theorem char_one_of_gen {N : ℕ} [NeZero N] (g : (ZMod N)ˣ) (hg : Subgroup.zpowers g = ⊤)
    (χ : DirichletCharacter ℂ N) (h : χ (g : ZMod N) = 1) : χ = 1 := by
  have hker : g ∈ (MulChar.toUnitHom χ).ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    simp [MulChar.coe_toUnitHom, h]
  have hle : Subgroup.zpowers g ≤ (MulChar.toUnitHom χ).ker := (Subgroup.zpowers_le).2 hker
  rw [hg] at hle
  ext u
  have hu : u ∈ (MulChar.toUnitHom χ).ker := hle (Subgroup.mem_top u)
  rw [MonoidHom.mem_ker] at hu
  have := congrArg (fun x : ℂˣ => (x : ℂ)) hu
  simp [MulChar.coe_toUnitHom] at this
  rw [this, MulChar.one_apply u.isUnit]

theorem psi_ne_one_gen (r : ℕ) (g : ℕ) (a : ℤ) (ha : ¬ (5 : ℤ) ∣ a) (hga : (g : ℤ) ^ 4 = 1 + 5 * a)
    (hg5 : ∀ o : ℕ, ((g : ℕ) : ZMod 5) ^ o = 1 → 4 ∣ o) (hcop : Nat.Coprime g 5)
    (ψ : DirichletCharacter ℂ (5 ^ (r + 1))) (hψ : ψ.IsPrimitive) : ψ (g : ZMod (5 ^ (r + 1))) ≠ 1 := by
  haveI : NeZero (5 ^ (r + 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
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
  have hone : ψ = 1 := char_one_of_gen u htop ψ (by simpa [hu] using h1)
  have hc : ψ.conductor = 1 := (eq_one_iff_conductor_eq_one).1 hone
  rw [show ψ.conductor = 5 ^ (r + 1) from hψ] at hc
  have : 5 ^ (r + 1) ≥ 5 := by
    calc 5 ^ (r + 1) ≥ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 5 := by norm_num
  omega

theorem psi_two_ne_one (r : ℕ) (hr : 1 ≤ r) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) :
    ψ (2 : ZMod (5 ^ r)) ≠ 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have := psi_ne_one_gen r' 2 3 (by norm_num) (by norm_num)
    (fun o ho => four_dvd_of_pow 2 (by decide) (by decide) o (by simpa using ho)) (by norm_num) ψ hψ
  simpa using this

theorem psi_three_ne_one (r : ℕ) (hr : 1 ≤ r) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive) :
    ψ (3 : ZMod (5 ^ r)) ≠ 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have := psi_ne_one_gen r' 3 16 (by norm_num) (by norm_num)
    (fun o ho => four_dvd_of_pow 3 (by decide) (by decide) o (by simpa using ho)) (by norm_num) ψ hψ
  simpa using this

end Erdos634.GA2NF1

#print axioms Erdos634.GA2NF1.orderOf_gen
#print axioms Erdos634.GA2NF1.psi_two_ne_one
#print axioms Erdos634.GA2NF1.psi_three_ne_one
