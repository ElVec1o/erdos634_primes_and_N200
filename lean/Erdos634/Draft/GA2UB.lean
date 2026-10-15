/-
GA2U, atom B: 3-adic facts for Lemma T (D3Lab), j >= 2.
  `ker_gen`            : g = -2 and h = g^(3^(j-2)) lies in N_3 = ker((Z/3^j)^x -> (Z/3^(j-1))^x), h != 1.
  `prim_gen_ne_one`    : eta primitive mod 3^j, h in N_3, h != 1  =>  eta(h) != 1.
  `prim_two_ne_neg_one`: eta primitive mod 3^j (j >= 2)  =>  eta(2) != -1.
  `exists_odd_prim`    : an odd primitive character mod 3^j exists (j >= 1).
  `two_ne_one3`, `two_ne_neg_one3`, `neg_ne_self3` : 2 != +-1, -u != u mod 3^j (j >= 2).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SJ

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UB

open DirichletCharacter
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.GA2SJ (card_ker3 ker_pow3)

theorem ker_gen (j : ℕ) (hj : 2 ≤ j) :
    ∃ g h : (ZMod (3 ^ j))ˣ, (g : ZMod (3 ^ j)) = -2 ∧ h = g ^ (3 ^ (j - 2)) ∧
      ZMod.unitsMap (pred_dvd 3 j) h = 1 ∧ h ≠ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
  haveI : NeZero (3 ^ (n + 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (n + 2 - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hgu : IsUnit (-2 : ZMod (3 ^ (n + 2))) := by
    have := (ZMod.isUnit_iff_coprime 2 (3 ^ (n + 2))).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this.neg
  have ho2 : orderOf (-2 : ZMod (3 ^ (n + 2))) = 3 ^ (n + 1) := by
    have := ZMod.orderOf_one_add_mul_prime (p := 3) Nat.prime_three (by norm_num) (-1) (by norm_num) (n + 1)
    have e : (1 + ((3 : ℕ) : ZMod (3 ^ (n + 1 + 1))) * (((-1 : ℤ)) : ZMod (3 ^ (n + 1 + 1)))) = -2 := by
      push_cast; ring
    rw [e] at this
    exact this
  have ho1 : orderOf (-2 : ZMod (3 ^ (n + 1))) = 3 ^ n := by
    have := ZMod.orderOf_one_add_mul_prime (p := 3) Nat.prime_three (by norm_num) (-1) (by norm_num) n
    have e : (1 + ((3 : ℕ) : ZMod (3 ^ (n + 1))) * (((-1 : ℤ)) : ZMod (3 ^ (n + 1)))) = -2 := by
      push_cast; ring
    rw [e] at this
    exact this
  refine ⟨hgu.unit, hgu.unit ^ (3 ^ (n + 2 - 2)), rfl, rfl, ?_, ?_⟩
  · apply Units.ext
    have ho1' : orderOf (-2 : ZMod (3 ^ (n + 2 - 1))) = 3 ^ n := ho1
    have hc : (((Units.map (↑(ZMod.castHom (pred_dvd 3 (n + 2)) (ZMod (3 ^ (n + 2 - 1)))) :
        ZMod (3 ^ (n + 2)) →* ZMod (3 ^ (n + 2 - 1)))) hgu.unit : (ZMod (3 ^ (n + 2 - 1)))ˣ) :
        ZMod (3 ^ (n + 2 - 1))) = -2 := by
      rw [Units.coe_map, IsUnit.unit_spec]
      change ZMod.castHom (pred_dvd 3 (n + 2)) (ZMod (3 ^ (n + 2 - 1))) (-2) = -2
      rw [map_neg, map_ofNat]
    simp only [ZMod.unitsMap, Units.val_pow_eq_pow_val, Units.val_one, map_pow]
    rw [hc, show n + 2 - 2 = n by omega, ← ho1']
    exact pow_orderOf_eq_one _
  · intro h
    have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h'
    have hd : orderOf (-2 : ZMod (3 ^ (n + 2))) ∣ 3 ^ (n + 2 - 2) := orderOf_dvd_of_pow_eq_one h'
    rw [ho2, show n + 2 - 2 = n by omega] at hd
    have := Nat.le_of_dvd (by positivity) hd
    have h2 : 3 ^ n < 3 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem prim_gen_ne_one (j : ℕ) (hj : 2 ≤ j) (η : DirichletCharacter ℂ (3 ^ j)) (h0 : η.IsPrimitive)
    (h : (ZMod (3 ^ j))ˣ) (hmem : ZMod.unitsMap (pred_dvd 3 j) h = 1) (hne : h ≠ 1) :
    η (h : ZMod (3 ^ j)) ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (j - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  intro hx1
  have hhK : h ∈ (ZMod.unitsMap (pred_dvd 3 j)).ker := by rw [MonoidHom.mem_ker]; exact hmem
  have hg : Subgroup.zpowers (⟨h, hhK⟩ : (ZMod.unitsMap (pred_dvd 3 j)).ker) = ⊤ :=
    zpowers_eq_top_of_prime_card (card_ker3 j hj) (by
      intro h'
      apply hne
      have := congrArg (fun x : (ZMod.unitsMap (pred_dvd 3 j)).ker => (x : (ZMod (3 ^ j))ˣ)) h'
      simpa using this)
  rw [Erdos634.LemmaSN.isPrimitive_iff_not_factorsThrough (p := 3) (by omega)] at h0
  apply h0
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := η) (pred_dvd 3 j)]
  intro k hk
  have hkm : (⟨k, hk⟩ : (ZMod.unitsMap (pred_dvd 3 j)).ker) ∈
      Subgroup.zpowers (⟨h, hhK⟩ : (ZMod.unitsMap (pred_dvd 3 j)).ker) := by
    rw [hg]; exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hkm
  have hkh : k = h ^ m := by
    have := congrArg (fun x : (ZMod.unitsMap (pred_dvd 3 j)).ker => (x : (ZMod (3 ^ j))ˣ)) hm
    simpa using this.symm
  rw [MonoidHom.mem_ker]
  have h1 : η.toUnitHom h = 1 := by
    apply Units.ext
    simp only [MulChar.coe_toUnitHom, Units.val_one]
    exact hx1
  rw [hkh, map_zpow, h1, one_zpow]

theorem prim_two_ne_neg_one (j : ℕ) (hj : 2 ≤ j) (η : DirichletCharacter ℂ (3 ^ j)) (h0 : η.IsPrimitive) :
    η (2 : ZMod (3 ^ j)) ≠ -1 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  intro h2
  obtain ⟨g, h, hg, hh, hmem, hne⟩ := ker_gen j hj
  have hηg : η (g : ZMod (3 ^ j)) = η (-1) * η 2 := by
    rw [hg, ← map_mul]; congr 1; ring
  have hηh : η (h : ZMod (3 ^ j)) = (η (g : ZMod (3 ^ j))) ^ (3 ^ (j - 2)) := by
    rw [hh, Units.val_pow_eq_pow_val, map_pow]
  rcases DirichletCharacter.even_or_odd η with he | ho
  · -- even: eta(g) = -1, eta(h) = -1, but h^3 = 1
    have e1 : η (g : ZMod (3 ^ j)) = -1 := by rw [hηg, he, h2]; ring
    have e2 : η (h : ZMod (3 ^ j)) = -1 := by
      rw [hηh, e1]
      exact Odd.neg_one_pow (Odd.pow (by decide))
    have h3 : h ^ 3 = 1 := ker_pow3 j hj h hmem
    have e3 : η (h : ZMod (3 ^ j)) ^ 3 = 1 := by
      rw [← map_pow]
      have : (h : ZMod (3 ^ j)) ^ 3 = 1 := by
        have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) h3
        simpa using this
      rw [this, map_one]
    rw [e2] at e3
    norm_num at e3
  · -- odd: eta(g) = 1, eta(h) = 1, contradiction with primitivity
    have e1 : η (g : ZMod (3 ^ j)) = 1 := by rw [hηg, ho, h2]; ring
    have e2 : η (h : ZMod (3 ^ j)) = 1 := by rw [hηh, e1, one_pow]
    exact prim_gen_ne_one j hj η h0 h hmem hne e2

theorem exists_odd_prim (j : ℕ) (hj : 1 ≤ j) :
    ∃ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive ∧ η (-1) = -1 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hodd3 : 3 ^ j % 2 = 1 := by
    have : Odd (3 ^ j) := Odd.pow (by decide)
    exact Nat.odd_iff.1 this
  obtain ⟨ω, hωp, hωo⟩ := (Erdos634.LemmaSParity.exists_odd_primitive_iff
    (d := 3 ^ j) (pow_ne_zero _ (by norm_num)) (by omega)).2
    ⟨by
      intro h
      have : 3 ^ 1 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega, by omega⟩
  exact ⟨ω, hωp, hωo⟩

theorem two_ne_one3 (j : ℕ) (hj : 2 ≤ j) : (2 : ZMod (3 ^ j)) ≠ 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod (3 ^ j)) = 0 := by
    have : (2 : ZMod (3 ^ j)) - 1 = 0 := by rw [h]; ring
    have e : (2 : ZMod (3 ^ j)) - 1 = ((1 : ℕ) : ZMod (3 ^ j)) := by push_cast; ring
    rw [← e]; exact this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  have h9 : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  omega

theorem two_ne_neg_one3 (j : ℕ) (hj : 2 ≤ j) : (2 : ZMod (3 ^ j)) ≠ -1 := by
  intro h
  have h1 : ((3 : ℕ) : ZMod (3 ^ j)) = 0 := by
    have : (2 : ZMod (3 ^ j)) + 1 = 0 := by rw [h]; ring
    have e : (2 : ZMod (3 ^ j)) + 1 = ((3 : ℕ) : ZMod (3 ^ j)) := by push_cast; ring
    rw [← e]; exact this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  have h9 : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  omega

theorem neg_ne_self3 (j : ℕ) (hj : 1 ≤ j) (u : (ZMod (3 ^ j))ˣ) : -u ≠ u := by
  intro h
  have h2 : (2 : ZMod (3 ^ j)) * (u : ZMod (3 ^ j)) = 0 := by
    have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) h
    simp only [Units.val_neg] at this
    linear_combination -this
  have h20 : (2 : ZMod (3 ^ j)) = 0 := by
    have := u.isUnit
    exact (this.mul_left_eq_zero).1 h2
  have h2n : ((2 : ℕ) : ZMod (3 ^ j)) = 0 := by exact_mod_cast h20
  rw [ZMod.natCast_eq_zero_iff] at h2n
  have := Nat.le_of_dvd (by norm_num) h2n
  have h9 : 3 ^ 1 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  omega

end Erdos634.GA2UB

#print axioms Erdos634.GA2UB.ker_gen
#print axioms Erdos634.GA2UB.prim_gen_ne_one
#print axioms Erdos634.GA2UB.prim_two_ne_neg_one
#print axioms Erdos634.GA2UB.exists_odd_prim
#print axioms Erdos634.GA2UB.neg_ne_self3
