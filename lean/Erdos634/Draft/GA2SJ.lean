/-
GA2S, atom J: infrastructure for the T-rows (an entry divisible by 3, not by 5) at j >= 2 and r >= 2.

  `pointwise5_small` : 5-adic analogue of GA2PC.pointwise_small: <= 4 unit tokens, psi(Phi) = 0 for all primitive psi mod 5^r of
                       parity eps  =>  Phi(v) + eps Phi(-v) = 0 for all v          (r >= 2; |N_5| = 5 > 4 points)
  `const_prim3`      : (I3' for PRIMITIVE characters) j >= 2: if eta(h) takes one value c on every primitive eta mod 3^j then h = 1.
                       (primitive * (character of lower conductor) is primitive  =>  h = 1 mod 3^(j-1); then eta, eta^-1 and |N_3| = 3.)
  `exists_prim3`     : a primitive character mod 3^j exists (j >= 1).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SA
import Erdos634.Draft.GA2PC
import Erdos634.Draft.GA2PB
import Erdos634.Draft.LemmaSParity
import Erdos634.Draft.LemmaSIso

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SJ

open DirichletCharacter Erdos634.GA2PC
open Erdos634.LemmaSN (pred_dvd)

theorem pointwise5_small (r : ℕ) (hr : 2 ≤ r) {ι : Type*} (a : ι → ℕ) (c : ι → ℂ) (V : Finset ι)
    (hV : V.card ≤ 4) (hu : ∀ t ∈ V, IsUnit (a t : ZMod (5 ^ r))) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (horth : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ t ∈ V, c t * ψ (a t : ZMod (5 ^ r)) = 0) :
    ∀ v, PhiV (5 ^ r) a c V v + ε * PhiV (5 ^ r) a c V (-v) = 0 := by
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  set P : Finset (ZMod (5 ^ r))ˣ := (V.attach ×ˢ (univ : Finset Bool)).image
    (fun p => if p.2 then (hu p.1.1 p.1.2).unit else -(hu p.1.1 p.1.2).unit) with hP
  have hPc : P.card < 10 := by
    have h1 : P.card ≤ (V.attach ×ˢ (univ : Finset Bool)).card := Finset.card_image_le
    rw [Finset.card_product, Finset.card_attach, Finset.card_univ, Fintype.card_bool] at h1
    omega
  have hmem : ∀ v : (ZMod (5 ^ r))ˣ, (PhiV (5 ^ r) a c V v ≠ 0 ∨ PhiV (5 ^ r) a c V (-v) ≠ 0) → v ∈ P := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hcond : (v : ZMod (5 ^ r)) = (a t : ZMod (5 ^ r)) := by
        by_contra hh; rw [if_neg hh] at hne; exact hne rfl
      refine Finset.mem_image.2 ⟨(⟨t, ht⟩, true), by simp, ?_⟩
      simp only [if_true]
      apply Units.ext
      rw [IsUnit.unit_spec]
      exact hcond.symm
    · obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hcond : ((-v : (ZMod (5 ^ r))ˣ) : ZMod (5 ^ r)) = (a t : ZMod (5 ^ r)) := by
        by_contra hh; rw [if_neg hh] at hne; exact hne rfl
      refine Finset.mem_image.2 ⟨(⟨t, ht⟩, false), by simp, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      apply Units.ext
      rw [Units.val_neg, IsUnit.unit_spec]
      rw [Units.val_neg] at hcond
      rw [← hcond]; ring
  have h := Erdos634.GA2QB.top5_zero_small r hr (PhiV (5 ^ r) a c V) hε
    (fun ψ hψ hψ1 => by rw [sum_PhiV (5 ^ r) a c V hu ψ]; exact horth ψ hψ hψ1) P hmem hPc
  intro v
  have := h v
  linear_combination this

theorem card_ker3 (j : ℕ) (hj : 2 ≤ j) :
    Nat.card (ZMod.unitsMap (pred_dvd 3 j)).ker = 3 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (j - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have := Erdos634.GA2PB.card_N3 j hj
  simpa [MonoidHom.mem_ker] using this

theorem ker_pow3 (j : ℕ) (hj : 2 ≤ j) (k : (ZMod (3 ^ j))ˣ)
    (hk : ZMod.unitsMap (pred_dvd 3 j) k = 1) : k ^ 3 = 1 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (j - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hmem : k ∈ (ZMod.unitsMap (pred_dvd 3 j)).ker := by rw [MonoidHom.mem_ker]; exact hk
  have h := pow_card_eq_one' (G := (ZMod.unitsMap (pred_dvd 3 j)).ker) (x := ⟨k, hmem⟩)
  rw [card_ker3 j hj] at h
  have := congrArg (fun x : (ZMod.unitsMap (pred_dvd 3 j)).ker => (x : (ZMod (3 ^ j))ˣ)) h
  simpa using this

theorem exists_prim3 (j : ℕ) (hj : 1 ≤ j) : ∃ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hodd3 : 3 ^ j % 2 = 1 := by
    have : Odd (3 ^ j) := Odd.pow (by decide)
    exact Nat.odd_iff.1 this
  obtain ⟨ω, hωp, _⟩ := (Erdos634.LemmaSParity.exists_odd_primitive_iff
    (d := 3 ^ j) (pow_ne_zero _ (by norm_num)) (by omega)).2
    ⟨by
      intro h
      have : 3 ^ 1 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega, by omega⟩
  exact ⟨ω, hωp⟩

theorem prim_mul_lower (j : ℕ) (hj : 2 ≤ j) (η0 : DirichletCharacter ℂ (3 ^ j)) (h0 : η0.IsPrimitive)
    (lam : DirichletCharacter ℂ (3 ^ (j - 1))) :
    (η0 * changeLevel (pred_dvd 3 j) lam).IsPrimitive := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (j - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [Erdos634.LemmaSN.isPrimitive_iff_not_factorsThrough (p := 3) (by omega)] at h0 ⊢
  intro hf
  apply h0
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := η0) (pred_dvd 3 j)]
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := η0 * changeLevel (pred_dvd 3 j) lam)
    (pred_dvd 3 j)] at hf
  intro k hk
  have h1 := hf hk
  rw [MonoidHom.mem_ker] at h1 ⊢
  have hl : (changeLevel (pred_dvd 3 j) lam).toUnitHom k = 1 := by
    rw [DirichletCharacter.changeLevel_toUnitHom]
    simp only [MonoidHom.comp_apply]
    rw [MonoidHom.mem_ker.1 hk, map_one]
  have e1 : η0 (k : ZMod (3 ^ j)) * (changeLevel (pred_dvd 3 j) lam) (k : ZMod (3 ^ j)) = 1 := by
    have := congrArg (fun w : ℂˣ => (w : ℂ)) h1
    simpa [MulChar.coe_toUnitHom, MulChar.mul_apply] using this
  have e2 : (changeLevel (pred_dvd 3 j) lam) (k : ZMod (3 ^ j)) = 1 := by
    have := congrArg (fun w : ℂˣ => (w : ℂ)) hl
    simpa [MulChar.coe_toUnitHom] using this
  apply Units.ext
  simp only [MulChar.coe_toUnitHom, Units.val_one]
  rw [e2, mul_one] at e1
  exact e1

theorem const_prim3 (j : ℕ) (hj : 2 ≤ j) (h : (ZMod (3 ^ j))ˣ) (c : ℂ)
    (hc : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive → η (h : ZMod (3 ^ j)) = c) : h = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (j - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨η0, h0⟩ := exists_prim3 j (by omega)
  have hη0 : η0 (h : ZMod (3 ^ j)) ≠ 0 := Erdos634.GA2LCore.nz η0 _ h.isUnit
  -- step (i): h reduces to 1 mod 3^(j-1)
  have hmem : ZMod.unitsMap (pred_dvd 3 j) h = 1 := by
    by_contra hne
    have hne' : ((ZMod.unitsMap (pred_dvd 3 j) h : (ZMod (3 ^ (j - 1)))ˣ) : ZMod (3 ^ (j - 1))) ≠ 1 := by
      intro h'
      apply hne
      apply Units.ext
      simpa using h'
    obtain ⟨lam, hlam⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne'
    have hp := prim_mul_lower j hj η0 h0 lam
    have e1 := hc η0 h0
    have e2 := hc _ hp
    rw [MulChar.mul_apply, e1] at e2
    have hl : (changeLevel (pred_dvd 3 j) lam) (h : ZMod (3 ^ j)) =
        lam ((ZMod.unitsMap (pred_dvd 3 j) h : (ZMod (3 ^ (j - 1)))ˣ) : ZMod (3 ^ (j - 1))) := by
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd lam (pred_dvd 3 j) h
      rw [this]
      congr 1
    rw [hl] at e2
    have hc0 : c ≠ 0 := e1 ▸ hη0
    exact hlam (mul_left_cancel₀ hc0 (by rw [mul_one]; exact e2))
  -- step (ii)
  by_contra hne1
  have h3 : h ^ 3 = 1 := ker_pow3 j hj h hmem
  have hinv : (η0⁻¹).IsPrimitive := by
    show (η0⁻¹).conductor = 3 ^ j
    rw [DirichletCharacter.conductor_inv]; exact h0
  have e1 := hc η0 h0
  have e2 := hc η0⁻¹ hinv
  rw [MulChar.inv_apply_eq_inv'] at e2
  have hB : η0 (h : ZMod (3 ^ j)) * η0 (h : ZMod (3 ^ j)) = 1 := by
    have : (η0 (h : ZMod (3 ^ j)))⁻¹ = η0 (h : ZMod (3 ^ j)) := by rw [e1] at e2 ⊢; exact e2
    field_simp at this
    linear_combination -this
  have hA : η0 (h : ZMod (3 ^ j)) ^ 3 = 1 := by
    rw [← map_pow]
    have : (h : ZMod (3 ^ j)) ^ 3 = 1 := by
      have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) h3
      simpa using this
    rw [this, map_one]
  have hx1 : η0 (h : ZMod (3 ^ j)) = 1 := by
    linear_combination hA - η0 (h : ZMod (3 ^ j)) * hB
  have hhK : h ∈ (ZMod.unitsMap (pred_dvd 3 j)).ker := by rw [MonoidHom.mem_ker]; exact hmem
  have hg : Subgroup.zpowers (⟨h, hhK⟩ : (ZMod.unitsMap (pred_dvd 3 j)).ker) = ⊤ :=
    zpowers_eq_top_of_prime_card (card_ker3 j hj) (by
      intro h'
      apply hne1
      have := congrArg (fun x : (ZMod.unitsMap (pred_dvd 3 j)).ker => (x : (ZMod (3 ^ j))ˣ)) h'
      simpa using this)
  rw [Erdos634.LemmaSN.isPrimitive_iff_not_factorsThrough (p := 3) (by omega)] at h0
  apply h0
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := η0) (pred_dvd 3 j)]
  intro k hk
  have hkm : (⟨k, hk⟩ : (ZMod.unitsMap (pred_dvd 3 j)).ker) ∈
      Subgroup.zpowers (⟨h, hhK⟩ : (ZMod.unitsMap (pred_dvd 3 j)).ker) := by
    rw [hg]; exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hkm
  have hkh : k = h ^ m := by
    have := congrArg (fun x : (ZMod.unitsMap (pred_dvd 3 j)).ker => (x : (ZMod (3 ^ j))ˣ)) hm
    simpa using this.symm
  rw [MonoidHom.mem_ker]
  have h1 : η0.toUnitHom h = 1 := by
    apply Units.ext
    simp only [MulChar.coe_toUnitHom, Units.val_one]
    exact hx1
  rw [hkh, map_zpow, h1, one_zpow]

end Erdos634.GA2SJ

#print axioms Erdos634.GA2SJ.pointwise5_small
#print axioms Erdos634.GA2SJ.const_prim3
#print axioms Erdos634.GA2SJ.exists_prim3
