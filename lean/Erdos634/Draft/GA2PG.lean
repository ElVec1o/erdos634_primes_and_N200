/-
GA2P, Theorem B, part 3: the BOTTOM step (trivial eta2, eta3, psi odd) killing shapes A and B.
  `bottomA` : a_Y = a_X + n/2, e_X = e_Y  =>  e_X = 0     (uses psi and psi^-1, c^2 = -1)
  `bottomB` : a_X + a_Y = n/2 = a_S       =>  e_X = e_Y
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PF
import Erdos634.Draft.LemmaSParity

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PG

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PF

theorem zmod5_of_dvd (x : ℕ) (h : 5 ∣ x) : (x : ZMod (5 ^ 1)) = 0 :=
  (ZMod.natCast_eq_zero_iff x (5 ^ 1)).2 (by simpa using h)

theorem exists_odd_psi : ∃ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive ∧ ψ (-1) = -1 := by
  obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 1 le_rfl (-1) (Or.inr rfl)
  exact ⟨ψ, (Erdos634.GA2LCore.mem_PrimPar.1 hψ).1, (Erdos634.GA2LCore.mem_PrimPar.1 hψ).2⟩

theorem prim_ne_one (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive) : ψ ≠ 1 := by
  rintro rfl
  have : (1 : DirichletCharacter ℂ (5 ^ 1)).conductor = 5 ^ 1 := hψ
  rw [DirichletCharacter.conductor_one] at this
  norm_num at this

theorem unit_cop (j : ℕ) (x : ℕ) (hx2 : x % 2 = 1) (hx3 : ¬ 3 ∣ x) : Nat.Coprime (2 ^ 2 * 3 ^ j) x := by
  apply Nat.Coprime.mul_left
  · apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  · exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hx3)

theorem one_neg_one_B (j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψo : ψ (-1) = -1) :
    ψ (-1) * (1 : DirichletCharacter ℂ (2 ^ 2)) (-1) * (1 : DirichletCharacter ℂ (3 ^ j)) (-1) = -1 := by
  rw [hψo, MulChar.one_apply (isUnit_one.neg), MulChar.one_apply (isUnit_one.neg)]; norm_num

/-- the equation of the BOTTOM step in shape A, for one odd primitive psi. -/
theorem eqA (j : ℕ) (hj : 1 ≤ j) (aX aY aS b : ℕ) (eX eY eS : ℂ)
    (hY : aY = aX + 2 * (5 * 3 ^ j)) (hb : aX + 2 * b = 5 * 3 ^ j) (hZ : aS = 4 * b)
    (hX5 : ¬ 5 ∣ aX) (hX3 : ¬ 3 ∣ aX) (hXo : aX % 2 = 1) (hE : eX = eY)
    (H : H3B j aX aY aS eX eY eS)
    (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive) (hψo : ψ (-1) = -1) :
    eX * (1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹) = eS * (ψ (2 : ZMod (5 ^ 1)))⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3N : 3 ∣ 5 * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 5
  have h5N : 5 ∣ 5 * 3 ^ j := dvd_mul_right _ _
  generalize hN : 5 * 3 ^ j = N at *
  have hY5 : ¬ 5 ∣ aY := by omega
  have hY3 : ¬ 3 ∣ aY := by omega
  have hYo : aY % 2 = 1 := by omega
  have hb3 : ¬ 3 ∣ b := by omega
  have hS5 : ¬ 5 ∣ 4 * b := by omega
  subst hZ
  subst hN
  have hbot := H ψ hψ 1 1 (one_neg_one_B j ψ hψo)
  rw [bracket_triv_odd j hj ψ hψ aX hX5 (unit_cop j aX hXo hX3),
    bracket_triv_odd j hj ψ hψ aY hY5 (unit_cop j aY hYo hY3),
    bracket_triv_four j hj ψ hψ b hS5 hb3] at hbot
  have hcast : (aY : ZMod (5 ^ 1)) = (aX : ZMod (5 ^ 1)) := by
    rw [hY]; push_cast
    have : ((5 * 3 ^ j : ℕ) : ZMod (5 ^ 1)) = 0 := zmod5_of_dvd _ (dvd_mul_right _ _)
    push_cast at this
    rw [this]; ring
  have hb2 : (2 : ZMod (5 ^ 1)) * (b : ZMod (5 ^ 1)) = -(aX : ZMod (5 ^ 1)) := by
    have : ((aX + 2 * b : ℕ) : ZMod (5 ^ 1)) = 0 := by rw [hb]; exact zmod5_of_dvd _ (dvd_mul_right _ _)
    push_cast at this
    linear_combination this
  have hψb : ψ (2 : ZMod (5 ^ 1)) * ψ (b : ZMod (5 ^ 1)) = - ψ (aX : ZMod (5 ^ 1)) := by
    rw [← map_mul, hb2]
    have : -(aX : ZMod (5 ^ 1)) = (-1) * (aX : ZMod (5 ^ 1)) := by ring
    rw [this, map_mul, hψo]; ring
  have h2ne : ψ (2 : ZMod (5 ^ 1)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (5 ^ 1)).2 (by norm_num)
    simpa using this
  have hψbv : ψ (b : ZMod (5 ^ 1)) = - ψ (aX : ZMod (5 ^ 1)) * (ψ (2 : ZMod (5 ^ 1)))⁻¹ := by
    field_simp
    linear_combination hψb
  have hXne : ψ (aX : ZMod (5 ^ 1)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hX5).symm
  have h3ne : (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹) ≠ 0 := by
    intro h0
    apply Erdos634.GA2NF1.psi_three_ne_one 1 le_rfl ψ hψ
    have : (ψ (3 : ZMod (5 ^ 1)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    simpa using inv_eq_one.1 this
  rw [hcast, hψbv, ← hE] at hbot
  have key : (2 * ψ (aX : ZMod (5 ^ 1)) * (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹)) *
      (eX * (1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹) - eS * (ψ (2 : ZMod (5 ^ 1)))⁻¹) = 0 := by
    linear_combination hbot
  have := (mul_eq_zero.1 key).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero hXne) h3ne)
  linear_combination this


theorem bottomA (j : ℕ) (hj : 1 ≤ j) (aX aY aS b : ℕ) (eX eY eS : ℂ)
    (hY : aY = aX + 2 * (5 * 3 ^ j)) (hb : aX + 2 * b = 5 * 3 ^ j) (hZ : aS = 4 * b)
    (hX5 : ¬ 5 ∣ aX) (hX3 : ¬ 3 ∣ aX) (hXo : aX % 2 = 1) (hE : eX = eY)
    (H : H3B j aX aY aS eX eY eS) : eX = 0 := by
  obtain ⟨ψ, hψ, hψo⟩ := exists_odd_psi
  have h1 := eqA j hj aX aY aS b eX eY eS hY hb hZ hX5 hX3 hXo hE H ψ hψ hψo
  have hψ' : (ψ⁻¹).IsPrimitive :=
    Erdos634.GA2PC.five_prim_of_ne_one ψ⁻¹ (inv_ne_one.2 (prim_ne_one ψ hψ))
  have hψ'o : ψ⁻¹ (-1) = -1 := by
    rw [MulChar.inv_apply_eq_inv', hψo]; norm_num
  have h2 := eqA j hj aX aY aS b eX eY eS hY hb hZ hX5 hX3 hXo hE H ψ⁻¹ hψ' hψ'o
  rw [MulChar.inv_apply_eq_inv', inv_inv] at h2
  have hsq : ψ (2 : ZMod (5 ^ 1)) * ψ (2 : ZMod (5 ^ 1)) = -1 := by
    rw [← map_mul]
    have : (2 : ZMod (5 ^ 1)) * 2 = -1 := by decide
    rw [this, hψo]
  have hinv : (ψ (2 : ZMod (5 ^ 1)))⁻¹ = -ψ (2 : ZMod (5 ^ 1)) :=
    inv_eq_of_mul_eq_one_right (by linear_combination -hsq)
  rw [hinv] at h1
  linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2

theorem bottomB (j : ℕ) (hj : 1 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hsXY : aX + aY = 2 * (5 * 3 ^ j)) (hS : aS = 2 * (5 * 3 ^ j))
    (hX5 : ¬ 5 ∣ aX) (hX3 : ¬ 3 ∣ aX) (hXo : aX % 2 = 1)
    (H : H3B j aX aY aS eX eY eS) : eX = eY := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, hψo⟩ := exists_odd_psi
  have h3N : 3 ∣ 5 * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 5
  have h5N : 5 ∣ 5 * 3 ^ j := dvd_mul_right _ _
  generalize hN : 5 * 3 ^ j = N at *
  have hY5 : ¬ 5 ∣ aY := by omega
  have hY3 : ¬ 3 ∣ aY := by omega
  have hYo : aY % 2 = 1 := by omega
  have hS5 : 5 ∣ aS := by omega
  have hbot := H ψ hψ 1 1 (one_neg_one_B j ψ hψo)
  rw [bracket_triv_odd j hj ψ hψ aX hX5 (unit_cop j aX hXo hX3),
    bracket_triv_odd j hj ψ hψ aY hY5 (unit_cop j aY hYo hY3),
    bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 2 j) hψ _ aS hS5] at hbot
  have hcast : (aY : ZMod (5 ^ 1)) = -(aX : ZMod (5 ^ 1)) := by
    have : ((aX + aY : ℕ) : ZMod (5 ^ 1)) = 0 := by rw [hsXY]; exact zmod5_of_dvd _ (by omega)
    push_cast at this
    linear_combination this
  have hψy : ψ (aY : ZMod (5 ^ 1)) = - ψ (aX : ZMod (5 ^ 1)) := by
    rw [hcast]
    have : -(aX : ZMod (5 ^ 1)) = (-1) * (aX : ZMod (5 ^ 1)) := by ring
    rw [this, map_mul, hψo]; ring
  have hXne : ψ (aX : ZMod (5 ^ 1)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hX5).symm
  have h2ne : (1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹) ≠ 0 := by
    intro h0
    apply Erdos634.GA2NF1.psi_two_ne_one 1 le_rfl ψ hψ
    have : (ψ (2 : ZMod (5 ^ 1)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    simpa using inv_eq_one.1 this
  have h3ne : (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹) ≠ 0 := by
    intro h0
    apply Erdos634.GA2NF1.psi_three_ne_one 1 le_rfl ψ hψ
    have : (ψ (3 : ZMod (5 ^ 1)))⁻¹ = 1 := by linear_combination (-1 : ℂ) * h0
    simpa using inv_eq_one.1 this
  rw [hψy] at hbot
  have key : (ψ (aX : ZMod (5 ^ 1)) * ((1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹) * (1 - (ψ (3 : ZMod (5 ^ 1)))⁻¹))) *
      (eX - eY) = 0 := by
    linear_combination hbot
  have := (mul_eq_zero.1 key).resolve_left (mul_ne_zero hXne (mul_ne_zero h2ne h3ne))
  linear_combination this



theorem m0_odd (j : ℕ) : (5 * 3 ^ j) % 2 = 1 := by
  have : Odd (5 * 3 ^ j) := Nat.odd_mul.2 ⟨by decide, Odd.pow (by decide)⟩
  exact Nat.odd_iff.1 this

theorem not3_of_cop (j : ℕ) (hj : 1 ≤ j) (x : ℕ) (h : Nat.Coprime (2 ^ 2 * 3 ^ j) x) : ¬ 3 ∣ x := by
  have h3 : 3 ∣ 2 ^ 2 * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (Nat.Coprime.coprime_dvd_left h3 h)

theorem stepB1 (j : ℕ) (hj : 2 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hYo : aY % 2 = 1) (hSe : aS % 2 = 0)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hS0 : 0 < aS)
    (hsum : aX + aY + aS = 4 * (5 * 3 ^ j))
    (H : H3B j aX aY aS eX eY eS) (hvX : ¬ 5 ∣ aX ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aX) :
    eX = 0 ∨ (aX = aY ∧ eX + eY = 0) := by
  obtain ⟨χ4, hχ4, hχ4o⟩ := exists_chi4
  have EQ := B_eq1 j hj aX aY aS eX eY eS hSe H χ4 hχ4 hχ4o hvX
  have hm0 := m0_odd j
  have hX3 : ¬ 3 ∣ aX := not3_of_cop j (by omega) aX hvX.2
  have hχX : χ4 (aX : ZMod (2 ^ 2)) ≠ 0 := chi4_ne_zero χ4 hχ4o aX hXo
  have h3N : 3 ∣ 5 * 3 ^ j := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 5
  have h5N : 5 ∣ 5 * 3 ^ j := dvd_mul_right _ _
  by_cases hcase : ((¬ 5 ∣ aY ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aY) ∧
      (aY ≡ aX [MOD 5 * 3 ^ j] ∨ 5 * 3 ^ j ∣ aX + aY))
  · rw [if_pos hcase] at EQ
    obtain ⟨hvY, hMatch⟩ := hcase
    have hχY : χ4 (aY : ZMod (2 ^ 2)) ≠ 0 := chi4_ne_zero χ4 hχ4o aY hYo
    have hcvX := chi4_val χ4 hχ4o aX hXo
    have hcvY := chi4_val χ4 hχ4o aY hYo
    rcases hMatch with hm | hm
    · -- aY = aX mod m0
      have hsh := shape_plus (5 * 3 ^ j) aY aX hm0 hYo hXo hY0 hX0 (by omega) (by omega) hm
      rcases hsh with h | h | h
      · -- same value
        right
        refine ⟨h.symm, ?_⟩
        rw [h] at EQ
        have : (eX + eY) * χ4 (aX : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
        exact (mul_eq_zero.1 this).resolve_right hχX
      · -- shape A, aY = aX + 2 m0
        left
        have hneq : eX = eY := by
          have hf : χ4 (aY : ZMod (2 ^ 2)) = - χ4 (aX : ZMod (2 ^ 2)) := by
            rw [hcvX, hcvY]
            have : aY % 4 = if aX % 4 = 1 then 3 else 1 := by split_ifs <;> omega
            split_ifs <;> first | rfl | omega | norm_num
          rw [hf] at EQ
          have : (eX - eY) * χ4 (aX : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
          have := (mul_eq_zero.1 this).resolve_right hχX
          linear_combination this
        refine bottomA j (by omega) aX aY aS ((5 * 3 ^ j - aX) / 2) eX eY eS (by omega) (by omega)
          (by omega) hvX.1 hX3 hXo hneq H
      · -- aX = aY + 2 m0
        left
        have hneq : eY = eX := by
          have hf : χ4 (aX : ZMod (2 ^ 2)) = - χ4 (aY : ZMod (2 ^ 2)) := by
            rw [hcvX, hcvY]
            split_ifs <;> first | rfl | omega | norm_num
          rw [hf] at EQ
          have : (eY - eX) * χ4 (aY : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
          have := (mul_eq_zero.1 this).resolve_right hχY
          linear_combination this
        have hY3 : ¬ 3 ∣ aY := not3_of_cop j (by omega) aY hvY.2
        have := bottomA j (by omega) aY aX aS ((5 * 3 ^ j - aY) / 2) eY eX eS (by omega) (by omega)
          (by omega) hvY.1 hY3 hYo hneq (H3B_swap H)
        rw [← hneq]; exact this
    · -- aX + aY = 2 m0
      left
      have hsh := shape_minus (5 * 3 ^ j) aX aY hm0 hXo hYo hX0 hY0 (by omega) hm
      have hcv : χ4 (aY : ZMod (2 ^ 2)) = χ4 (aX : ZMod (2 ^ 2)) := by
        rw [hcvX, hcvY]
        split_ifs <;> first | rfl | omega | norm_num
      rw [hcv] at EQ
      have h1 : (eX + eY) * χ4 (aX : ZMod (2 ^ 2)) = 0 := by linear_combination EQ
      have h2 := (mul_eq_zero.1 h1).resolve_right hχX
      have h3 := bottomB j (by omega) aX aY aS eX eY eS hsh (by omega) hvX.1 hX3 hXo H
      linear_combination (1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h3
  · rw [if_neg hcase, add_zero] at EQ
    left
    exact (mul_eq_zero.1 EQ).resolve_right hχX


theorem exists_L1char (j : ℕ) (D : ℕ) (hD : D ∣ 3 ^ j) (χ4 : DirichletCharacter ℂ (2 ^ 2))
    (hχ4o : χ4 (-1) = -1) :
    ∃ (ψ : DirichletCharacter ℂ (5 ^ 1)) (η3 : DirichletCharacter ℂ (3 ^ j)),
      ψ.IsPrimitive ∧ η3.conductor = D ∧ ψ (-1) * χ4 (-1) * η3 (-1) = -1 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨l, hl, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hD
  rcases Nat.eq_zero_or_pos l with rfl | hlp
  · obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 1 le_rfl 1 (Or.inl rfl)
    obtain ⟨hψp, hψs⟩ := Erdos634.GA2LCore.mem_PrimPar.1 hψ
    refine ⟨ψ, 1, hψp, by simpa using (DirichletCharacter.conductor_one : (1 : DirichletCharacter ℂ (3 ^ j)).conductor = 1), ?_⟩
    rw [hψs, hχ4o, MulChar.one_apply (isUnit_one.neg)]; norm_num
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hodd3 : 3 ^ l % 2 = 1 := by
      have : Odd (3 ^ l) := Odd.pow (by decide)
      exact Nat.odd_iff.1 this
    obtain ⟨ω, hωp, hωo⟩ := (Erdos634.LemmaSParity.exists_odd_primitive_iff
      (d := 3 ^ l) (pow_ne_zero _ (by norm_num)) (by omega)).2
      ⟨by
        intro h
        have : 3 ^ 1 ≤ 3 ^ l := Nat.pow_le_pow_right (by norm_num) hlp
        omega, by omega⟩
    haveI : NeZero (3 ^ l) := ⟨pow_ne_zero _ (by norm_num)⟩
    obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 1 le_rfl (-1) (Or.inr rfl)
    obtain ⟨hψp, hψs⟩ := Erdos634.GA2LCore.mem_PrimPar.1 hψ
    refine ⟨ψ, changeLevel (pow_dvd_pow 3 hl) ω, hψp,
      Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive (pow_dvd_pow 3 hl) hωp, ?_⟩
    have hω1 : ω (-1) = -1 := hωo
    rw [Erdos634.GA2NB2.changeLevel_neg_one, hω1, hψs, hχ4o]; norm_num

theorem bracket_even_zero (j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4 : χ4.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (a : ℕ) (hSe : a % 2 = 0) :
    bracket (chi ψ (chi χ4 η3)) a = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases h5 : 5 ∣ a
  · exact bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 2 j) hψ _ a h5
  · rw [bracket_gen2 1 2 j ψ hψ χ4 η3 a h5, if_neg]
    intro hdv
    have hc4 : χ4.conductor = 2 ^ 2 := hχ4
    have h4 : 4 ∣ dm (2 ^ 2 * 3 ^ j) a := by
      have : 2 ^ 2 ∣ χ4.conductor * η3.conductor := by rw [hc4]; exact dvd_mul_right _ _
      simpa using this.trans hdv
    have hg : (2 ^ 2 * 3 ^ j).gcd a ∣ 2 ^ 2 * 3 ^ j := Nat.gcd_dvd_left _ _
    have h2g : 2 ∣ (2 ^ 2 * 3 ^ j).gcd a :=
      Nat.dvd_gcd (Dvd.dvd.mul_right (by norm_num) _) (by omega)
    have hmul : dm (2 ^ 2 * 3 ^ j) a * (2 ^ 2 * 3 ^ j).gcd a = 2 ^ 2 * 3 ^ j := Nat.div_mul_cancel hg
    have h8 : 2 * 4 ∣ 2 ^ 2 * 3 ^ j := by
      rw [← hmul]; exact Nat.mul_dvd_mul h2g h4 |>.trans (by rw [mul_comm])
    have h2j : 2 ∣ 3 ^ j := by
      have : 2 ^ 2 * 2 ∣ 2 ^ 2 * 3 ^ j := by simpa [mul_comm] using h8
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2j
    omega


theorem stepB2 (j : ℕ) (hj : 2 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hSe : aS % 2 = 0)
    (H : H3B j aX aY aS eX eY eS) (hX5 : ¬ 5 ∣ aX) (hY : eY = 0 ∨ 5 ∣ aY) : eX = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨χ4, hχ4, hχ4o⟩ := exists_chi4
  have hD : 3 ^ j / Nat.gcd (3 ^ j) aX ∣ 3 ^ j := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨ψ, η3, hψ, hη3, hodd⟩ := exists_L1char j _ hD χ4 hχ4o
  have hbot := H ψ hψ χ4 η3 hodd
  have hX : bracket (chi ψ (chi χ4 η3)) aX ≠ 0 := by
    refine bracket_ne_zero_of_eq2 1 2 j ψ hψ χ4 η3 aX hX5 ?_
    rw [dm_odd2 2 j aX (Nat.odd_iff.2 hXo) (by norm_num), hη3]
    have hc4 : χ4.conductor = 2 ^ 2 := hχ4
    rw [hc4]
  have hS := bracket_even_zero j ψ hψ χ4 hχ4 η3 aS hSe
  have hYt : eY * bracket (chi ψ (chi χ4 η3)) aY = 0 := by
    rcases hY with h | h
    · rw [h, zero_mul]
    · rw [bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 2 j) hψ _ aY h, mul_zero]
  rw [hS, hYt, mul_zero, add_zero, add_zero] at hbot
  exact (mul_eq_zero.1 hbot).resolve_right hX

def Good (aX aY : ℕ) (eX eY : ℂ) : Prop := 5 ∣ aX ∨ eX = 0 ∨ (aX = aY ∧ eX + eY = 0)

theorem pair_zero (B : ℕ → ℂ) (hB5 : ∀ x, 5 ∣ x → B x = 0) (aX aY : ℕ) (eX eY : ℂ)
    (hX : Good aX aY eX eY) (hY : Good aY aX eY eX) : eX * B aX + eY * B aY = 0 := by
  rcases hX with h | h | ⟨h1, h2⟩
  · rw [hB5 _ h, mul_zero, zero_add]
    rcases hY with h' | h' | ⟨h1, h2⟩
    · rw [hB5 _ h', mul_zero]
    · rw [h', zero_mul]
    · have h5Y : 5 ∣ aY := by rw [h1]; exact h
      rw [hB5 _ h5Y, mul_zero]
  · rw [h, zero_mul, zero_add]
    rcases hY with h' | h' | ⟨h1, h2⟩
    · rw [hB5 _ h', mul_zero]
    · rw [h', zero_mul]
    · rw [h] at h2; rw [show eY = 0 by linear_combination h2, zero_mul]
  · rw [← h1]
    linear_combination (B aX) * h2

theorem stepB3 (j : ℕ) (hj : 2 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (H : H3B j aX aY aS eX eY eS) (hS5 : ¬ 5 ∣ aS)
    (hX : Good aX aY eX eY) (hY : Good aY aX eY eX) : eS = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, hψo⟩ := exists_odd_psi
  have hbot := H ψ hψ 1 1 (one_neg_one_B j ψ hψo)
  set B : ℕ → ℂ := fun x => bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 2)) (1 : DirichletCharacter ℂ (3 ^ j)))) x with hB
  have hB5 : ∀ x, 5 ∣ x → B x = 0 := fun x hx =>
    bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 2 j) hψ _ x hx
  have hBne : B aS ≠ 0 :=
    bracket_triv_ne_zero2 1 2 j ψ hψ (Erdos634.GA2NF1.psi_two_ne_one 1 le_rfl ψ hψ)
      (Erdos634.GA2NF1.psi_three_ne_one 1 le_rfl ψ hψ) aS hS5
  have hz := pair_zero B hB5 aX aY eX eY hX hY
  have : eX * B aX + eY * B aY + eS * B aS = 0 := hbot
  rw [hz, zero_add] at this
  exact (mul_eq_zero.1 this).resolve_right hBne

/-- If X is an odd entry prime to 5 then Good X Y, assuming the other odd entry Y is not also divisible by 3
when X is. -/
theorem goodX (j : ℕ) (hj : 2 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ)
    (hXo : aX % 2 = 1) (hYo : aY % 2 = 1) (hSe : aS % 2 = 0)
    (hX0 : 0 < aX) (hY0 : 0 < aY) (hS0 : 0 < aS)
    (hsum : aX + aY + aS = 4 * (5 * 3 ^ j))
    (hno3 : ¬ (3 ∣ aX ∧ 3 ∣ aY))
    (H : H3B j aX aY aS eX eY eS) : Good aX aY eX eY := by
  by_cases h5 : 5 ∣ aX
  · exact Or.inl h5
  · by_cases h3 : 3 ∣ aX
    · -- leftover
      right; left
      have hY3 : ¬ 3 ∣ aY := fun h => hno3 ⟨h3, h⟩
      refine stepB2 j hj aX aY aS eX eY eS hXo hSe H h5 ?_
      by_cases h5Y : 5 ∣ aY
      · exact Or.inr h5Y
      · left
        have := stepB1 j hj aY aX aS eY eX eS hYo hXo hSe hY0 hX0 hS0 (by omega) (H3B_swap H)
          ⟨h5Y, unit_cop j aY hYo hY3⟩
        rcases this with h | ⟨h, _⟩
        · exact h
        · exfalso; exact hY3 (by rw [h]; exact h3)
    · right
      exact stepB1 j hj aX aY aS eX eY eS hXo hYo hSe hX0 hY0 hS0 hsum H ⟨h5, unit_cop j aX hXo h3⟩


/-- **Theorem B (labelled form, i = 2, r = 1, j >= 2).** n = 4 * 5 * 3^j; P, Q the odd entries, S the even entry. -/
theorem theoremB_lab (j : ℕ) (hj : 2 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : aP % 2 = 1) (hQo : aQ % 2 = 1) (hSe : aS % 2 = 0)
    (hP0 : 0 < aP) (hQ0 : 0 < aQ) (hS0 : 0 < aS)
    (hsum : aP + aQ + aS = 4 * (5 * 3 ^ j))
    (hgcd : Nat.gcd (Nat.gcd aP aQ) aS = 1)
    (H : H3B j aP aQ aS eP eQ eS) :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if aP = x then eP else 0) + (if aQ = x then eQ else 0) + (if aS = x then eS else 0) = 0 := by
  have h3N : 3 ∣ 4 * (5 * 3 ^ j) := Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 5) 4
  have hno3 : ¬ (3 ∣ aP ∧ 3 ∣ aQ) := by
    rintro ⟨h1, h2⟩
    have h3 : 3 ∣ aS := by omega
    have := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [hgcd] at this
    omega
  have GP : Good aP aQ eP eQ := goodX j hj aP aQ aS eP eQ eS hPo hQo hSe hP0 hQ0 hS0 hsum hno3 H
  have GQ : Good aQ aP eQ eP := goodX j hj aQ aP aS eQ eP eS hQo hPo hSe hQ0 hP0 hS0 (by omega)
    (fun h => hno3 ⟨h.2, h.1⟩) (H3B_swap H)
  intro x hx
  have hSP : aS ≠ aP := by intro h; omega
  have hSQ : aS ≠ aQ := by intro h; omega
  by_cases hSx : aS = x
  · have hS5 : ¬ 5 ∣ aS := by rw [hSx]; exact hx
    have heS := stepB3 j hj aP aQ aS eP eQ eS H hS5 GP GQ
    rw [if_neg (fun h => hSP (by rw [hSx, h])), if_neg (fun h => hSQ (by rw [hSx, h])), if_pos hSx, heS]
    ring
  · rw [if_neg hSx, add_zero]
    by_cases hPx : aP = x
    · have hP5 : ¬ 5 ∣ aP := by rw [hPx]; exact hx
      by_cases hQx : aQ = x
      · have hQ5 : ¬ 5 ∣ aQ := by rw [hQx]; exact hx
        rw [if_pos hPx, if_pos hQx]
        rcases GP with h | h | ⟨_, h⟩
        · exact absurd h hP5
        · rcases GQ with h' | h' | ⟨_, h'⟩
          · exact absurd h' hQ5
          · rw [h, h']; ring
          · linear_combination h'
        · exact h
      · rw [if_pos hPx, if_neg hQx, add_zero]
        rcases GP with h | h | ⟨h, _⟩
        · exact absurd h hP5
        · exact h
        · exfalso; apply hQx; rw [← h]; exact hPx
    · rw [if_neg hPx, zero_add]
      by_cases hQx : aQ = x
      · have hQ5 : ¬ 5 ∣ aQ := by rw [hQx]; exact hx
        rw [if_pos hQx]
        rcases GQ with h | h | ⟨h, _⟩
        · exact absurd h hQ5
        · exact h
        · exfalso; apply hPx; rw [← h]; exact hQx
      · rw [if_neg hQx]

end Erdos634.GA2PG

#print axioms Erdos634.GA2PG.stepB2
#print axioms Erdos634.GA2PG.stepB3
#print axioms Erdos634.GA2PG.goodX
#print axioms Erdos634.GA2PG.theoremB_lab
