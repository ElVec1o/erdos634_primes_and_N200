/-
GA2N, item (3), A5 and A4 of Theorem A: the two SHAPE KILLS.

Setting: n = 2^(k+3) 3^j 5^r (k >= 0, j, r >= 1), M = 2^(k+3) 3^j, h = n/2 = 2^(k+2) 3^j 5^r.
`kill_B` (shape B, Lemma A5): aP + aQ = h, eQ = -eP, aP odd coprime to 15  ==>  eP = 0     [BOTTOM: eta = 1, psi odd]
`kill_A` (shape A, Lemma A4): aH = aL + h, eH = eL,  aL odd coprime to 15, aS > 0 ==> eL = 0
    [MID: eta2 odd of conductor 2^(k+2), eta3 odd of conductor 3, psi odd:  T_H = T_L, T_S = 2 T_L  => eS = -e;
     BOTTOM: T_H = T_L, T_S = -2 T_L  => eS = e;   hence e = 0.]
Both use the hypothesis `H` = the full odd-character system over (psi prim mod 5^r, eta2 mod 2^(k+3) ARBITRARY, eta3 mod 3^j ARBITRARY).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NB2

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NK

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2MTop Erdos634.GA2NB Erdos634.GA2NB2 Erdos634.GA2NR1 Erdos634.GA2NF1 Erdos634.GA2LCore
open Erdos634.GA2LGroup

/-! ## arithmetic helpers -/

theorem cop_M (k j a : ℕ) (ha : Odd a) (h3 : ¬ 3 ∣ a) : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a := by
  refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ?_) (Nat.Coprime.pow_left _ ?_)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 ha)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3

theorem cast_neg_of_dvd (x y m : ℕ) (h : m ∣ x + y) : (x : ZMod m) = -(y : ZMod m) := by
  have : ((x + y : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at this
  linear_combination this

theorem cast_eq_add_mul (y t m : ℕ) : ((y + m * t : ℕ) : ZMod m) = (y : ZMod m) := by
  push_cast
  simp

theorem primeFactors_23 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : (2 ^ a * 3 ^ b).primeFactors = {2, 3} := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity), Nat.primeFactors_prime_pow (by omega) Nat.prime_two,
    Nat.primeFactors_prime_pow (by omega) Nat.prime_three]
  rfl

/-- Closed form of the trivial-eta bracket at a unit a (gcd(M,a) = 1). -/
theorem bracket_triv_coprime (r k j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (a : ℕ) (ha5 : ¬ 5 ∣ a) (hc : Nat.Coprime (2 ^ (k + 3) * 3 ^ j) a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ (k + 3))) (1 : DirichletCharacter ℂ (3 ^ j)))) a =
      ψ (a : ZMod (5 ^ r)) *
        ∏ ℓ ∈ Nat.primeFactors (2 ^ (k + 3) * 3 ^ j), (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹) := by
  rw [bracket_triv_formula r k j ψ hψ a ha5]
  have hg : (2 ^ (k + 3) * 3 ^ j).gcd a = 1 := hc
  have hdm : dm (2 ^ (k + 3) * 3 ^ j) a = 2 ^ (k + 3) * 3 ^ j := by
    unfold dm; rw [hg, Nat.div_one]
  have hφ : ((2 ^ (k + 3) * 3 ^ j).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
  rw [hdm, hg, Nat.div_one, div_self hφ, one_mul]

/-! ## A5: shape B -/

theorem kill_B (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eS : ℂ)
    (hPo : Odd aP) (hQo : Odd aQ) (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hP5 : ¬ 5 ∣ aP) (hQ5 : ¬ 5 ∣ aQ)
    (hsum : aP + aQ + aS = 2 ^ (k + 3) * (3 ^ j * 5 ^ r))
    (hshape : aP + aQ = 2 ^ (k + 2) * (3 ^ j * 5 ^ r))
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eP * bracket (chi ψ (chi η2 η3)) aP + (-eP) * bracket (chi ψ (chi η2 η3)) aQ +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    eP = 0 := by
  obtain ⟨ψ, hψ⟩ := nonempty5 r hr (-1) (Or.inr rfl)
  obtain ⟨hψp, hψs⟩ := mem_PrimPar.1 hψ
  have hS5 : 5 ∣ aS := by
    have h1 : aS = 2 ^ (k + 2) * (3 ^ j * 5 ^ r) := by
      have : 2 ^ (k + 3) * (3 ^ j * 5 ^ r) = 2 * (2 ^ (k + 2) * (3 ^ j * 5 ^ r)) := by ring
      omega
    rw [h1]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_pow_self 5 (by omega)) _) _
  have h := H ψ hψp 1 1 (by simp [MulChar.one_apply (isUnit_one.neg), hψs])
  rw [bracket_p_dvd hr (not5_dvd k j) hψp _ aS hS5, mul_zero, add_zero] at h
  rw [bracket_triv_coprime r k j hj ψ hψp aP hP5 (cop_M k j aP hPo hP3),
    bracket_triv_coprime r k j hj ψ hψp aQ hQ5 (cop_M k j aQ hQo hQ3)] at h
  have hq : (aQ : ZMod (5 ^ r)) = -(aP : ZMod (5 ^ r)) := by
    apply cast_neg_of_dvd
    rw [add_comm, hshape]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_refl _) _) _
  have hneg : ψ (-(aP : ZMod (5 ^ r))) = -ψ (aP : ZMod (5 ^ r)) := by
    rw [neg_eq_neg_one_mul, map_mul, hψs]; ring
  rw [hq, hneg] at h
  have hne := bracket_triv_ne_zero r k j hj ψ hψp (psi_two_ne_one r hr ψ hψp) (psi_three_ne_one r hr ψ hψp)
    aP hP5
  rw [bracket_triv_coprime r k j hj ψ hψp aP hP5 (cop_M k j aP hPo hP3)] at hne
  have h2 : eP * (ψ (aP : ZMod (5 ^ r)) * ∏ ℓ ∈ Nat.primeFactors (2 ^ (k + 3) * 3 ^ j),
      (1 - (ψ (ℓ : ZMod (5 ^ r)))⁻¹)) * 2 = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact (mul_eq_zero.1 h3).resolve_right hne
  · norm_num at h3

/-! ## A4: shape A -/

theorem cop_23 (a b c : ℕ) (hc : Odd c) (h3 : ¬ 3 ∣ c) : Nat.Coprime (2 ^ a * 3 ^ b) c := by
  refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ?_) (Nat.Coprime.pow_left _ ?_)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hc)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3

theorem F5_mid (k N : ℕ) (hN : N = 2 ^ (k + 2)) (η : DirichletCharacter ℂ N) (hη : η.IsPrimitive)
    (hodd : η (-1) = -1) : η ((1 + 2 ^ (k + 1) : ℕ) : ZMod N) = -1 := by
  subst hN
  rcases k with _ | k'
  · have : (((1 + 2 ^ (0 + 1) : ℕ)) : ZMod (2 ^ (0 + 2))) = -1 := by decide
    rw [this, hodd]
  · have := eta2_val k' η hη
    push_cast
    exact this

theorem totient_half (k j : ℕ) :
    (2 ^ (k + 3) * 3 ^ j).totient = 2 * (2 ^ (k + 2) * 3 ^ j).totient := by
  have hc : ∀ e : ℕ, Nat.Coprime (2 ^ e) (3 ^ j) := fun e => Nat.Coprime.pow _ _ (by norm_num)
  rw [Nat.totient_mul (hc _), Nat.totient_mul (hc _), Nat.totient_prime_pow Nat.prime_two (by omega),
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  have e1 : k + 3 - 1 = (k + 2 - 1) + 1 := by omega
  rw [e1, pow_succ]
  ring

theorem cast_eq_of_dvd (x y m d : ℕ) (hx : x = y + d) (hd : m ∣ d) : (x : ZMod m) = (y : ZMod m) := by
  obtain ⟨t, ht⟩ := hd
  rw [hx, ht]
  exact cast_eq_add_mul y t m

theorem kill_A (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (aL aH aS : ℕ) (eL eS : ℂ)
    (hLo : Odd aL) (hL3 : ¬ 3 ∣ aL) (hL5 : ¬ 5 ∣ aL) (hS0 : 0 < aS)
    (hsum : aL + aH + aS = 2 ^ (k + 3) * (3 ^ j * 5 ^ r))
    (hshape : aH = aL + 2 ^ (k + 2) * (3 ^ j * 5 ^ r))
    (H : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
        ψ (-1) * η2 (-1) * η3 (-1) = -1 →
        eL * bracket (chi ψ (chi η2 η3)) aL + eL * bracket (chi ψ (chi η2 η3)) aH +
          eS * bracket (chi ψ (chi η2 η3)) aS = 0) :
    eL = 0 := by
  -- arithmetic of the shape
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = 3 ^ j * 5 ^ r := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 2 ^ (k + 1) * u := ⟨_, rfl⟩
  have hT2 : 2 ^ (k + 2) * (3 ^ j * 5 ^ r) = 2 * T := by rw [hT, hu]; ring
  have hT4 : 2 ^ (k + 3) * (3 ^ j * 5 ^ r) = 4 * T := by rw [hT, hu]; ring
  have hTe : T % 2 = 0 := by
    have : T = 2 * (2 ^ k * u) := by rw [hT]; ring
    omega
  have h3T : 3 ∣ T := ⟨2 ^ (k + 1) * 3 ^ (j - 1) * 5 ^ r, by
    rw [hT, hu]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring⟩
  have h5T : 5 ∣ T := ⟨2 ^ (k + 1) * 3 ^ j * 5 ^ (r - 1), by
    rw [hT, hu]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring⟩
  have h5rT : 5 ^ r ∣ T := ⟨2 ^ (k + 1) * 3 ^ j, by rw [hT, hu]; ring⟩
  rw [hT2] at hshape
  rw [hT4] at hsum
  have hLo' : aL % 2 = 1 := Nat.odd_iff.1 hLo
  obtain ⟨c, hc⟩ : ∃ c, c = T - aL := ⟨_, rfl⟩
  have hcL : c + aL = T := by omega
  have hS2 : aS = 2 * c := by omega
  have hco : c % 2 = 1 := by omega
  have hc3 : ¬ 3 ∣ c := by omega
  have hc5 : ¬ 5 ∣ c := by omega
  have hcodd : Odd c := Nat.odd_iff.2 hco
  have hHodd : Odd aH := by rw [Nat.odd_iff]; omega
  have hH3 : ¬ 3 ∣ aH := by omega
  have hH5 : ¬ 5 ∣ aH := by omega
  have hMM2 : 2 ^ (k + 3) * 3 ^ j = 2 * (2 ^ (k + 2) * 3 ^ j) := by ring
  have hMpos : 0 < 2 ^ (k + 3) * 3 ^ j := by positivity
  have hgL : Nat.gcd (2 ^ (k + 3) * 3 ^ j) aL = 1 := cop_M k j aL hLo hL3
  have hgH : Nat.gcd (2 ^ (k + 3) * 3 ^ j) aH = 1 := cop_M k j aH hHodd hH3
  have hgS : Nat.gcd (2 ^ (k + 3) * 3 ^ j) aS = 2 := by
    rw [hS2, hMM2, Nat.gcd_mul_left]
    have : Nat.gcd (2 ^ (k + 2) * 3 ^ j) c = 1 := cop_23 (k + 2) j c hcodd hc3
    rw [this]
  have hdmS : (2 ^ (k + 3) * 3 ^ j) / 2 = 2 ^ (k + 2) * 3 ^ j := by omega
  have hcS : aS / 2 = c := by omega
  -- congruences
  have d2T : 2 ^ (k + 2) ∣ 2 * T := ⟨3 ^ j * 5 ^ r, by rw [← hT2]⟩
  have e5c : (c : ZMod (5 ^ r)) = -(aL : ZMod (5 ^ r)) := by
    apply cast_neg_of_dvd
    rw [hcL]; exact h5rT
  have e5H : (aH : ZMod (5 ^ r)) = (aL : ZMod (5 ^ r)) :=
    cast_eq_of_dvd aH aL _ (2 * T) hshape (Dvd.dvd.mul_left h5rT 2)
  -- MID characters
  obtain ⟨ψ, η2, η3, hψp, hc2, hc3', hψo, h2o, h3o⟩ := exists_mid r k j hr hj
  have hmid := H ψ hψp η2 η3 (by rw [hψo, h2o, h3o]; norm_num)
  have hdvdM : 2 ^ (k + 2) * 3 ∣ 2 ^ (k + 3) * 3 ^ j :=
    mul_dvd_mul (pow_dvd_pow 2 (by omega)) (dvd_pow_self 3 (by omega))
  have hdvdM2 : 2 ^ (k + 2) * 3 ∣ 2 ^ (k + 2) * 3 ^ j :=
    mul_dvd_mul dvd_rfl (dvd_pow_self 3 (by omega))
  have h2f : 2 ∣ η2.conductor * η3.conductor := by
    rw [hc2, hc3']; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have h3f : 3 ∣ η2.conductor * η3.conductor := by
    rw [hc2, hc3']; exact Dvd.dvd.mul_left (dvd_refl 3) _
  have valL := bracket_val_noeuler r k j ψ hψp η2 η3 aL hL5 hj
    (by unfold dm; rw [hgL, Nat.div_one, hc2, hc3']; exact hdvdM) h2f h3f
  have valH := bracket_val_noeuler r k j ψ hψp η2 η3 aH hH5 hj
    (by unfold dm; rw [hgH, Nat.div_one, hc2, hc3']; exact hdvdM) h2f h3f
  have valS := bracket_val_noeuler r k j ψ hψp η2 η3 aS (by omega) hj
    (by unfold dm; rw [hgS, hdmS, hc2, hc3']; exact hdvdM2) h2f h3f
  unfold dm at valL valH valS
  rw [hgL, Nat.div_one, Nat.div_one, div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne')] at valL
  rw [hgH, Nat.div_one, Nat.div_one, div_self (by exact_mod_cast (Nat.totient_pos.2 hMpos).ne')] at valH
  rw [hgS, hdmS, hcS] at valS
  -- star values
  have hprim2 : η2.primitiveCharacter.IsPrimitive := primitiveCharacter_isPrimitive η2
  have hstar2 : η2.primitiveCharacter (-1 : ZMod η2.conductor) = -1 := by rw [star_neg_one, h2o]
  have hstar3 : η3.primitiveCharacter (-1 : ZMod η3.conductor) = -1 := by rw [star_neg_one, h3o]
  have hF5 : η2.primitiveCharacter ((1 + 2 ^ (k + 1) : ℕ) : ZMod η2.conductor) = -1 :=
    F5_mid k η2.conductor hc2 η2.primitiveCharacter hprim2 hstar2
  have c2H : (aH : ZMod η2.conductor) = (aL : ZMod η2.conductor) :=
    cast_eq_of_dvd aH aL _ (2 * T) hshape (by rw [hc2]; exact d2T)
  have c3H : (aH : ZMod η3.conductor) = (aL : ZMod η3.conductor) :=
    cast_eq_of_dvd aH aL _ (2 * T) hshape (by rw [hc3']; exact Dvd.dvd.mul_left h3T 2)
  have c3c : (c : ZMod η3.conductor) = -(aL : ZMod η3.conductor) := by
    apply cast_neg_of_dvd
    rw [hcL, hc3']; exact h3T
  have hu_odd : u % 2 = 1 := by
    have h3 : Odd ((3 : ℕ) ^ j) := Odd.pow (by decide)
    have h5 : Odd ((5 : ℕ) ^ r) := Odd.pow (by decide)
    have := Nat.odd_iff.1 (h3.mul h5)
    rw [hu]; exact this
  obtain ⟨w, hw⟩ : ∃ w, u + aL = 2 * w := ⟨(u + aL) / 2, by omega⟩
  have c2c : (c : ZMod η2.conductor) = -(((1 + 2 ^ (k + 1)) * aL : ℕ) : ZMod η2.conductor) := by
    apply cast_neg_of_dvd
    rw [hc2]
    refine ⟨w, ?_⟩
    calc c + (1 + 2 ^ (k + 1)) * aL = (c + aL) + 2 ^ (k + 1) * aL := by ring
      _ = 2 ^ (k + 1) * u + 2 ^ (k + 1) * aL := by rw [hcL, hT]
      _ = 2 ^ (k + 1) * (u + aL) := by ring
      _ = 2 ^ (k + 1) * (2 * w) := by rw [hw]
      _ = 2 ^ (k + 2) * w := by ring
  have A2c : η2.primitiveCharacter (c : ZMod η2.conductor) = η2.primitiveCharacter (aL : ZMod η2.conductor) := by
    rw [c2c, Nat.cast_mul, neg_eq_neg_one_mul, map_mul, map_mul, hstar2, hF5]; ring
  have A3c : η3.primitiveCharacter (c : ZMod η3.conductor) = -η3.primitiveCharacter (aL : ZMod η3.conductor) := by
    rw [c3c, neg_eq_neg_one_mul, map_mul, hstar3]; ring
  have Pc : ψ (c : ZMod (5 ^ r)) = -ψ (aL : ZMod (5 ^ r)) := by
    rw [e5c, neg_eq_neg_one_mul, map_mul, hψo]; ring
  have hhalf : ((((2 ^ (k + 3) * 3 ^ j).totient : ℕ) : ℂ) / (((2 ^ (k + 2) * 3 ^ j).totient : ℕ) : ℂ)) = 2 := by
    have h2 : (((2 ^ (k + 2) * 3 ^ j).totient : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
    rw [div_eq_iff h2, totient_half k j]
    push_cast; ring
  rw [hhalf, Pc, A2c, A3c] at valS
  rw [e5H, c2H, c3H] at valH
  -- X != 0
  have hXne : ψ (aL : ZMod (5 ^ r)) * (η2.primitiveCharacter (aL : ZMod η2.conductor) *
      η3.primitiveCharacter (aL : ZMod η3.conductor)) ≠ 0 := by
    have hu5 : IsUnit ((aL : ℕ) : ZMod (5 ^ r)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hL5).symm
    have hc2' : Nat.Coprime aL η2.conductor := by
      rw [hc2]; exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hLo)).symm
    have hc3'' : Nat.Coprime aL η3.conductor := by
      rw [hc3']; exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hL3).symm
    exact mul_ne_zero (nz ψ _ hu5) (mul_ne_zero (Erdos634.LemmaSIso.primChar_ne_zero η2 _ hc2')
      (Erdos634.LemmaSIso.primChar_ne_zero η3 _ hc3''))
  rw [valL, valH, valS] at hmid
  have hmid2 : (ψ (aL : ZMod (5 ^ r)) * (η2.primitiveCharacter (aL : ZMod η2.conductor) *
      η3.primitiveCharacter (aL : ZMod η3.conductor))) * (2 * (eL + eS)) = 0 := by
    linear_combination hmid
  have hMID : eL + eS = 0 := by
    rcases mul_eq_zero.1 hmid2 with h | h
    · exact absurd h hXne
    · have : (2 : ℂ) ≠ 0 := two_ne_zero
      exact (mul_eq_zero.1 h).resolve_left this
  -- BOTTOM
  obtain ⟨ψb, hψb⟩ := nonempty5 r hr (-1) (Or.inr rfl)
  obtain ⟨hψbp, hψbs⟩ := mem_PrimPar.1 hψb
  have hbot := H ψb hψbp 1 1 (by simp [MulChar.one_apply (isUnit_one.neg), hψbs])
  rw [bracket_triv_coprime r k j hj ψb hψbp aL hL5 hgL,
    bracket_triv_coprime r k j hj ψb hψbp aH hH5 hgH] at hbot
  have hbotS := bracket_triv_formula r k j ψb hψbp aS (by omega)
  unfold dm at hbotS
  rw [hgS, hdmS, hcS] at hbotS
  rw [hbotS, hhalf] at hbot
  have hpf : Nat.primeFactors (2 ^ (k + 2) * 3 ^ j) = Nat.primeFactors (2 ^ (k + 3) * 3 ^ j) := by
    rw [primeFactors_23 (k + 2) j (by omega) hj, primeFactors_23 (k + 3) j (by omega) hj]
  rw [hpf] at hbot
  have Pcb : ψb (c : ZMod (5 ^ r)) = -ψb (aL : ZMod (5 ^ r)) := by
    rw [e5c, neg_eq_neg_one_mul, map_mul, hψbs]; ring
  rw [Pcb, e5H] at hbot
  have hnb := bracket_triv_ne_zero r k j hj ψb hψbp (psi_two_ne_one r hr ψb hψbp)
    (psi_three_ne_one r hr ψb hψbp) aL hL5
  rw [bracket_triv_coprime r k j hj ψb hψbp aL hL5 hgL] at hnb
  have hbot2 : (ψb (aL : ZMod (5 ^ r)) * ∏ ℓ ∈ Nat.primeFactors (2 ^ (k + 3) * 3 ^ j),
      (1 - (ψb (ℓ : ZMod (5 ^ r)))⁻¹)) * (2 * (eL - eS)) = 0 := by
    linear_combination hbot
  have hEq : eL - eS = 0 := by
    rcases mul_eq_zero.1 hbot2 with h | h
    · exact absurd h hnb
    · exact (mul_eq_zero.1 h).resolve_left two_ne_zero
  have h2L : (2 : ℂ) * eL = 0 := by linear_combination hMID + hEq
  exact (mul_eq_zero.1 h2L).resolve_left two_ne_zero

end Erdos634.GA2NK

#print axioms Erdos634.GA2NK.kill_B
#print axioms Erdos634.GA2NK.kill_A
