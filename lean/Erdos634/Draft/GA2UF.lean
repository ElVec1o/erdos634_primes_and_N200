/-
GA2U, atom F: Lemma T, case A (the 3-divisible entry T = S is the EVEN one; P, Q odd, both prime to 3).
  `F_ne_odd`   : psi odd mod 5 (r = 1), eta ANY character mod 3^j (j >= 1):  1 - psi(2)^-1 eta(2)^-1 != 0.
  `topA_eqn`   : H1 at (psi, eta primitive of the right parity):  (cP eta(aP) + cQ eta(aQ)) (1 - psi(2)^-1 eta(2)^-1) = 0,
                 cX = [5 !| aX] eX psi(aX).
  `two_tok`    : two unit tokens mod 3^j orthogonal to all primitive even eta:  (cP = cQ = 0) or (aQ = +-aP and cP + cQ = 0).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2UB
import Erdos634.Draft.GA2UA
import Erdos634.Draft.GA2SP
import Erdos634.Draft.GA2PJ
import Erdos634.Draft.GA2PG

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UF

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)
open Erdos634.GA2SP (H1 H1_swap unit_cop1)
open Erdos634.GA2SL (unit3)
open Erdos634.GA2SD (unit5r)
open Erdos634.GA2PA (not5_dvd')
open Erdos634.GA2PC (PhiV sum_PhiV)

theorem F_ne_odd (j : ℕ) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ (-1) = -1)
    (η : DirichletCharacter ℂ (3 ^ j)) :
    1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹ ≠ 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  intro h0
  have hs := Erdos634.GA2UA.psi_odd_sq ψ hψ
  have hs0 : ψ (2 : ZMod (5 ^ 1)) ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  have hη2 : η (2 : ZMod (3 ^ j)) ≠ 0 := by
    apply Erdos634.GA2LCore.nz
    have := (ZMod.isUnit_iff_coprime 2 (3 ^ j)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  -- eta(2) = psi(2)^-1, so eta(2)^2 = -1
  have h1 : η (2 : ZMod (3 ^ j)) * ψ (2 : ZMod (5 ^ 1)) = 1 := by
    field_simp at h0
    linear_combination h0
  have h2 : η (2 : ZMod (3 ^ j)) ^ 2 = -1 := by
    have : (η (2 : ZMod (3 ^ j)) * ψ (2 : ZMod (5 ^ 1))) ^ 2 = 1 := by rw [h1]; norm_num
    have e : (η (2 : ZMod (3 ^ j)) * ψ (2 : ZMod (5 ^ 1))) ^ 2 = η (2 : ZMod (3 ^ j)) ^ 2 * (-1) := by
      rw [mul_pow, pow_two (ψ _), hs]
    rw [e] at this
    linear_combination -this
  -- eta(2)^phi = 1 with phi = 3^(j-1) * 2
  have hu2 : IsUnit (2 : ZMod (3 ^ j)) := by
    have := (ZMod.isUnit_iff_coprime 2 (3 ^ j)).2 (Nat.Coprime.pow_right _ (by norm_num))
    simpa using this
  have hphi : (2 : ZMod (3 ^ j)) ^ (Nat.totient (3 ^ j)) = 1 := by
    have h' := congrArg Units.val (ZMod.pow_totient hu2.unit)
    rw [Units.val_pow_eq_pow_val, Units.val_one, IsUnit.unit_spec] at h'
    exact h'
  have hphi' : η (2 : ZMod (3 ^ j)) ^ (Nat.totient (3 ^ j)) = 1 := by
    rw [← map_pow, hphi, map_one]
  rw [Nat.totient_prime_pow Nat.prime_three (by omega), show (3 - 1 : ℕ) = 2 by norm_num, mul_comm, pow_mul, h2] at hphi'
  have hodd : _root_.Odd (3 ^ (j - 1)) := Odd.pow (by decide)
  rw [hodd.neg_one_pow] at hphi'
  norm_num at hphi'

theorem topA_eqn (j : ℕ) (hj : 1 ≤ j) (aP aQ aS : ℕ) (eP eQ eS : ℂ)
    (hPo : aP % 2 = 1) (hQo : aQ % 2 = 1) (hP3 : ¬ 3 ∣ aP) (hQ3 : ¬ 3 ∣ aQ) (hS3 : 3 ∣ aS) (hS5 : ¬ 5 ∣ aS)
    (H : H1 1 j aP aQ aS eP eQ eS) (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η : DirichletCharacter ℂ (3 ^ j)) (hη : η.IsPrimitive) (hodd : ψ (-1) * η (-1) = -1) :
    ((if 5 ∣ aP then 0 else eP * ψ (aP : ZMod (5 ^ 1))) * η (aP : ZMod (3 ^ j)) +
      (if 5 ∣ aQ then 0 else eQ * ψ (aQ : ZMod (5 ^ 1))) * η (aQ : ZMod (3 ^ j))) *
      (1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hb := H ψ hψ η hodd
  rw [Erdos634.GA2PJ.bracket_i1_three 1 j hj ψ hψ η hη aS hS5 hS3, mul_zero, add_zero] at hb
  have hBP : eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aP =
      (if 5 ∣ aP then 0 else eP * ψ (aP : ZMod (5 ^ 1))) * η (aP : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹) := by
    by_cases h5 : 5 ∣ aP
    · rw [if_pos h5, Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 1 j) hψ _ aP h5]
      ring
    · rw [if_neg h5, Erdos634.GA2PJ.bracket_i1_odd 1 j hj ψ hψ η hη aP h5 (unit_cop1 j aP hPo hP3)]
      ring
  have hBQ : eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 1)) η)) aQ =
      (if 5 ∣ aQ then 0 else eQ * ψ (aQ : ZMod (5 ^ 1))) * η (aQ : ZMod (3 ^ j)) *
        (1 - (ψ (2 : ZMod (5 ^ 1)))⁻¹ * (η (2 : ZMod (3 ^ j)))⁻¹) := by
    by_cases h5 : 5 ∣ aQ
    · rw [if_pos h5, Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 1 j) hψ _ aQ h5]
      ring
    · rw [if_neg h5, Erdos634.GA2PJ.bracket_i1_odd 1 j hj ψ hψ η hη aQ h5 (unit_cop1 j aQ hQo hQ3)]
      ring
  rw [hBP, hBQ] at hb
  linear_combination hb

theorem two_tok (j : ℕ) (hj : 2 ≤ j) (aP aQ : ℕ) (cP cQ : ℂ)
    (hP : IsUnit (aP : ZMod (3 ^ j))) (hQ : IsUnit (aQ : ZMod (3 ^ j)))
    (horth : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive → η (-1) = 1 →
      cP * η (aP : ZMod (3 ^ j)) + cQ * η (aQ : ZMod (3 ^ j)) = 0) :
    (cP = 0 ∧ cQ = 0) ∨
      (((aQ : ZMod (3 ^ j)) = (aP : ZMod (3 ^ j)) ∨ (aQ : ZMod (3 ^ j)) = -(aP : ZMod (3 ^ j))) ∧ cP + cQ = 0) := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set a : Fin 2 → ℕ := ![aP, aQ] with ha
  set c : Fin 2 → ℂ := ![cP, cQ] with hc
  have hu : ∀ t ∈ (Finset.univ : Finset (Fin 2)), IsUnit (a t : ZMod (3 ^ j)) := by
    intro t _
    fin_cases t
    · exact hP
    · exact hQ
  have hpt := Erdos634.GA2PC.pointwise_small j hj a c Finset.univ (by simp) hu (ε := 1) (Or.inl rfl)
    (by
      intro η hη he
      rw [Fin.sum_univ_two]
      exact horth η hη he)
  set p0 : (ZMod (3 ^ j))ˣ := hP.unit with hp0
  set p1 : (ZMod (3 ^ j))ˣ := hQ.unit with hp1
  have hp0c : (p0 : ZMod (3 ^ j)) = (aP : ZMod (3 ^ j)) := IsUnit.unit_spec _
  have hp1c : (p1 : ZMod (3 ^ j)) = (aQ : ZMod (3 ^ j)) := IsUnit.unit_spec _
  have hΦ : ∀ v : (ZMod (3 ^ j))ˣ, PhiV (3 ^ j) a c Finset.univ v =
      (if v = p0 then cP else 0) + (if v = p1 then cQ else 0) := by
    intro v
    show (∑ t : Fin 2, if (v : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) then c t else 0) = _
    rw [Fin.sum_univ_two]
    have e0 : (a 0 : ZMod (3 ^ j)) = (p0 : ZMod (3 ^ j)) := hp0c.symm
    have e1 : (a 1 : ZMod (3 ^ j)) = (p1 : ZMod (3 ^ j)) := hp1c.symm
    rw [e0, e1]
    simp only [Units.val_inj]
    rfl
  have hnn0 : -p0 ≠ p0 := Erdos634.GA2UB.neg_ne_self3 j (by omega) p0
  have hnn1 : -p1 ≠ p1 := Erdos634.GA2UB.neg_ne_self3 j (by omega) p1
  by_cases hq1 : p1 = p0
  · right
    refine ⟨Or.inl (by rw [← hp0c, ← hp1c, hq1]), ?_⟩
    have := hpt p0
    rw [hΦ, hΦ, if_pos rfl, if_pos hq1.symm, if_neg hnn0, if_neg (by rw [hq1]; exact hnn0)] at this
    linear_combination this
  · by_cases hq2 : p1 = -p0
    · right
      refine ⟨Or.inr (by rw [← hp0c, ← hp1c, hq2]; simp), ?_⟩
      have := hpt p0
      rw [hΦ, hΦ, if_pos rfl, if_neg (fun h => hq1 h.symm), if_neg hnn0, if_pos hq2.symm] at this
      linear_combination this
    · left
      have h0 := hpt p0
      rw [hΦ, hΦ, if_pos rfl, if_neg (Ne.symm hq1), if_neg hnn0, if_neg (fun h => hq2 h.symm)] at h0
      have h1 := hpt p1
      rw [hΦ, hΦ, if_neg hq1, if_pos rfl, if_neg (fun h => hq2 (by rw [← h]; simp)), if_neg hnn1] at h1
      constructor
      · linear_combination h0
      · linear_combination h1

end Erdos634.GA2UF

#print axioms Erdos634.GA2UF.F_ne_odd
#print axioms Erdos634.GA2UF.topA_eqn
#print axioms Erdos634.GA2UF.two_tok
