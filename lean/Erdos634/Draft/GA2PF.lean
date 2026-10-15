/-
GA2P, Theorem B (i = 2, r = 1, j >= 2), part 2: the TOP step with eta2 = chi_4 and eta3 primitive mod 3^j.
  `HB`          : the hypothesis (all odd characters psi (eta2 x eta3), psi primitive mod 5, eta2 mod 4, eta3 mod 3^j).
  `visB`        : visible entries (prime to 5 and to 6).
  `eqprimB`     : the top equation  sum_{t in visB} e_t psi(a_t) chi4(a_t) eta3(a_t) = 0.
  `B_top`       : (<= 2 visible entries)  for every visible t,
                  sum_{t' visible} [a_t' = a_t mod n/4  or  n/4 | a_t + a_t'] e_t' chi4(a_t') = 0.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PD
import Erdos634.Draft.GA2PE

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PF

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE

def HB (j : ℕ) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
    ∀ η2 : DirichletCharacter ℂ (2 ^ 2), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η2 (-1) * η3 (-1) = -1 →
      ∑ t, e t * bracket (chi ψ (chi η2 η3)) (a t) = 0

def visB (j : ℕ) (a : Fin 3 → ℕ) : Finset (Fin 3) :=
  univ.filter (fun t => ¬ 5 ∣ a t ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) (a t))

theorem eqprimB (j : ℕ) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (H : HB j a e)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4 : χ4.IsPrimitive) (hχ4o : χ4 (-1) = -1)
    (ψ : DirichletCharacter ℂ (5 ^ 1)) (hψ : ψ.IsPrimitive)
    (η3 : DirichletCharacter ℂ (3 ^ j)) (hη3 : η3.IsPrimitive) (h1 : η3 (-1) = ψ (-1)) :
    ∑ t ∈ visB j a, e t * (ψ (a t : ZMod (5 ^ 1)) * (χ4 (a t : ZMod (2 ^ 2)) * η3 (a t : ZMod (3 ^ j)))) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hodd : ψ (-1) * χ4 (-1) * η3 (-1) = -1 := by
    rw [hχ4o, h1]
    rcases DirichletCharacter.even_or_odd ψ with h | h <;> rw [h] <;> norm_num
  have h := H ψ hψ χ4 η3 hodd
  refine Eq.trans ?_ h
  unfold visB
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h5 : 5 ∣ a t
  · rw [bracket_p_dvd (p := 5) (r := 1) le_rfl (not5_dvd' 2 j) hψ _ (a t) h5]; simp [h5]
  · rw [bracket_top_prim 1 2 j ψ hψ χ4 hχ4 η3 hη3 (a t) h5]
    by_cases hc : Nat.Coprime (2 ^ 2 * 3 ^ j) (a t)
    · rw [if_pos hc, if_pos ⟨h5, hc⟩]
    · rw [if_neg hc, if_neg (fun h' => hc h'.2)]; ring

theorem B_top (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (e : Fin 3 → ℂ) (H : HB j a e)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4 : χ4.IsPrimitive) (hχ4o : χ4 (-1) = -1)
    (hcard : (visB j a).card ≤ 2) :
    ∀ t ∈ visB j a, ∑ t' ∈ visB j a,
      (if (a t' ≡ a t [MOD 5 * 3 ^ j] ∨ 5 * 3 ^ j ∣ a t + a t') then
        e t' * χ4 (a t' : ZMod (2 ^ 2)) else 0) = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  intro t ht
  have hvis : ∀ t' ∈ visB j a, ¬ 5 ∣ a t' ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) (a t') :=
    fun t' h => (Finset.mem_filter.1 h).2
  have hcop3 : ∀ t' ∈ visB j a, Nat.Coprime 3 (a t') := by
    intro t' ht'
    have := (hvis t' ht').2
    rw [Nat.coprime_mul_iff_left] at this
    exact (Nat.coprime_pow_left_iff (by omega) 3 _).1 this.2
  have hu : ∀ t' ∈ visB j a, IsUnit (a t' : ZMod (3 ^ j)) := by
    intro t' ht'
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (hcop3 t' ht').symm
  have hε : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ (-1) = 1 ∨ ψ (-1) = -1 :=
    fun ψ => DirichletCharacter.even_or_odd ψ
  set πf : Fin 3 → ZMod (5 ^ 1) := fun t' =>
    if (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) then (a t' : ZMod (5 ^ 1)) else -(a t' : ZMod (5 ^ 1)) with hπf
  set xf : Fin 3 → ℂ := fun t' =>
    if ((a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) ∨ (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))) then
      e t' * χ4 (a t' : ZMod (2 ^ 2)) else 0 with hxf
  have hunit5 : ∀ t' ∈ visB j a, IsUnit (a t' : ZMod (5 ^ 1)) := by
    intro t' ht'
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (hvis t' ht').1).symm
  have hπ : ∀ t' ∈ visB j a, IsUnit (πf t') := by
    intro t' ht'
    simp only [hπf]
    split_ifs
    · exact hunit5 t' ht'
    · exact (hunit5 t' ht').neg
  have hh : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
      ∑ t' ∈ visB j a, xf t' * ψ (πf t') = 0 := by
    intro ψ hψ
    set c : Fin 3 → ℂ := fun t' => e t' * (ψ (a t' : ZMod (5 ^ 1)) * χ4 (a t' : ZMod (2 ^ 2))) with hc
    have hpt : ∀ v, PhiV (3 ^ j) a c (visB j a) v + (ψ (-1)) * PhiV (3 ^ j) a c (visB j a) (-v) = 0 := by
      refine pointwise_small j hj a c (visB j a) hcard hu (hε ψ) ?_
      intro η hη hη1
      have := eqprimB j a e H χ4 hχ4 hχ4o ψ hψ η hη hη1
      rw [← this]
      exact Finset.sum_congr rfl (fun t' _ => by simp only [hc]; ring)
    have hr := pointwise_form (3 ^ j) a c (visB j a) hu (ψ (-1)) hpt t ht
    refine Eq.trans ?_ hr
    refine Finset.sum_congr rfl (fun t' ht' => ?_)
    have hex : ¬ ((a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) ∧ (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))) := by
      rintro ⟨h1, h2⟩
      exact not_self_neg j (by omega) (a t) (hcop3 t ht) (h1.symm.trans h2)
    by_cases p3 : (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j))
    · have hm3 : ¬ (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j)) := fun h => hex ⟨p3, h⟩
      simp only [hxf, hπf, if_pos p3, if_pos (Or.inl p3), if_neg hm3, hc]
      ring
    · by_cases m3 : (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))
      · simp only [hxf, hπf, if_neg p3, if_pos (Or.inr m3), if_pos m3, hc]
        have : -(a t' : ZMod (5 ^ 1)) = (-1) * (a t' : ZMod (5 ^ 1)) := by ring
        rw [this, map_mul]
        ring
      · simp only [hxf, hπf, if_neg p3, if_neg m3, hc]
        rw [if_neg (by tauto)]
        ring
  have hfv := five_vanish (visB j a) πf hπ xf hh t ht
  refine Eq.trans (Finset.sum_congr rfl (fun t' ht' => ?_)) hfv
  have hπt : πf t = (a t : ZMod (5 ^ 1)) := by simp [hπf]
  have hex : ¬ ((a t : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))) := not_self_neg j (by omega) (a t) (hcop3 t ht)
  by_cases p3 : (a t' : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j))
  · have hπt' : πf t' = (a t' : ZMod (5 ^ 1)) := by simp [hπf, p3]
    have hxt' : xf t' = e t' * χ4 (a t' : ZMod (2 ^ 2)) := by simp [hxf, p3]
    rw [hπt', hπt, hxt']
    have hnot2 : ¬ 5 * 3 ^ j ∣ a t + a t' := by
      intro h
      have h3 : 3 ^ j ∣ a t + a t' := (Dvd.intro_left 5 rfl).trans h
      have := (natcast_neg_iff (3 ^ j) (a t) (a t')).2 h3
      rw [p3] at this
      exact hex this
    have hiff : (a t' ≡ a t [MOD 5 * 3 ^ j] ∨ 5 * 3 ^ j ∣ a t + a t') ↔
        (a t' : ZMod (5 ^ 1)) = (a t : ZMod (5 ^ 1)) := by
      rw [or_iff_left hnot2]
      constructor
      · intro h
        have h5 : a t' ≡ a t [MOD 5] := Nat.ModEq.of_mul_right (3 ^ j) h
        exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (by simpa using h5)
      · intro h5
        exact modEq_m0 j _ _ ((ZMod.natCast_eq_natCast_iff _ _ _).1 p3)
          (by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).1 h5)
    rw [if_congr hiff rfl rfl]
  · have hπt' : πf t' = -(a t' : ZMod (5 ^ 1)) := by simp [hπf, p3]
    have hnot1 : ¬ a t' ≡ a t [MOD 5 * 3 ^ j] := by
      intro h
      have h3 : a t' ≡ a t [MOD 3 ^ j] := Nat.ModEq.of_mul_left 5 h
      exact p3 ((ZMod.natCast_eq_natCast_iff _ _ _).2 h3)
    by_cases m3 : (a t' : ZMod (3 ^ j)) = -(a t : ZMod (3 ^ j))
    · have hxt' : xf t' = e t' * χ4 (a t' : ZMod (2 ^ 2)) := by
        simp [hxf, m3]
      rw [hπt', hπt, hxt']
      have h3 : 3 ^ j ∣ a t' + a t := (natcast_neg_iff _ _ _).1 m3
      have hiff : (a t' ≡ a t [MOD 5 * 3 ^ j] ∨ 5 * 3 ^ j ∣ a t + a t') ↔
          -(a t' : ZMod (5 ^ 1)) = (a t : ZMod (5 ^ 1)) := by
        rw [or_iff_right hnot1]
        constructor
        · intro h
          have h5 : 5 ∣ a t + a t' := (Dvd.intro _ rfl).trans h
          have := (natcast_neg_iff (5 ^ 1) (a t) (a t')).2 (by simpa using h5)
          rw [this]
        · intro h5
          have h5' : (a t : ZMod (5 ^ 1)) = -(a t' : ZMod (5 ^ 1)) := h5.symm
          have h5'' := (natcast_neg_iff (5 ^ 1) (a t) (a t')).1 h5'
          exact dvd_m0 j _ (by rwa [add_comm]) (by simpa using h5'')
      rw [if_congr hiff rfl rfl]
    · have hxt' : xf t' = 0 := by simp [hxf, p3, m3]
      rw [hxt']
      have hnot : ¬ (a t' ≡ a t [MOD 5 * 3 ^ j] ∨ 5 * 3 ^ j ∣ a t + a t') := by
        rintro (h | h)
        · exact hnot1 h
        · apply m3
          have h3 : 3 ^ j ∣ a t' + a t := by
            rw [add_comm]; exact (Dvd.intro_left 5 rfl).trans h
          exact (natcast_neg_iff _ _ _).2 h3
      rw [if_neg hnot]
      simp


/-- The labelled hypothesis for a triple (X, Y, S) = (odd, odd, even) with all odd characters. -/
def H3B (j : ℕ) (aX aY aS : ℕ) (eX eY eS : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
    ∀ η2 : DirichletCharacter ℂ (2 ^ 2), ∀ η3 : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η2 (-1) * η3 (-1) = -1 →
      eX * bracket (chi ψ (chi η2 η3)) aX + eY * bracket (chi ψ (chi η2 η3)) aY +
        eS * bracket (chi ψ (chi η2 η3)) aS = 0

theorem H3B_swap {j : ℕ} {aX aY aS : ℕ} {eX eY eS : ℂ} (H : H3B j aX aY aS eX eY eS) :
    H3B j aY aX aS eY eX eS := by
  intro ψ hψ η2 η3 hodd
  have := H ψ hψ η2 η3 hodd
  linear_combination this

theorem HB_of_H3B {j : ℕ} {aX aY aS : ℕ} {eX eY eS : ℂ} (H : H3B j aX aY aS eX eY eS) :
    HB j ![aX, aY, aS] ![eX, eY, eS] := by
  intro ψ hψ η2 η3 hodd
  have := H ψ hψ η2 η3 hodd
  simpa [Fin.sum_univ_three] using this

theorem not_cop_even (j : ℕ) (a : ℕ) (h : a % 2 = 0) : ¬ Nat.Coprime (2 ^ 2 * 3 ^ j) a := by
  intro hc
  have h2 : 2 ∣ Nat.gcd (2 ^ 2 * 3 ^ j) a :=
    Nat.dvd_gcd (Dvd.dvd.mul_right (by norm_num) _) (by omega)
  rw [hc] at h2
  omega

theorem chi4_ne_zero (χ : DirichletCharacter ℂ (2 ^ 2)) (hχ : χ (-1) = -1) (a : ℕ) (ha : a % 2 = 1) :
    χ (a : ZMod (2 ^ 2)) ≠ 0 := by
  rw [chi4_val χ hχ a ha]
  split_ifs <;> norm_num

theorem B_eq1 (j : ℕ) (hj : 2 ≤ j) (aX aY aS : ℕ) (eX eY eS : ℂ) (hSe : aS % 2 = 0)
    (H : H3B j aX aY aS eX eY eS)
    (χ4 : DirichletCharacter ℂ (2 ^ 2)) (hχ4 : χ4.IsPrimitive) (hχ4o : χ4 (-1) = -1)
    (hvX : ¬ 5 ∣ aX ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aX) :
    eX * χ4 (aX : ZMod (2 ^ 2)) +
      (if ((¬ 5 ∣ aY ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aY) ∧
          (aY ≡ aX [MOD 5 * 3 ^ j] ∨ 5 * 3 ^ j ∣ aX + aY)) then eY * χ4 (aY : ZMod (2 ^ 2)) else 0) = 0 := by
  have hHB := HB_of_H3B H
  have hcard : (visB j ![aX, aY, aS]).card ≤ 2 := by
    have hsub : visB j ![aX, aY, aS] ⊆ {0, 1} := by
      intro t ht
      have := (Finset.mem_filter.1 ht).2.2
      fin_cases t
      · simp
      · simp
      · exfalso; exact not_cop_even j aS hSe (by simpa using this)
    exact (Finset.card_le_card hsub).trans (by decide)
  have ht0 : (0 : Fin 3) ∈ visB j ![aX, aY, aS] :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hvX.1, hvX.2⟩
  have h := B_top j hj ![aX, aY, aS] ![eX, eY, eS] hHB χ4 hχ4 hχ4o hcard 0 ht0
  unfold visB at h
  rw [Finset.sum_filter] at h
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  have h2' : ¬ (¬ 5 ∣ aS ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aS) := fun hh => not_cop_even j aS hSe hh.2
  rw [if_pos hvX, if_neg h2', add_zero] at h
  rw [if_pos (Or.inl (Nat.ModEq.refl _))] at h
  by_cases hY : (¬ 5 ∣ aY ∧ Nat.Coprime (2 ^ 2 * 3 ^ j) aY)
  · rw [if_pos hY] at h
    by_cases hm : (aY ≡ aX [MOD 5 * 3 ^ j] ∨ 5 * 3 ^ j ∣ aX + aY)
    · rw [if_pos hm] at h
      rw [if_pos ⟨hY, hm⟩]
      exact h
    · rw [if_neg hm, add_zero] at h
      rw [if_neg (fun hh => hm hh.2), add_zero]
      exact h
  · rw [if_neg hY, add_zero] at h
    rw [if_neg (fun hh => hY hh.1), add_zero]
    exact h

#print axioms Erdos634.GA2PF.B_eq1

end Erdos634.GA2PF
