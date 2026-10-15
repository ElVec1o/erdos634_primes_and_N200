/-
GA2P, infrastructure for Theorems B, C (GA2Y_NOTES Section 5): the 3-adic TOP system and the 5-adic orthogonality.

  `fourier_zero`      : Psi on (Z/N)^x with sum_u eta(u) Psi(u) = 0 for ALL Dirichlet characters eta mod N is 0.
  `sum_PhiV`          : for entries a_t (units mod N) and weights c_t:  sum_u eta(u) Phi(u) = sum_t c_t eta(a_t),
                        Phi(u) = sum_{t in V} [u = a_t] c_t.
  `pointwise_small`   : (Lemma N at p = 3, |V| <= 2) orthogonality to the PRIMITIVE characters of parity eps mod 3^j (j >= 2)
                        gives Phi(v) + eps Phi(-v) = 0 for all v.
  `pointwise_all`     : the same conclusion from orthogonality to ALL characters of parity eps (|V| arbitrary).
  `pointwise_form`    : the entry-wise form  sum_{t' in V} c_t' ([a_t' = a_t] + eps [a_t' = -a_t]) = 0  (t in V).
  `five_vanish`       : (mod 5, <= 3 points < 4 = |(Z/5)^x|) sum_{t in V} x_t psi(pi_t) = 0 for all primitive psi mod 5
                        => for t in V the sum of x_t' over pi_t' = pi_t is 0.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PB
import Erdos634.Draft.LemmaSC

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PC

open DirichletCharacter

theorem fourier_zero {N : ℕ} [NeZero N] (Ψ : (ZMod N)ˣ → ℂ)
    (h : ∀ η : DirichletCharacter ℂ N, ∑ u : (ZMod N)ˣ, η (u : ZMod N) * Ψ u = 0) :
    ∀ v, Ψ v = 0 := by
  intro v
  have h1 : ∑ η : DirichletCharacter ℂ N, η ((v : ZMod N)⁻¹) * (∑ u : (ZMod N)ˣ, η (u : ZMod N) * Ψ u) = 0 := by
    simp [h]
  have h2 : ∑ η : DirichletCharacter ℂ N, η ((v : ZMod N)⁻¹) * (∑ u : (ZMod N)ˣ, η (u : ZMod N) * Ψ u)
      = (N.totient : ℂ) * Ψ v := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have key : ∀ u : (ZMod N)ˣ, ∑ η : DirichletCharacter ℂ N,
        η ((v : ZMod N)⁻¹) * (η (u : ZMod N) * Ψ u)
        = (if (v : ZMod N) = u then (N.totient : ℂ) else 0) * Ψ u := by
      intro u
      have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit (u : ZMod N)
      calc _ = (∑ η : DirichletCharacter ℂ N, η ((v : ZMod N)⁻¹) * η (u : ZMod N)) * Ψ u := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun η _ => ?_); ring
        _ = _ := by rw [this]
    simp_rw [key]
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      rw [if_neg, zero_mul]
      intro hh
      exact hu (Units.ext hh.symm)
    · simp
  rw [h2] at h1
  have hφ : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  exact (mul_eq_zero.1 h1).resolve_left hφ

/-- The function Phi(u) = sum_{t in V} [u = a_t] c_t on units. -/
noncomputable def PhiV {ι : Type*} (N : ℕ) (a : ι → ℕ) (c : ι → ℂ) (V : Finset ι) (u : (ZMod N)ˣ) : ℂ :=
  ∑ t ∈ V, if (u : ZMod N) = (a t : ZMod N) then c t else 0

theorem sum_PhiV {ι : Type*} (N : ℕ) [NeZero N] (a : ι → ℕ) (c : ι → ℂ) (V : Finset ι)
    (hu : ∀ t ∈ V, IsUnit (a t : ZMod N)) (η : DirichletCharacter ℂ N) :
    ∑ u : (ZMod N)ˣ, η (u : ZMod N) * PhiV N a c V u = ∑ t ∈ V, c t * η (a t : ZMod N) := by
  unfold PhiV
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  obtain ⟨u0, hu0⟩ := hu t ht
  rw [Finset.sum_eq_single u0]
  · rw [if_pos hu0, hu0]; ring
  · intro u _ hne
    rw [if_neg, mul_zero]
    intro hh
    apply hne
    apply Units.ext
    rw [hh, hu0]
  · simp


theorem pointwise_small (j : ℕ) (hj : 2 ≤ j) {ι : Type*} (a : ι → ℕ) (c : ι → ℂ) (V : Finset ι)
    (hV : V.card ≤ 2) (hu : ∀ t ∈ V, IsUnit (a t : ZMod (3 ^ j))) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (horth : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive → η (-1) = ε →
      ∑ t ∈ V, c t * η (a t : ZMod (3 ^ j)) = 0) :
    ∀ v, PhiV (3 ^ j) a c V v + ε * PhiV (3 ^ j) a c V (-v) = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set P : Finset (ZMod (3 ^ j))ˣ := (V.attach ×ˢ (univ : Finset Bool)).image
    (fun p => if p.2 then (hu p.1.1 p.1.2).unit else -(hu p.1.1 p.1.2).unit) with hP
  have hPc : P.card < 6 := by
    have h1 : P.card ≤ (V.attach ×ˢ (univ : Finset Bool)).card := Finset.card_image_le
    rw [Finset.card_product, Finset.card_attach, Finset.card_univ, Fintype.card_bool] at h1
    omega
  have hmem : ∀ v : (ZMod (3 ^ j))ˣ, (PhiV (3 ^ j) a c V v ≠ 0 ∨ PhiV (3 ^ j) a c V (-v) ≠ 0) → v ∈ P := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hcond : (v : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) := by
        by_contra hh; rw [if_neg hh] at hne; exact hne rfl
      refine Finset.mem_image.2 ⟨(⟨t, ht⟩, true), by simp, ?_⟩
      simp only [if_true]
      apply Units.ext
      rw [IsUnit.unit_spec]
      exact hcond.symm
    · obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hcond : ((-v : (ZMod (3 ^ j))ˣ) : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) := by
        by_contra hh; rw [if_neg hh] at hne; exact hne rfl
      refine Finset.mem_image.2 ⟨(⟨t, ht⟩, false), by simp, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      apply Units.ext
      rw [Units.val_neg, IsUnit.unit_spec]
      rw [Units.val_neg] at hcond
      rw [← hcond]; ring
  have h := Erdos634.GA2PB.top3_zero_small j hj (PhiV (3 ^ j) a c V) hε
    (fun ψ hψ hψ1 => by rw [sum_PhiV (3 ^ j) a c V hu ψ]; exact horth ψ hψ hψ1) P hmem hPc
  intro v
  have := h v
  linear_combination this

theorem pointwise_all (j : ℕ) {ι : Type*} (a : ι → ℕ) (c : ι → ℂ) (V : Finset ι)
    (hu : ∀ t ∈ V, IsUnit (a t : ZMod (3 ^ j))) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (horth : ∀ η : DirichletCharacter ℂ (3 ^ j), η (-1) = ε →
      ∑ t ∈ V, c t * η (a t : ZMod (3 ^ j)) = 0) :
    ∀ v, PhiV (3 ^ j) a c V v + ε * PhiV (3 ^ j) a c V (-v) = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set Φ := PhiV (3 ^ j) a c V with hΦ
  refine fourier_zero (fun u => Φ u + ε * Φ (-u)) ?_
  intro η
  have hneg : ∑ u : (ZMod (3 ^ j))ˣ, η (u : ZMod (3 ^ j)) * Φ (-u) =
      η (-1) * ∑ u : (ZMod (3 ^ j))ˣ, η (u : ZMod (3 ^ j)) * Φ u := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun u => ?_)
    simp only [Equiv.neg_apply, Units.val_neg]
    have : η (u : ZMod (3 ^ j)) = η (-1) * η (-(u : ZMod (3 ^ j))) := by
      rw [← map_mul]; congr 1; ring
    rw [this]
    ring
  have hsum : ∑ u : (ZMod (3 ^ j))ˣ, η (u : ZMod (3 ^ j)) * (Φ u + ε * Φ (-u)) =
      (1 + ε * η (-1)) * ∑ u : (ZMod (3 ^ j))ˣ, η (u : ZMod (3 ^ j)) * Φ u := by
    have : ∀ u : (ZMod (3 ^ j))ˣ, η (u : ZMod (3 ^ j)) * (Φ u + ε * Φ (-u)) =
        η (u : ZMod (3 ^ j)) * Φ u + ε * (η (u : ZMod (3 ^ j)) * Φ (-u)) := fun u => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hneg]
    ring
  show ∑ u : (ZMod (3 ^ j))ˣ, η (u : ZMod (3 ^ j)) * (Φ u + ε * Φ (-u)) = 0
  rw [hsum]
  rcases DirichletCharacter.even_or_odd η with h1 | h1
  · rcases hε with rfl | rfl
    · rw [sum_PhiV (3 ^ j) a c V hu η, horth η h1, mul_zero]
    · rw [h1]; norm_num
  · rcases hε with rfl | rfl
    · rw [h1]; norm_num
    · rw [sum_PhiV (3 ^ j) a c V hu η, horth η h1, mul_zero]

/-- Entry-wise form of the pointwise relation. -/
theorem pointwise_form (N : ℕ) [NeZero N] {ι : Type*} (a : ι → ℕ) (c : ι → ℂ) (V : Finset ι)
    (hu : ∀ t ∈ V, IsUnit (a t : ZMod N)) (ε : ℂ)
    (hpt : ∀ v, PhiV N a c V v + ε * PhiV N a c V (-v) = 0) (t : ι) (ht : t ∈ V) :
    ∑ t' ∈ V, c t' * ((if (a t' : ZMod N) = (a t : ZMod N) then 1 else 0) +
      ε * (if (a t' : ZMod N) = -(a t : ZMod N) then 1 else 0)) = 0 := by
  obtain ⟨u0, hu0⟩ := hu t ht
  have h := hpt u0
  unfold PhiV at h
  rw [Finset.mul_sum, ← Finset.sum_add_distrib] at h
  refine Eq.trans (Finset.sum_congr rfl (fun t' _ => ?_)) h
  rw [Units.val_neg, hu0]
  by_cases h1 : (a t' : ZMod N) = (a t : ZMod N)
  · by_cases h2 : (a t' : ZMod N) = -(a t : ZMod N)
    · rw [if_pos h1, if_pos h2, if_pos h1.symm, if_pos h2.symm]; ring
    · rw [if_pos h1, if_neg h2, if_pos h1.symm, if_neg (fun h => h2 h.symm)]; ring
  · by_cases h2 : (a t' : ZMod N) = -(a t : ZMod N)
    · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.symm), if_pos h2.symm]; ring
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.symm), if_neg (fun h => h2 h.symm)]; ring


theorem five_free (x0 x1 x2 : ZMod (5 ^ 1)) :
    ∃ u : (ZMod (5 ^ 1))ˣ, (u : ZMod (5 ^ 1)) ≠ x0 ∧ (u : ZMod (5 ^ 1)) ≠ x1 ∧ (u : ZMod (5 ^ 1)) ≠ x2 := by
  revert x0 x1 x2
  decide

theorem five_prim_of_ne_one (η : DirichletCharacter ℂ (5 ^ 1)) (h : η ≠ 1) : η.IsPrimitive := by
  have hne : η.conductor ≠ 1 := fun hc => h ((eq_one_iff_conductor_eq_one).2 hc)
  have hd : η.conductor ∣ 5 := Nat.dvd_trans (conductor_dvd_level η) (by norm_num)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hd with h1 | h1
  · exact absurd h1 hne
  · show η.conductor = 5 ^ 1
    rw [h1]; norm_num

theorem five_vanish (V : Finset (Fin 3)) (π : Fin 3 → ZMod (5 ^ 1)) (hπ : ∀ t ∈ V, IsUnit (π t))
    (x : Fin 3 → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ∑ t ∈ V, x t * ψ (π t) = 0) :
    ∀ t ∈ V, ∑ t' ∈ V, (if π t' = π t then x t' else 0) = 0 := by
  have hu : ∀ t ∈ V, IsUnit (((π t).val : ℕ) : ZMod (5 ^ 1)) := by
    intro t ht; rw [ZMod.natCast_zmod_val]; exact hπ t ht
  set a : Fin 3 → ℕ := fun t => (π t).val with ha
  have hcast : ∀ t, ((a t : ℕ) : ZMod (5 ^ 1)) = π t := fun t => ZMod.natCast_zmod_val (π t)
  set m := PhiV (5 ^ 1) a x V with hm
  have hS : ∀ η : DirichletCharacter ℂ (5 ^ 1),
      ∑ u : (ZMod (5 ^ 1))ˣ, η (u : ZMod (5 ^ 1)) * m u = ∑ t ∈ V, x t * η (π t) := by
    intro η
    rw [hm, sum_PhiV (5 ^ 1) a x V hu η]
    exact Finset.sum_congr rfl (fun t _ => by rw [hcast])
  set K : ℂ := ∑ t ∈ V, x t with hK
  have hK1 : ∑ u : (ZMod (5 ^ 1))ˣ, m u = K := by
    have := hS 1
    simp only [MulChar.one_apply (Units.isUnit _), one_mul] at this
    rw [this]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [MulChar.one_apply (hπ t ht), mul_one]
  have hcard : ((Finset.univ : Finset (ZMod (5 ^ 1))ˣ).card : ℂ) = 4 := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient]
    norm_num [Nat.totient_prime (by norm_num : Nat.Prime 5)]
  have hz : ∀ v, m v - K / 4 = 0 := by
    refine fourier_zero (fun u => m u - K / 4) ?_
    intro η
    by_cases hη : η = 1
    · subst hη
      simp only [MulChar.one_apply (Units.isUnit _), one_mul, Finset.sum_sub_distrib, hK1,
        Finset.sum_const, nsmul_eq_mul, hcard]
      ring
    · have hprim := five_prim_of_ne_one η hη
      have h0 := h η hprim
      have hs0 : ∑ u : (ZMod (5 ^ 1))ˣ, η (u : ZMod (5 ^ 1)) = 0 := by
        have := Erdos634.LemmaSC.sum_units_eq_sum η (fun _ => (1 : ℂ))
        simp only [mul_one] at this
        rw [this]
        exact MulChar.sum_eq_zero_of_ne_one hη
      simp only [mul_sub, Finset.sum_sub_distrib, hS η, h0, ← Finset.sum_mul, hs0]
      ring
  obtain ⟨u0, hy⟩ := five_free (π 0) (π 1) (π 2)
  have hm0 : m u0 = 0 := by
    rw [hm]
    unfold PhiV
    refine Finset.sum_eq_zero (fun t _ => ?_)
    rw [if_neg, ]
    rw [hcast]
    fin_cases t
    · exact hy.1
    · exact hy.2.1
    · exact hy.2.2
  have hK0 : K / 4 = 0 := by have := hz u0; rw [hm0] at this; linear_combination -this
  have hmz : ∀ v, m v = 0 := fun v => by have := hz v; rw [hK0] at this; linear_combination this
  intro t ht
  obtain ⟨u1, hu1⟩ := hπ t ht
  have := hmz u1
  rw [hm] at this
  unfold PhiV at this
  refine Eq.trans (Finset.sum_congr rfl (fun t' _ => ?_)) this
  rw [hcast, hu1]
  by_cases hh : π t' = π t
  · rw [if_pos hh, if_pos hh.symm]
  · rw [if_neg hh, if_neg (fun h' => hh h'.symm)]

end Erdos634.GA2PC
