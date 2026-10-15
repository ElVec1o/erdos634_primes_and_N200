/-
GA2N, item (2b): **group core of the TOP step for general r >= 1 and general j >= 1** (GA2Y_NOTES Lemma A3 Steps 1-3).

`HypR r k j z5 z2 z3 c` (eta3 != 1) and `HypTR r k z5 z2 c` (eta3 = 1, only used when j = 1).
`group_core_gen` : the shared skeleton (Steps 1 and 3), parametrised by the Step-2 conclusion `S2`.
`S2_j2`          : Step 2 for j >= 2 (I3' `const_nontriv`).
`S2_j1`          : Step 2 for j = 1 (Leg vs 1; even psi, odd eta2 with psi(3) eta2(3) != 1, `exists_even_odd`).
`group_core_R`   : r >= 1, j >= 1:  z5 = z3 = (-1)^s, z2 = (-1)^s (1+2^(k+2))^e, c = (-1)^(s+e).
`five_odd_gen`   : r = 1 (`GA2LCore.five_odd`) and r >= 2 (`GA2NG.five_odd_R`, lemma G) in one statement.
Witnesses: `group_core_R_converse`, `admissible_exists_R`, `G_R_witness`.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2NG
import Erdos634.Draft.GA2NJ1

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2NR1

open Erdos634.GA2LPar Erdos634.GA2LCore Erdos634.GA2LGroup Erdos634.GA2NG Erdos634.GA2MF4 Erdos634.GA2NJ1

def HypR (r k j : ℕ) (z5 z2 z3 : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
  ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
    ψ (-1) * η2 (-1) * η3 (-1) = -1 →
    ψ (z5 : ZMod (5 ^ r)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ j)) = c

def HypTR (r k : ℕ) (z5 z2 : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
    ψ (-1) * η2 (-1) = -1 →
    ψ (3 : ZMod (5 ^ r)) * η2 (3 : ZMod (2 ^ (k + 3))) ≠ 1 →
    ψ (z5 : ZMod (5 ^ r)) * η2 (z2 : ZMod (2 ^ (k + 3))) = c

theorem r_cases (r : ℕ) (hr : 1 ≤ r) : (∃ t, r = t + 2) ∨ r = 1 := by
  rcases Nat.lt_or_ge r 2 with h | h
  · right; omega
  · left; exact ⟨r - 2, by omega⟩

theorem five_odd_gen (r : ℕ) (hr : 1 ≤ r) (z : ℤ) (hz : IsUnit ((z : ZMod (5 ^ r)))) (c : ℂ)
    (hc : ∀ ψ ∈ PrimPar 5 r (-1), ψ (z : ZMod (5 ^ r)) = c) :
    (z ≡ 1 [ZMOD 5 ^ r] ∧ c = 1) ∨ (z ≡ -1 [ZMOD 5 ^ r] ∧ c = -1) := by
  obtain ⟨t, rfl⟩ | rfl := r_cases r hr
  · exact five_odd_R t z hz c hc
  · simpa using five_odd z hz c hc

theorem nonempty5 (r : ℕ) (hr : 1 ≤ r) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) : (PrimPar 5 r ε).Nonempty := by
  obtain ⟨t, rfl⟩ | rfl := r_cases r hr
  · exact nonempty_R t ε hε
  · rw [← card_pos, card_five ε hε]; split_ifs <;> norm_num

theorem sgn2 {n m : ℕ} (ψ : DirichletCharacter ℂ n) (η : DirichletCharacter ℂ m) :
    (-(ψ (-1) * η (-1))) = 1 ∨ (-(ψ (-1) * η (-1))) = -1 := by
  rcases sign_val ψ with h | h <;> rcases sign_val η with h' | h' <;> rw [h, h'] <;> norm_num

/-- The shared skeleton of `group_core`; Step 2 is supplied. -/
theorem group_core_gen (r k j : ℕ) (hr : 1 ≤ r) (η30 : DirichletCharacter ℂ (3 ^ j)) (hη30 : η30 ≠ 1)
    (z5 z2 z3 : ℤ) (c : ℂ)
    (u5 : IsUnit (z5 : ZMod (5 ^ r))) (u2 : IsUnit (z2 : ZMod (2 ^ (k + 3))))
    (u3 : IsUnit (z3 : ZMod (3 ^ j))) (H : HypR r k j z5 z2 z3 c)
    (S2 : ∀ s e : ℕ, s < 2 → e < 2 →
      (∀ ε' : ℂ, (ε' = 1 ∨ ε' = -1) → ∀ η ∈ PrimPar 2 (k + 3) ε',
        η (z2 : ZMod (2 ^ (k + 3))) = ε' ^ s * (-1) ^ e) →
      (∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
        ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
        ∀ η2 ∈ PrimPar 2 (k + 3) (-(ψ (-1) * η3 (-1))),
          ψ (z5 : ZMod (5 ^ r)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ j)) = c) →
      (z3 : ZMod (3 ^ j)) * (-1) ^ s = 1) :
    ∃ s e : ℕ, s < 2 ∧ e < 2 ∧ (z5 : ZMod (5 ^ r)) = (-1) ^ s ∧ (z3 : ZMod (3 ^ j)) = (-1) ^ s ∧
      (z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e ∧ c = (-1) ^ (s + e) := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have claim : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
      ∀ η2 ∈ PrimPar 2 (k + 3) (-(ψ (-1) * η3 (-1))),
        ψ (z5 : ZMod (5 ^ r)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ j)) = c := by
    intro ψ hψ η3 hη3 η2 hη2
    obtain ⟨hp2, hs2⟩ := mem_PrimPar.1 hη2
    refine H ψ hψ η2 hp2 η3 hη3 ?_
    rw [hs2]
    rcases sign_val ψ with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num
  obtain ⟨ψe, hψe⟩ := nonempty5 r hr 1 (Or.inl rfl)
  obtain ⟨hψe_p, hψe_s⟩ := mem_PrimPar.1 hψe
  have A0 : ψe (z5 : ZMod (5 ^ r)) ≠ 0 := nz ψe _ u5
  have step1 : ∃ s e : ℕ, s < 2 ∧ e < 2 ∧
      ((z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e) ∧
      ∀ ε' : ℂ, (ε' = 1 ∨ ε' = -1) → ∀ η ∈ PrimPar 2 (k + 3) ε',
        η (z2 : ZMod (2 ^ (k + 3))) = ε' ^ s * (-1) ^ e := by
    refine two_part_core k (-(ψe (-1) * η30 (-1))) (sgn2 ψe η30) z2 u2
      ⟨c / (ψe (z5 : ZMod (5 ^ r)) * η30 (z3 : ZMod (3 ^ j))), fun η hη => ?_⟩
    have h := claim ψe hψe_p η30 hη30 η hη
    have B0 : η30 (z3 : ZMod (3 ^ j)) ≠ 0 := nz η30 _ u3
    rw [eq_div_iff (mul_ne_zero A0 B0)]
    linear_combination h
  obtain ⟨s, e, hs, he, h2eq, hval⟩ := step1
  have step2 := S2 s e hs he hval claim
  have z3eq : (z3 : ZMod (3 ^ j)) = (-1) ^ s := by
    have hs2 : ((-1 : ZMod (3 ^ j)) ^ s) * ((-1) ^ s) = 1 := by
      rw [← mul_pow]; simp
    calc (z3 : ZMod (3 ^ j)) = (z3 * (-1) ^ s) * (-1) ^ s := by
          rw [mul_assoc, hs2, mul_one]
      _ = (-1) ^ s := by rw [step2, one_mul]
  have step3 : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
      ψ (z5 : ZMod (5 ^ r)) * ((-(ψ (-1) * η30 (-1))) ^ s * (-1) ^ e * η30 (-1) ^ s) = c := by
    intro ψ hψ
    obtain ⟨η2, hη2⟩ := nonempty_par2 k (-(ψ (-1) * η30 (-1))) (sgn2 ψ η30)
    have h := claim ψ hψ η30 hη30 η2 hη2
    rw [hval _ (sgn2 ψ η30) η2 hη2, z3eq, map_pow] at h
    linear_combination h
  have sq1 : ∀ x : ℂ, (x = 1 ∨ x = -1) → ∀ n : ℕ, x ^ n * x ^ n = 1 := by
    intro x hx n; rw [← mul_pow]; rcases hx with rfl | rfl <;> simp
  have hX := sq1 (η30 (-1)) (sign_val η30) s
  have hb := sq1 (-1 : ℂ) (Or.inr rfl) e
  have odd5 : ∀ ψ ∈ PrimPar 5 r (-1), ψ (z5 : ZMod (5 ^ r)) = (-1) ^ e * c := by
    intro ψ hψ
    obtain ⟨hp, hs⟩ := mem_PrimPar.1 hψ
    have h := step3 ψ hp
    rw [hs, neg_one_mul, neg_neg] at h
    linear_combination (-1 : ℂ) ^ e * h - ψ (z5 : ZMod (5 ^ r)) * (η30 (-1) ^ s * η30 (-1) ^ s) * hb
      - ψ (z5 : ZMod (5 ^ r)) * hX
  have five := five_odd_gen r hr z5 u5 ((-1) ^ e * c) odd5
  have zm5 : ∀ {w : ℤ}, z5 ≡ w [ZMOD 5 ^ r] → (z5 : ZMod (5 ^ r)) = (w : ZMod (5 ^ r)) := by
    intro w h
    rw [ZMod.intCast_eq_intCast_iff]; push_cast; exact h
  have hcc : c = (-1) ^ (s + e) := by
    have hz5 : (z5 : ZMod (5 ^ r)) = 1 ∨ (z5 : ZMod (5 ^ r)) = -1 := by
      rcases five with ⟨h, _⟩ | ⟨h, _⟩
      · left; simpa using zm5 h
      · right; simpa using zm5 h
    have hψ1 : ψe (z5 : ZMod (5 ^ r)) = 1 := by
      rcases hz5 with h | h <;> rw [h]
      · exact map_one ψe
      · exact hψe_s
    have h := step3 ψe hψe_p
    rw [hψ1, hψe_s, one_mul, one_mul, neg_pow] at h
    rw [pow_add]
    linear_combination -h + (-1 : ℂ) ^ s * (-1) ^ e * hX
  refine ⟨s, e, hs, he, ?_, z3eq, h2eq, hcc⟩
  have hb1 : (-1 : ℂ) ^ e * (-1) ^ (s + e) = (-1) ^ s := by
    rw [pow_add]; linear_combination (-1 : ℂ) ^ s * hb
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · rcases five with ⟨h, h'⟩ | ⟨h, h'⟩
    · simpa using zm5 h
    · exfalso
      rw [hcc, hb1] at h'
      norm_num at h'
  · rcases five with ⟨h, h'⟩ | ⟨h, h'⟩
    · exfalso
      rw [hcc, hb1] at h'
      norm_num at h'
    · simpa using zm5 h

/-! ## Step 2 for j >= 2 -/

theorem S2_j2 (r k j : ℕ) (hr : 1 ≤ r) (hj : 2 ≤ j) (z5 z2 z3 : ℤ) (c : ℂ)
    (u5 : IsUnit (z5 : ZMod (5 ^ r))) (u3 : IsUnit (z3 : ZMod (3 ^ j))) :
    ∀ s e : ℕ, s < 2 → e < 2 →
      (∀ ε' : ℂ, (ε' = 1 ∨ ε' = -1) → ∀ η ∈ PrimPar 2 (k + 3) ε',
        η (z2 : ZMod (2 ^ (k + 3))) = ε' ^ s * (-1) ^ e) →
      (∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
        ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
        ∀ η2 ∈ PrimPar 2 (k + 3) (-(ψ (-1) * η3 (-1))),
          ψ (z5 : ZMod (5 ^ r)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ j)) = c) →
      (z3 : ZMod (3 ^ j)) * (-1) ^ s = 1 := by
  intro s e hs he hval claim
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨ψe, hψe⟩ := nonempty5 r hr 1 (Or.inl rfl)
  obtain ⟨hψe_p, hψe_s⟩ := mem_PrimPar.1 hψe
  have A0 : ψe (z5 : ZMod (5 ^ r)) ≠ 0 := nz ψe _ u5
  have usg : IsUnit ((-1 : ZMod (3 ^ j)) ^ s) := (isUnit_one.neg).pow s
  by_contra hne
  set g3 : ZMod (3 ^ j) := (z3 : ZMod (3 ^ j)) * (-1) ^ s with hg3
  have hug : IsUnit g3 := u3.mul usg
  have hAe : ψe (z5 : ZMod (5 ^ r)) * (-1) ^ (s + e) ≠ 0 :=
    mul_ne_zero A0 (pow_ne_zero _ (by norm_num))
  refine const_nontriv (3 ^ j) g3 hug hne (tot3 j hj)
    (c / (ψe (z5 : ZMod (5 ^ r)) * (-1) ^ (s + e))) (fun η3 hη3 => ?_)
  obtain ⟨η2, hη2⟩ := nonempty_par2 k (-(ψe (-1) * η3 (-1))) (sgn2 ψe η3)
  have h := claim ψe hψe_p η3 hη3 η2 hη2
  rw [hval _ (sgn2 ψe η3) η2 hη2, hψe_s] at h
  rw [eq_div_iff hAe, hg3, map_mul, map_pow]
  rw [neg_pow] at h
  simp only [one_mul] at h
  rw [pow_add]
  linear_combination h

/-! ## Step 2 for j = 1 -/

/-- There is an even primitive psi mod 5^r and an odd primitive eta2 mod 2^(k+3) with psi(3) eta2(3) != 1.
r = 1: psi(3) = -1 and F4.  r >= 2: otherwise psi(3) would be constant over the even primitive psi, contradicting
lemma G (`G_R`) since 3 != +-1 mod 5. -/
theorem exists_even_odd (r k : ℕ) (hr : 1 ≤ r) :
    ∃ ψ ∈ PrimPar 5 r 1, ∃ η2 ∈ PrimPar 2 (k + 3) (-1),
      ψ (3 : ZMod (5 ^ r)) * η2 (3 : ZMod (2 ^ (k + 3))) ≠ 1 := by
  obtain ⟨t, rfl⟩ | rfl := r_cases r hr
  · by_contra H
    push_neg at H
    obtain ⟨η0, hη0⟩ := nonempty_par2 k (-1) (Or.inr rfl)
    have hη0u : η0 (3 : ZMod (2 ^ (k + 3))) ≠ 0 := nz η0 _ (isUnit_three_2 k)
    have hconst : ∀ ψ ∈ PrimPar 5 (t + 2) 1,
        ψ (((3 : ℤ) : ZMod (5 ^ (t + 2)))) = (η0 (3 : ZMod (2 ^ (k + 3))))⁻¹ := by
      intro ψ hψ
      have := H ψ hψ η0 hη0
      have h3 : ((3 : ℤ) : ZMod (5 ^ (t + 2))) = 3 := by push_cast; rfl
      rw [h3]
      exact eq_inv_of_mul_eq_one_left this
    have hu : IsUnit (((3 : ℤ) : ZMod (5 ^ (t + 2)))) := by
      have := (ZMod.isUnit_iff_coprime 3 (5 ^ (t + 2))).2 (Nat.Coprime.pow_right _ (by norm_num))
      simpa using this
    have h5 : (5 : ℤ) ∣ 5 ^ (t + 2) := dvd_pow_self 5 (by omega)
    rcases G_R t 1 (Or.inl rfl) 3 hu _ hconst with ⟨h, -⟩ | ⟨h, -⟩
    · have := h.of_dvd h5
      revert this; decide
    · have := h.of_dvd h5
      revert this; decide
  · obtain ⟨ψ, hψ⟩ := nonempty5 1 le_rfl 1 (Or.inl rfl)
    obtain ⟨hψ_p, hψ_s⟩ := mem_PrimPar.1 hψ
    obtain ⟨η2, hη2⟩ := nonempty_par2 k (-1) (Or.inr rfl)
    obtain ⟨hη2_p, hη2_s⟩ := mem_PrimPar.1 hη2
    refine ⟨ψ, hψ, η2, hη2, ?_⟩
    rw [even_five_three ψ hψ_p hψ_s]
    intro h
    exact eta2_three_ne k η2 hη2_p hη2_s (by linear_combination -h)

theorem S2_j1 (r k : ℕ) (hr : 1 ≤ r) (η30 : DirichletCharacter ℂ (3 ^ 1)) (hη30 : η30 ≠ 1)
    (z5 z2 z3 : ℤ) (c : ℂ)
    (u5 : IsUnit (z5 : ZMod (5 ^ r))) (u3 : IsUnit (z3 : ZMod (3 ^ 1)))
    (HT : HypTR r k z5 z2 c) :
    ∀ s e : ℕ, s < 2 → e < 2 →
      (∀ ε' : ℂ, (ε' = 1 ∨ ε' = -1) → ∀ η ∈ PrimPar 2 (k + 3) ε',
        η (z2 : ZMod (2 ^ (k + 3))) = ε' ^ s * (-1) ^ e) →
      (∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive →
        ∀ η3 : DirichletCharacter ℂ (3 ^ 1), η3 ≠ 1 →
        ∀ η2 ∈ PrimPar 2 (k + 3) (-(ψ (-1) * η3 (-1))),
          ψ (z5 : ZMod (5 ^ r)) * η2 (z2 : ZMod (2 ^ (k + 3))) * η3 (z3 : ZMod (3 ^ 1)) = c) →
      (z3 : ZMod (3 ^ 1)) * (-1) ^ s = 1 := by
  intro s e hs he hval claim
  haveI : NeZero (3 ^ 1) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : Fact (1 < 3 ^ 1) := ⟨by norm_num⟩
  obtain ⟨ψe, hψe, η2o, hη2o, hne3⟩ := exists_even_odd r k hr
  obtain ⟨hψe_p, hψe_s⟩ := mem_PrimPar.1 hψe
  obtain ⟨hη2o_p, hη2o_s⟩ := mem_PrimPar.1 hη2o
  have A0 : ψe (z5 : ZMod (5 ^ r)) ≠ 0 := nz ψe _ u5
  have usg : IsUnit ((-1 : ZMod (3 ^ 1)) ^ s) := (isUnit_one.neg).pow s
  have hLeg : η30 (-1) = -1 := three_odd η30 hη30
  have sg1 : (-(ψe (-1) * η30 (-1))) = 1 := by rw [hψe_s, hLeg]; norm_num
  obtain ⟨η2e, hη2e⟩ := nonempty_par2 k (-(ψe (-1) * η30 (-1))) (sgn2 ψe η30)
  have hA := claim ψe hψe_p η30 hη30 η2e hη2e
  rw [hval _ (sgn2 ψe η30) η2e hη2e, sg1] at hA
  simp only [one_pow] at hA
  have hB := HT ψe hψe_p η2o hη2o_p (by rw [hψe_s, hη2o_s]; norm_num) hne3
  rw [hval (-1) (Or.inr rfl) η2o hη2o] at hB
  have hLz : η30 (z3 : ZMod (3 ^ 1)) = (-1) ^ s := by
    have hne : ψe (z5 : ZMod (5 ^ r)) * (-1) ^ e ≠ 0 :=
      mul_ne_zero A0 (pow_ne_zero _ (by norm_num))
    apply mul_left_cancel₀ hne
    linear_combination hA - hB
  have hug : IsUnit ((z3 : ZMod (3 ^ 1)) * (-1) ^ s) := u3.mul usg
  have hg : η30 ((z3 : ZMod (3 ^ 1)) * (-1) ^ s) = 1 := by
    rw [map_mul, map_pow, hLz, hLeg, ← mul_pow]; norm_num
  rcases zmod3_cases ((z3 : ZMod (3 ^ 1)) * (-1) ^ s) with h | h | h
  · exfalso; rw [h] at hug; exact not_isUnit_zero hug
  · exact h
  · exfalso; rw [h, hLeg] at hg; norm_num at hg

/-! ## The group core, r >= 1, j >= 1 -/

theorem group_core_R (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (z5 z2 z3 : ℤ) (c : ℂ)
    (u5 : IsUnit (z5 : ZMod (5 ^ r))) (u2 : IsUnit (z2 : ZMod (2 ^ (k + 3))))
    (u3 : IsUnit (z3 : ZMod (3 ^ j))) (H : HypR r k j z5 z2 z3 c)
    (HT : j = 1 → HypTR r k z5 z2 c) :
    ∃ s e : ℕ, s < 2 ∧ e < 2 ∧ (z5 : ZMod (5 ^ r)) = (-1) ^ s ∧ (z3 : ZMod (3 ^ j)) = (-1) ^ s ∧
      (z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e ∧ c = (-1) ^ (s + e) := by
  rcases Nat.lt_or_ge j 2 with h | h
  · obtain rfl : j = 1 := by omega
    obtain ⟨η30, hη30⟩ := exists_ne_one3_j1
    exact group_core_gen r k 1 hr η30 hη30 z5 z2 z3 c u5 u2 u3 H
      (S2_j1 r k hr η30 hη30 z5 z2 z3 c u5 u3 (HT rfl))
  · obtain ⟨η30, hη30⟩ := exists_ne_one3 j h
    exact group_core_gen r k j hr η30 hη30 z5 z2 z3 c u5 u2 u3 H
      (S2_j2 r k j hr h z5 z2 z3 c u5 u3)

/-! ## Converse / witnesses -/

theorem group_core_R_converse (r k j : ℕ) (s e : ℕ) (z5 z2 z3 : ℤ)
    (e5 : (z5 : ZMod (5 ^ r)) = (-1) ^ s) (e3 : (z3 : ZMod (3 ^ j)) = (-1) ^ s)
    (e2 : (z2 : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e) :
    HypR r k j z5 z2 z3 ((-1) ^ (s + e)) := by
  intro ψ _ η2 hη2 η3 _ hodd
  rw [e5, e2, e3, map_pow, map_mul, map_pow, map_pow, map_pow, eta2_val k η2 hη2]
  have key : ψ (-1) ^ s * (η2 (-1) ^ s * (-1) ^ e) * η3 (-1) ^ s =
      (ψ (-1) * η2 (-1) * η3 (-1)) ^ s * (-1) ^ e := by ring
  rw [key, hodd, pow_add (-1 : ℂ) s e]

theorem admissible_exists_R (r k j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    ∃ (ψ : DirichletCharacter ℂ (5 ^ r)) (η2 : DirichletCharacter ℂ (2 ^ (k + 3)))
      (η3 : DirichletCharacter ℂ (3 ^ j)), ψ.IsPrimitive ∧ η2.IsPrimitive ∧ η3 ≠ 1 ∧
        ψ (-1) * η2 (-1) * η3 (-1) = -1 := by
  obtain ⟨ψe, hψe⟩ := nonempty5 r hr 1 (Or.inl rfl)
  obtain ⟨hp, hs⟩ := mem_PrimPar.1 hψe
  have h3 : ∃ η : DirichletCharacter ℂ (3 ^ j), η ≠ 1 := by
    rcases Nat.lt_or_ge j 2 with h | h
    · obtain rfl : j = 1 := by omega
      exact exists_ne_one3_j1
    · exact exists_ne_one3 j h
  obtain ⟨η3, h3⟩ := h3
  obtain ⟨η2, hη2⟩ := nonempty_par2 k _ (sgn2 ψe η3)
  obtain ⟨hp2, hs2⟩ := mem_PrimPar.1 hη2
  refine ⟨ψe, η2, η3, hp, hp2, h3, ?_⟩
  rw [hs2]
  rcases sign_val ψe with h | h <;> rcases sign_val η3 with h' | h' <;> rw [h, h'] <;> norm_num

/-- Witness for `G_R`: z = 1 and z = -1 satisfy the constancy hypothesis (with c = 1, c = eps) on a NONEMPTY set. -/
theorem G_R_witness (t : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    (PrimPar 5 (t + 2) ε).Nonempty ∧
    (∀ ψ ∈ PrimPar 5 (t + 2) ε, ψ ((1 : ℤ) : ZMod (5 ^ (t + 2))) = 1) ∧
    (∀ ψ ∈ PrimPar 5 (t + 2) ε, ψ ((-1 : ℤ) : ZMod (5 ^ (t + 2))) = ε) := by
  refine ⟨nonempty_R t ε hε, fun ψ _ => by simp, fun ψ hψ => ?_⟩
  have := (mem_PrimPar.1 hψ).2
  simpa using this

end Erdos634.GA2NR1

#print axioms Erdos634.GA2NR1.five_odd_gen
#print axioms Erdos634.GA2NR1.exists_even_odd
#print axioms Erdos634.GA2NR1.group_core_R
#print axioms Erdos634.GA2NR1.group_core_R_converse
#print axioms Erdos634.GA2NR1.admissible_exists_R
#print axioms Erdos634.GA2NR1.G_R_witness
