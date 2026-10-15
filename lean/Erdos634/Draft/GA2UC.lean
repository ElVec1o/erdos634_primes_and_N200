/-
GA2U, atom C: the support-counting lemma behind Lemma T, case B (one odd, one even column).
  `periodic_small` : Psi on (Z/3^j)^x, even (Psi(-v) = Psi v) and N_3-periodic (Psi(v n0) = Psi v, n0 in N_3), whose support lies in
                     {+-p_0, +-p_1, +-p_2}:  either Psi = 0, or the six points +-p_i are pairwise distinct, Psi is constant on them,
                     and that constant is nonzero.   (|+-N_3| = 6; so a nonzero periodic Psi needs 6 support points.)
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2UB

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UC

open Erdos634.LemmaSN (pred_dvd)
open Erdos634.GA2UB

theorem periodic_small (j : ℕ) (hj : 2 ≤ j) (Ψ : (ZMod (3 ^ j))ˣ → ℂ)
    (hneg : ∀ v, Ψ (-v) = Ψ v)
    (hper : ∀ n0 : (ZMod (3 ^ j))ˣ, ZMod.unitsMap (pred_dvd 3 j) n0 = 1 → ∀ v, Ψ (v * n0) = Ψ v)
    (p : Fin 3 → (ZMod (3 ^ j))ˣ) (hsupp : ∀ v, Ψ v ≠ 0 → ∃ i, v = p i ∨ v = -p i) :
    (∀ v, Ψ v = 0) ∨
      ((∀ i k, i ≠ k → p i ≠ p k ∧ p i ≠ -p k) ∧ (∀ i, -p i ≠ p i) ∧
        (∀ i, Ψ (p i) = Ψ (p 0)) ∧ Ψ (p 0) ≠ 0) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  by_cases hall : ∀ v, Ψ v = 0
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨v0, hv0⟩ := hall
  obtain ⟨-, n0, -, -, hmem, hne⟩ := ker_gen j hj
  have hn3 : n0 ^ 3 = 1 := Erdos634.GA2SJ.ker_pow3 j hj n0 hmem
  have hord : orderOf n0 = 3 := orderOf_eq_prime hn3 hne
  have hm1 : (-1 : (ZMod (3 ^ j))ˣ) ≠ 1 := by
    intro h
    exact neg_ne_self3 j (by omega) 1 (by simpa using h)
  have hinv : ∀ k : ℕ, Ψ (v0 * n0 ^ k) = Ψ v0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, hper n0 hmem, ih]
  set f : Fin 3 × Bool → (ZMod (3 ^ j))ˣ := fun x => (if x.2 then v0 else -v0) * n0 ^ (x.1 : ℕ) with hf
  have hfΨ : ∀ x, Ψ (f x) = Ψ v0 := by
    rintro ⟨k, s⟩
    cases s
    · simp only [hf, Bool.false_eq_true, if_false]
      rw [neg_mul, hneg, hinv]
    · simp only [hf, if_true]
      exact hinv k
  have hpow : ∀ k k' : Fin 3, n0 ^ (k : ℕ) = n0 ^ (k' : ℕ) → k = k' := by
    intro k k' h
    have := pow_injOn_Iio_orderOf (x := n0) (by rw [hord]; exact k.2) (by rw [hord]; exact k'.2) h
    exact Fin.ext this
  have hcube : ∀ k : Fin 3, (n0 ^ (k : ℕ)) ^ 3 = 1 := by
    intro k; rw [← pow_mul, mul_comm, pow_mul, hn3, one_pow]
  have key : ∀ k k' : Fin 3, n0 ^ (k : ℕ) ≠ -(n0 ^ (k' : ℕ)) := by
    intro k k' h
    have h3 := congrArg (fun w : (ZMod (3 ^ j))ˣ => w ^ 3) h
    simp only [hcube k, Odd.neg_pow (by decide : Odd 3), hcube k'] at h3
    exact hm1 h3.symm
  have hfinj : Function.Injective f := by
    rintro ⟨k, s⟩ ⟨k', s'⟩ h
    simp only [hf] at h
    cases s <;> cases s' <;> simp only [Bool.false_eq_true, if_false, if_true] at h
    · rw [hpow k k' (mul_left_cancel h)]
    · exfalso
      rw [neg_mul, ← mul_neg] at h
      exact key k' k (mul_left_cancel h).symm
    · exfalso
      rw [neg_mul, ← mul_neg] at h
      exact key k k' (mul_left_cancel h)
    · rw [hpow k k' (mul_left_cancel h)]
  -- the support of Psi lies in T = {+-p_i}; the orbit of v0 has 6 points inside it
  set g : Fin 3 × Bool → (ZMod (3 ^ j))ˣ := fun x => if x.2 then p x.1 else -p x.1 with hg
  have hsub : (univ : Finset (Fin 3 × Bool)).image f ⊆ (univ : Finset (Fin 3 × Bool)).image g := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hw
    have hne0 : Ψ (f x) ≠ 0 := by rw [hfΨ]; exact hv0
    obtain ⟨i, hi⟩ := hsupp _ hne0
    rcases hi with hi | hi
    · exact Finset.mem_image.2 ⟨(i, true), Finset.mem_univ _, by simp [hg, hi]⟩
    · exact Finset.mem_image.2 ⟨(i, false), Finset.mem_univ _, by simp [hg, hi]⟩
  have hc6 : ((univ : Finset (Fin 3 × Bool)).image f).card = 6 := by
    rw [Finset.card_image_of_injective _ hfinj]; simp
  have hcT : ((univ : Finset (Fin 3 × Bool)).image g).card ≤ 6 := by
    have := Finset.card_image_le (s := (univ : Finset (Fin 3 × Bool))) (f := g)
    simpa using this
  have hTeq : (univ : Finset (Fin 3 × Bool)).image f = (univ : Finset (Fin 3 × Bool)).image g :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hginj : Function.Injective g := by
    have hc : ((univ : Finset (Fin 3 × Bool)).image g).card = (univ : Finset (Fin 3 × Bool)).card := by
      rw [← hTeq, hc6]; simp
    exact fun a b h => Finset.injOn_of_card_image_eq hc (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) h
  have hpΨ : ∀ i, Ψ (p i) = Ψ v0 := by
    intro i
    have : p i ∈ (univ : Finset (Fin 3 × Bool)).image g :=
      Finset.mem_image.2 ⟨(i, true), Finset.mem_univ _, by simp [hg]⟩
    rw [← hTeq] at this
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 this
    rw [← hx, hfΨ]
  refine ⟨?_, fun i => neg_ne_self3 j (by omega) (p i), fun i => by rw [hpΨ, hpΨ], by rw [hpΨ]; exact hv0⟩
  intro i k hik
  constructor
  · intro h
    have := hginj (a₁ := (i, true)) (a₂ := (k, true)) (by simpa [hg] using h)
    exact hik (by simpa using this)
  · intro h
    have := hginj (a₁ := (i, true)) (a₂ := (k, false)) (by simpa [hg] using h)
    simp at this

end Erdos634.GA2UC

#print axioms Erdos634.GA2UC.periodic_small
