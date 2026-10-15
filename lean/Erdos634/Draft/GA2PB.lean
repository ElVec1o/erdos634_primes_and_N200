/-
GA2P, atom 3b: **Lemma N at p = 3** and the coset/support lemma (GA2Y_NOTES Theorem B/C, "(I2)").

  `card_N3`        : N_3 = ker((Z/3^j)^x -> (Z/3^(j-1))^x) has exactly 3 elements (j >= 2).
  `unitsMap_neg`   : unitsMap (-u) = - unitsMap u.
  `neg_unitsMap_ne`: -u and u have different images mod 3^(j-1) (j >= 2), i.e. -1 is not in N_3.
  `lemmaN3`        : (instance of LemmaSN.lemmaN at p = 3) Phi + eps [-1] Phi is N_3-invariant when sum_u psi(u) Phi(u) = 0
                     for all primitive psi mod 3^j of parity eps.
  `top3_zero_small`: if moreover the set Q = {v : Phi v != 0 or Phi(-v) != 0} lies in a set P with |P| < 6, then
                     Phi(u) = - eps Phi(-u) for every unit u.   (the "<= 4 points < 6 = |g N_3 u -g N_3|" step)
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.LemmaSN
import Erdos634.Draft.LemmaSC

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2PB

open Erdos634.LemmaSN (pred_dvd lemmaN lemmaN_a)

theorem card_N3 (j : ℕ) (hj : 2 ≤ j) :
    (univ.filter (fun v : (ZMod (3 ^ j))ˣ => ZMod.unitsMap (pred_dvd 3 j) v = 1)).card = 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  haveI : NeZero (3 ^ (m + 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (m + 2 - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h := Erdos634.LemmaSC.fiber_card (n := 3 ^ (m + 2)) (d := 3 ^ (m + 2 - 1)) (pred_dvd 3 (m + 2))
  have e1 : (3 ^ (m + 2) : ℕ).totient = 3 ^ (m + 1) * 2 := by
    rw [Nat.totient_prime_pow (by norm_num) (by omega)]; simp
  have e2 : (3 ^ (m + 2 - 1) : ℕ).totient = 3 ^ m * 2 := by
    rw [show m + 2 - 1 = m + 1 by omega, Nat.totient_prime_pow (by norm_num) (by omega)]; simp
  rw [e1, e2] at h
  have : ((univ.filter (fun v : (ZMod (3 ^ (m + 2)))ˣ =>
      ZMod.unitsMap (pred_dvd 3 (m + 2)) v = 1)).card : ℂ) = ((3 : ℕ) : ℂ) := by
    rw [h]
    push_cast
    rw [pow_succ]
    field_simp
  exact_mod_cast this

theorem unitsMap_neg {m n : ℕ} [NeZero m] [NeZero n] (h : n ∣ m) (u : (ZMod m)ˣ) :
    ZMod.unitsMap h (-u) = - ZMod.unitsMap h u := by
  apply Units.ext
  simp [ZMod.unitsMap]

theorem neg_unitsMap_ne (j : ℕ) (hj : 2 ≤ j) (u : (ZMod (3 ^ j))ˣ) :
    ZMod.unitsMap (pred_dvd 3 j) (-u) ≠ ZMod.unitsMap (pred_dvd 3 j) u := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (j - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  intro h
  rw [unitsMap_neg] at h
  have h3 : 3 ∣ 3 ^ (j - 1) := dvd_pow_self 3 (by omega)
  have h' := congrArg (ZMod.unitsMap h3) h
  rw [unitsMap_neg] at h'
  revert h'
  generalize ZMod.unitsMap h3 (ZMod.unitsMap (pred_dvd 3 j) u) = w
  revert w
  decide

theorem lemmaN3 (j : ℕ) (hj : 1 ≤ j) (Φ : (ZMod (3 ^ j))ˣ → ℂ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (3 ^ j), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (3 ^ j))ˣ, ψ (u : ZMod (3 ^ j)) * Φ u = 0)
    (u n0 : (ZMod (3 ^ j))ˣ) (hn0 : ZMod.unitsMap (pred_dvd 3 j) n0 = 1) :
    Φ (u * n0) + ε * Φ (-(u * n0)) = Φ u + ε * Φ (-u) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact lemmaN hj Φ hε h u n0 hn0

theorem top3_zero_small (j : ℕ) (hj : 2 ≤ j) (Φ : (ZMod (3 ^ j))ˣ → ℂ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (3 ^ j), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (3 ^ j))ˣ, ψ (u : ZMod (3 ^ j)) * Φ u = 0)
    (P : Finset (ZMod (3 ^ j))ˣ) (hP : ∀ v, (Φ v ≠ 0 ∨ Φ (-v) ≠ 0) → v ∈ P) (hPc : P.card < 6) :
    ∀ u, Φ u = -ε * Φ (-u) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine lemmaN_a (by omega) Φ hε h ?_
  intro u
  rw [card_N3 j hj]
  by_contra hge
  push Not at hge
  set S := univ.filter (fun v : (ZMod (3 ^ j))ˣ => ZMod.unitsMap (pred_dvd 3 j) v = ZMod.unitsMap (pred_dvd 3 j) u ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0)) with hS
  set S' := univ.filter (fun v : (ZMod (3 ^ j))ˣ => ZMod.unitsMap (pred_dvd 3 j) v = ZMod.unitsMap (pred_dvd 3 j) (-u) ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0)) with hS'
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ (j - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hcardS' : 3 ≤ S'.card := by
    refine le_trans hge (Finset.card_le_card_of_injOn (fun v => -v) ?_ ?_)
    · intro v hv
      have hv' := (mem_filter.1 hv).2
      refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
      · rw [unitsMap_neg, hv'.1, unitsMap_neg]
      · rw [neg_neg]; exact hv'.2.symm
    · intro x _ y _ hxy; exact neg_injective hxy
  have hdisj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact neg_unitsMap_ne j hj u ((mem_filter.1 hv').2.1.symm.trans (mem_filter.1 hv).2.1)
  have hsub : S ∪ S' ⊆ P := by
    intro v hv
    rcases mem_union.1 hv with hv | hv
    · exact hP v (mem_filter.1 hv).2.2
    · exact hP v (mem_filter.1 hv).2.2
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  omega

end Erdos634.GA2PB

#print axioms Erdos634.GA2PB.card_N3
#print axioms Erdos634.GA2PB.neg_unitsMap_ne
#print axioms Erdos634.GA2PB.lemmaN3
#print axioms Erdos634.GA2PB.top3_zero_small
