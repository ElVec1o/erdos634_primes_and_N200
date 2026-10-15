/-
GA2Q, item (1): **Lemma N at p = 5**  (GA2Y_NOTES (I2); the p = 5 analogue of GA2PB).

  `card_N5`          : for r >= 2, N_5 = ker((Z/5^r)^x -> (Z/5^(r-1))^x) has exactly 5 elements.
  `neg_unitsMap_ne5` : for r >= 2, -u and u have different images mod 5^(r-1), i.e. -1 is not in N_5.
  `lemmaN5`          : (instance of LemmaSN.lemmaN at p = 5, ANY r >= 1) Phi + eps [-1] Phi is N_5-invariant when
                       sum_u psi(u) Phi(u) = 0 for all primitive psi mod 5^r of parity eps.
  `top5_zero_small`  : (r >= 2) if the points {v : Phi v != 0 or Phi(-v) != 0} lie in a set P with |P| < 10, then
                       Phi(u) = -eps Phi(-u) for every u.   ("<= 3 < 5 points per N_5-coset" step of Prop K)
  `lemmaN5_r1_b/_c`  : (r = 1, p = 5, N = the whole group) eps = -1: Phi is EVEN, no support condition; eps = +1: Phi = -[-1]Phi as
                       soon as |supp(Phi + [-1]Phi)| < 4 = p - 1  (instances of LemmaSN.lemmaN_b/_c at p = 5).
  `sum_N5_witness`   : witnesses: a Phi on (Z/25)^x with support 2 points, with the character hypothesis, nonzero.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.LemmaSN
import Erdos634.Draft.LemmaSC
import Erdos634.Draft.GA2PB

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2QB

open Erdos634.LemmaSN (pred_dvd lemmaN lemmaN_a)

theorem card_N5 (r : ℕ) (hr : 2 ≤ r) :
    (univ.filter (fun v : (ZMod (5 ^ r))ˣ => ZMod.unitsMap (pred_dvd 5 r) v = 1)).card = 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  haveI : NeZero (5 ^ (m + 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ (m + 2 - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h := Erdos634.LemmaSC.fiber_card (n := 5 ^ (m + 2)) (d := 5 ^ (m + 2 - 1)) (pred_dvd 5 (m + 2))
  have e1 : (5 ^ (m + 2) : ℕ).totient = 5 ^ (m + 1) * 4 := by
    rw [Nat.totient_prime_pow (by norm_num) (by omega)]; simp
  have e2 : (5 ^ (m + 2 - 1) : ℕ).totient = 5 ^ m * 4 := by
    rw [show m + 2 - 1 = m + 1 by omega, Nat.totient_prime_pow (by norm_num) (by omega)]; simp
  rw [e1, e2] at h
  have : ((univ.filter (fun v : (ZMod (5 ^ (m + 2)))ˣ =>
      ZMod.unitsMap (pred_dvd 5 (m + 2)) v = 1)).card : ℂ) = ((5 : ℕ) : ℂ) := by
    rw [h]
    push_cast
    rw [pow_succ]
    field_simp
  exact_mod_cast this

theorem neg_unitsMap_ne5 (r : ℕ) (hr : 2 ≤ r) (u : (ZMod (5 ^ r))ˣ) :
    ZMod.unitsMap (pred_dvd 5 r) (-u) ≠ ZMod.unitsMap (pred_dvd 5 r) u := by
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ (r - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero 5 := ⟨by norm_num⟩
  intro h
  rw [Erdos634.GA2PB.unitsMap_neg] at h
  have h5 : 5 ∣ 5 ^ (r - 1) := dvd_pow_self 5 (by omega)
  have h' := congrArg (ZMod.unitsMap h5) h
  rw [Erdos634.GA2PB.unitsMap_neg] at h'
  revert h'
  generalize ZMod.unitsMap h5 (ZMod.unitsMap (pred_dvd 5 r) u) = w
  revert w
  decide

theorem lemmaN5 (r : ℕ) (hr : 1 ≤ r) (Φ : (ZMod (5 ^ r))ˣ → ℂ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (5 ^ r))ˣ, ψ (u : ZMod (5 ^ r)) * Φ u = 0)
    (u n0 : (ZMod (5 ^ r))ˣ) (hn0 : ZMod.unitsMap (pred_dvd 5 r) n0 = 1) :
    Φ (u * n0) + ε * Φ (-(u * n0)) = Φ u + ε * Φ (-u) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact lemmaN hr Φ hε h u n0 hn0

theorem top5_zero_small (r : ℕ) (hr : 2 ≤ r) (Φ : (ZMod (5 ^ r))ˣ → ℂ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (5 ^ r))ˣ, ψ (u : ZMod (5 ^ r)) * Φ u = 0)
    (P : Finset (ZMod (5 ^ r))ˣ) (hP : ∀ v, (Φ v ≠ 0 ∨ Φ (-v) ≠ 0) → v ∈ P) (hPc : P.card < 10) :
    ∀ u, Φ u = -ε * Φ (-u) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine lemmaN_a (by omega) Φ hε h ?_
  intro u
  rw [card_N5 r hr]
  by_contra hge
  push Not at hge
  set S := univ.filter (fun v : (ZMod (5 ^ r))ˣ => ZMod.unitsMap (pred_dvd 5 r) v = ZMod.unitsMap (pred_dvd 5 r) u ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0)) with hS
  set S' := univ.filter (fun v : (ZMod (5 ^ r))ˣ => ZMod.unitsMap (pred_dvd 5 r) v = ZMod.unitsMap (pred_dvd 5 r) (-u) ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0)) with hS'
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (5 ^ (r - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hcardS' : 5 ≤ S'.card := by
    refine le_trans hge (Finset.card_le_card_of_injOn (fun v => -v) ?_ ?_)
    · intro v hv
      have hv' := (mem_filter.1 hv).2
      refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
      · rw [Erdos634.GA2PB.unitsMap_neg, hv'.1, Erdos634.GA2PB.unitsMap_neg]
      · rw [neg_neg]; exact hv'.2.symm
    · intro x _ y _ hxy; exact neg_injective hxy
  have hdisj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact neg_unitsMap_ne5 r hr u ((mem_filter.1 hv').2.1.symm.trans (mem_filter.1 hv).2.1)
  have hsub : S ∪ S' ⊆ P := by
    intro v hv
    rcases mem_union.1 hv with hv | hv
    · exact hP v (mem_filter.1 hv).2.2
    · exact hP v (mem_filter.1 hv).2.2
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  omega

theorem lemmaN5_r1_b (Φ : (ZMod (5 ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (5 ^ 1))ˣ, ψ (u : ZMod (5 ^ 1)) * Φ u = 0) : ∀ u, Φ u = Φ (-u) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact Erdos634.LemmaSN.lemmaN_b Φ h

theorem lemmaN5_r1_c (Φ : (ZMod (5 ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (5 ^ 1))ˣ, ψ (u : ZMod (5 ^ 1)) * Φ u = 0)
    (hcard : (univ.filter (fun v : (ZMod (5 ^ 1))ˣ => Φ v + Φ (-v) ≠ 0)).card < 4) :
    ∀ u, Φ u = -Φ (-u) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact Erdos634.LemmaSN.lemmaN_c Φ h (by simpa using hcard)

/-! ### Witnesses (controls): the hypotheses of the p = 5 statements are satisfiable and the statements are not `bot`-trivial -/

/-- (Z/25)^x: Phi = delta_1 - delta_{-1} satisfies the character hypothesis (eps = +1, even psi) with a 2-point support,
and Phi 1 != 0; the conclusion Phi = -eps [-1] Phi holds for it.  So `top5_zero_small` has a non-vacuous instance. -/
theorem top5_witness : ∃ Φ : (ZMod (5 ^ 2))ˣ → ℂ, Φ 1 ≠ 0 ∧
    (∀ ψ : DirichletCharacter ℂ (5 ^ 2), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (5 ^ 2))ˣ, ψ (u : ZMod (5 ^ 2)) * Φ u = 0) ∧
    (∀ u, Φ u = -(1:ℂ) * Φ (-u)) := by
  have h1m : (1 : (ZMod (5 ^ 2))ˣ) ≠ -1 := by decide
  refine ⟨fun u => (if u = 1 then 1 else 0) - (if u = -1 then 1 else 0), ?_, ?_, ?_⟩
  · simp [h1m]
  · intro ψ _ hψ
    simp only [mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ,
      if_true, Units.val_one, Units.val_neg, MulChar.map_one, hψ, sub_self]
  · intro u
    by_cases h1 : u = 1
    · subst h1; simp [h1m, h1m.symm]
    · by_cases h2 : u = -1
      · subst h2; simp [h1m, h1m.symm]
      · have h3 : -u ≠ 1 := fun h => h2 (by rw [← h]; simp)
        have h4 : -u ≠ -1 := fun h => h1 (neg_injective h)
        simp [h1, h2, h3, h4]

/-- instance of `card_N5` at r = 2 (|N_5| = 5 in (Z/25)^x). -/
theorem card_N5_witness : (Finset.univ.filter (fun v : (ZMod (5 ^ 2))ˣ =>
    ZMod.unitsMap (pred_dvd 5 2) v = 1)).card = 5 := card_N5 2 le_rfl

end Erdos634.GA2QB

#print axioms Erdos634.GA2QB.card_N5
#print axioms Erdos634.GA2QB.neg_unitsMap_ne5
#print axioms Erdos634.GA2QB.lemmaN5
#print axioms Erdos634.GA2QB.top5_zero_small
#print axioms Erdos634.GA2QB.lemmaN5_r1_b
#print axioms Erdos634.GA2QB.lemmaN5_r1_c
#print axioms Erdos634.GA2QB.top5_witness
