/-
GA2U, atom D: three atoms on (Z/3^j)^x (Lemma T, case B).
  `three_atoms` : weights c_0, c_1 = kappa c_0, c_2 at three unit tokens a_0, a_1, a_2 mod 3^j (j >= 2), a_1 != +-a_0,
                  with sum_t c_t eta(a_t) = 0 for every primitive EVEN eta mod 3^j, kappa != 0, 1:  c_0 = c_1 = c_2 = 0.
                  (Lemma N at p = 3 makes Psi(v) = Phi(v) + Phi(-v) N_3-periodic; `GA2UC.periodic_small` counts supports.)
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2UC
import Erdos634.Draft.GA2PC
import Erdos634.Draft.GA2PB

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2UD

open Erdos634.LemmaSN (pred_dvd)
open Erdos634.GA2PC (PhiV sum_PhiV)

theorem three_atoms (j : ℕ) (hj : 2 ≤ j) (a : Fin 3 → ℕ) (c : Fin 3 → ℂ)
    (hu : ∀ t, IsUnit (a t : ZMod (3 ^ j)))
    (h10 : (a 1 : ZMod (3 ^ j)) ≠ a 0 ∧ (a 1 : ZMod (3 ^ j)) ≠ -(a 0 : ZMod (3 ^ j)))
    (horth : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive → η (-1) = 1 →
      ∑ t, c t * η (a t : ZMod (3 ^ j)) = 0)
    (κ : ℂ) (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1) (hc : c 1 = κ * c 0) :
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set p : Fin 3 → (ZMod (3 ^ j))ˣ := fun i => (hu i).unit with hp
  have hpc : ∀ i, ((p i : (ZMod (3 ^ j))ˣ) : ZMod (3 ^ j)) = (a i : ZMod (3 ^ j)) := fun i => IsUnit.unit_spec _
  set Φ := PhiV (3 ^ j) a c Finset.univ with hΦ
  have hΦe : ∀ v : (ZMod (3 ^ j))ˣ, Φ v = (if v = p 0 then c 0 else 0) + (if v = p 1 then c 1 else 0) +
      (if v = p 2 then c 2 else 0) := by
    intro v
    show (∑ t : Fin 3, if (v : ZMod (3 ^ j)) = (a t : ZMod (3 ^ j)) then c t else 0) = _
    rw [Fin.sum_univ_three]
    simp only [← hpc, Units.val_inj]
  have hN : ∀ u n0 : (ZMod (3 ^ j))ˣ, ZMod.unitsMap (pred_dvd 3 j) n0 = 1 →
      Φ (u * n0) + 1 * Φ (-(u * n0)) = Φ u + 1 * Φ (-u) := by
    intro u n0 hn0
    exact Erdos634.GA2PB.lemmaN3 j (by omega) Φ (ε := 1) (Or.inl rfl)
      (by
        intro ψ hψ hψ1
        rw [sum_PhiV (3 ^ j) a c Finset.univ (fun t _ => hu t) ψ]
        exact horth ψ hψ hψ1) u n0 hn0
  set Ψ : (ZMod (3 ^ j))ˣ → ℂ := fun v => Φ v + Φ (-v) with hΨ
  have hneg : ∀ v, Ψ (-v) = Ψ v := by intro v; simp only [hΨ, neg_neg]; ring
  have hper : ∀ n0 : (ZMod (3 ^ j))ˣ, ZMod.unitsMap (pred_dvd 3 j) n0 = 1 → ∀ v, Ψ (v * n0) = Ψ v := by
    intro n0 hn0 v
    have := hN v n0 hn0
    simp only [hΨ]
    linear_combination this
  have hsupp : ∀ v, Ψ v ≠ 0 → ∃ i, v = p i ∨ v = -p i := by
    intro v hv
    by_contra hcon
    push Not at hcon
    apply hv
    simp only [hΨ, hΦe]
    have h1 : ∀ i, v ≠ p i := fun i => (hcon i).1
    have h2 : ∀ i, -v ≠ p i := fun i h => (hcon i).2 (by rw [← h]; simp)
    simp [h1, h2]
  have hp10 : p 1 ≠ p 0 ∧ p 1 ≠ -p 0 := by
    constructor
    · intro h; apply h10.1; rw [← hpc, ← hpc, h]
    · intro h; apply h10.2; rw [← hpc, ← hpc, h]; simp
  rcases Erdos634.GA2UC.periodic_small j hj Ψ hneg hper p hsupp with hz | ⟨hdist, hnn, hconst, hne0⟩
  · -- Psi = 0
    have e0 := hz (p 0)
    have e1 := hz (p 1)
    have e2 := hz (p 2)
    simp only [hΨ, hΦe] at e0 e1 e2
    have hnn0 : -p 0 ≠ p 0 := Erdos634.GA2UB.neg_ne_self3 j (by omega) (p 0)
    have hnn1 : -p 1 ≠ p 1 := Erdos634.GA2UB.neg_ne_self3 j (by omega) (p 1)
    have hnn2 : -p 2 ≠ p 2 := Erdos634.GA2UB.neg_ne_self3 j (by omega) (p 2)
    have hn10 : -p 1 ≠ p 0 := fun h => hp10.2 (by rw [← h]; simp)
    have hn01 : -p 0 ≠ p 1 := fun h => hp10.2 h.symm
    have hp01 : p 0 ≠ p 1 := fun h => hp10.1 h.symm
    simp only [if_true, if_neg hp01, if_neg hnn0, if_neg hn01, zero_add, add_zero] at e0
    simp only [if_true, if_neg hp10.1, if_neg hnn1, if_neg hn10, zero_add, add_zero] at e1
    simp only [if_true, if_neg hnn2, add_zero] at e2
    have hc0 : c 0 = 0 := by
      by_contra h0
      have h1' : c 1 ≠ 0 := by rw [hc]; exact mul_ne_zero hκ0 h0
      have hA : p 0 = p 2 ∨ -p 0 = p 2 := by
        by_contra hh
        push Not at hh
        rw [if_neg hh.1, if_neg hh.2] at e0
        exact h0 (by simpa using e0)
      have hB : p 1 = p 2 ∨ -p 1 = p 2 := by
        by_contra hh
        push Not at hh
        rw [if_neg hh.1, if_neg hh.2] at e1
        exact h1' (by simpa using e1)
      rcases hA with hA | hA <;> rcases hB with hB | hB
      · exact hp10.1 (hB.trans hA.symm)
      · exact hp10.2 (neg_eq_iff_eq_neg.1 (hB.trans hA.symm))
      · exact hp10.2 (hB.trans hA.symm)
      · exact hp10.1 (neg_injective (hB.trans hA.symm))
    have hc1 : c 1 = 0 := by rw [hc, hc0, mul_zero]
    refine ⟨hc0, hc1, ?_⟩
    rw [hc0, hc1] at e2
    simpa using e2
  · exfalso
    have q0 : Ψ (p 0) = c 0 := by
      show Φ (p 0) + Φ (-p 0) = c 0
      rw [hΦe (p 0), hΦe (-p 0)]
      rw [if_pos rfl, if_neg (hdist 0 1 (by decide)).1, if_neg (hdist 0 2 (by decide)).1, if_neg (hnn 0),
        if_neg (fun h => (hdist 1 0 (by decide)).2 h.symm), if_neg (fun h => (hdist 2 0 (by decide)).2 h.symm)]
      ring
    have q1 : Ψ (p 1) = c 1 := by
      show Φ (p 1) + Φ (-p 1) = c 1
      rw [hΦe (p 1), hΦe (-p 1)]
      rw [if_neg (hdist 1 0 (by decide)).1, if_pos rfl, if_neg (hdist 1 2 (by decide)).1,
        if_neg (fun h => (hdist 0 1 (by decide)).2 h.symm), if_neg (hnn 1),
        if_neg (fun h => (hdist 2 1 (by decide)).2 h.symm)]
      ring
    have h01 : c 1 = c 0 := by rw [← q1, ← q0]; exact hconst 1
    have : (κ - 1) * c 0 = 0 := by linear_combination hc.symm.trans h01
    have hc00 : c 0 = 0 := (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hκ1)
    exact hne0 (by rw [q0, hc00])

end Erdos634.GA2UD

#print axioms Erdos634.GA2UD.three_atoms
