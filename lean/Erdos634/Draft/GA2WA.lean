/-
GA2W, part A: infrastructure for the j = 1 atoms KbJ1Lab / KcJ1Lab (GA2V_NOTES).
  `cast_int_ne`, `mul_unit_inj`, `unit_int` : small integer multiples of a unit are distinct mod 5^r, r >= 2.
  `lemmaN_Z`   : 5-adic orthogonality, +-support version (GA2V Lemma N):  |P| < 10 instead of V.card <= 4.
  `lemmaN_lin` : the same for tokens m_i * u with integer multipliers m_i (|m_i| <= 12, 5 !| m_i).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SM
import Erdos634.Draft.GA2SP
import Erdos634.Draft.GA2QB

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2WA

open DirichletCharacter

theorem cast_int_ne (r : ℕ) (hr : 2 ≤ r) (n : ℤ) (h0 : n ≠ 0) (h1 : -25 < n) (h2 : n < 25) :
    (n : ZMod (5 ^ r)) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h25 : 25 ≤ 5 ^ r := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have h3 : (5 ^ r : ℕ) ∣ n.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 h
    simpa using this
  have h4 := Nat.le_of_dvd (Int.natAbs_pos.2 h0) h3
  omega

theorem mul_unit_inj (r : ℕ) (hr : 2 ≤ r) {u : ZMod (5 ^ r)} (hu : IsUnit u) (a b : ℤ)
    (h1 : -25 < a - b) (h2 : a - b < 25) (h : (a : ZMod (5 ^ r)) * u = (b : ZMod (5 ^ r)) * u) : a = b := by
  by_contra hne
  have h0 : ((a - b : ℤ) : ZMod (5 ^ r)) * u = 0 := by push_cast; linear_combination h
  have := (hu.mul_left_eq_zero).1 h0
  exact cast_int_ne r hr (a - b) (sub_ne_zero.2 hne) h1 h2 this

theorem unit_int (r : ℕ) (n : ℤ) (h : ¬ (5 : ℤ) ∣ n) : IsUnit ((n : ℤ) : ZMod (5 ^ r)) := by
  have h' : ¬ 5 ∣ n.natAbs := by
    intro hh
    apply h
    have : ((5 : ℕ) : ℤ) ∣ n := Int.natCast_dvd.2 hh
    simpa using this
  rcases Int.natAbs_eq n with hn | hn
  · have e : ((n : ℤ) : ZMod (5 ^ r)) = ((n.natAbs : ℤ) : ZMod (5 ^ r)) := congrArg _ hn
    rw [e, Int.cast_natCast]; exact Erdos634.GA2SD.unit5r r _ h'
  · have e : ((n : ℤ) : ZMod (5 ^ r)) = ((-(n.natAbs : ℤ) : ℤ) : ZMod (5 ^ r)) := congrArg _ hn
    rw [e, Int.cast_neg, Int.cast_natCast]; exact (Erdos634.GA2SD.unit5r r _ h').neg

theorem lemmaN_Z (r : ℕ) (hr : 2 ≤ r) {k : ℕ} (pts : Fin k → ZMod (5 ^ r)) (hu : ∀ i, IsUnit (pts i))
    (c : Fin k → ℂ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (P : Finset (ZMod (5 ^ r)))
    (hP : ∀ i, pts i ∈ P ∧ -pts i ∈ P) (hPc : P.card < 10)
    (horth : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ i, c i * ψ (pts i) = 0) :
    ∀ g : ZMod (5 ^ r), (∑ i, if g = pts i then c i else 0) = -ε * ∑ i, if -g = pts i then c i else 0 := by
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  set Φ : (ZMod (5 ^ r))ˣ → ℂ := fun v => ∑ i, if (v : ZMod (5 ^ r)) = pts i then c i else 0 with hΦ
  have hsum : ∀ ψ : DirichletCharacter ℂ (5 ^ r),
      ∑ v : (ZMod (5 ^ r))ˣ, ψ (v : ZMod (5 ^ r)) * Φ v = ∑ i, c i * ψ (pts i) := by
    intro ψ
    simp only [hΦ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    obtain ⟨u0, hu0⟩ := hu i
    rw [Finset.sum_eq_single u0]
    · rw [if_pos hu0, hu0]; ring
    · intro v _ hne
      rw [if_neg, mul_zero]
      intro hh
      apply hne
      apply Units.ext
      rw [hu0]; exact hh
    · intro h; exact absurd (Finset.mem_univ _) h
  set Pu : Finset (ZMod (5 ^ r))ˣ := Finset.univ.filter (fun v => (v : ZMod (5 ^ r)) ∈ P) with hPu
  have hPuc : Pu.card < 10 := by
    calc Pu.card ≤ P.card :=
          Finset.card_le_card_of_injOn (fun v => (v : ZMod (5 ^ r)))
            (fun v hv => (Finset.mem_filter.1 hv).2) (fun a _ b _ h => Units.ext h)
      _ < 10 := hPc
  have key := Erdos634.GA2QB.top5_zero_small r hr Φ hε
    (fun ψ hψ h1 => by rw [hsum ψ]; exact horth ψ hψ h1) Pu ?_ hPuc
  · intro g
    by_cases hg : IsUnit g
    · obtain ⟨g0, rfl⟩ := hg
      have := key g0
      simp only [hΦ, Units.val_neg] at this
      exact this
    · have h1 : (∑ i, if g = pts i then c i else 0) = 0 :=
        Finset.sum_eq_zero (fun i _ => by
          rw [if_neg]; intro h; exact hg (h ▸ hu i))
      have h2 : (∑ i, if -g = pts i then c i else 0) = 0 :=
        Finset.sum_eq_zero (fun i _ => by
          rw [if_neg]; intro h
          apply hg
          have := (hu i).neg
          rw [← h, neg_neg] at this
          exact this)
      rw [h1, h2]; ring
  · intro v hv
    rw [hPu, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hv with hv | hv
    · obtain ⟨i, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hcond : (v : ZMod (5 ^ r)) = pts i := by
        by_contra hh; rw [if_neg hh] at hne; exact hne rfl
      rw [hcond]; exact (hP i).1
    · obtain ⟨i, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hcond : ((-v : (ZMod (5 ^ r))ˣ) : ZMod (5 ^ r)) = pts i := by
        by_contra hh; rw [if_neg hh] at hne; exact hne rfl
      rw [Units.val_neg] at hcond
      have : (v : ZMod (5 ^ r)) = -pts i := by rw [← hcond]; ring
      rw [this]; exact (hP i).2

theorem lemmaN_lin (r : ℕ) (hr : 2 ≤ r) {u : ZMod (5 ^ r)} (hu : IsUnit u) {k : ℕ} (m : Fin k → ℤ)
    (c : Fin k → ℂ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (P : Finset ℤ)
    (hP : ∀ i, m i ∈ P ∧ -m i ∈ P) (hPc : P.card < 10)
    (hb : ∀ n ∈ P, -12 ≤ n ∧ n ≤ 12) (h5 : ∀ n ∈ P, ¬ (5 : ℤ) ∣ n)
    (horth : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ i, c i * ψ ((m i : ZMod (5 ^ r)) * u) = 0) :
    ∀ n ∈ P, (∑ i, if n = m i then c i else 0) = -ε * ∑ i, if -n = m i then c i else 0 := by
  have hunit : ∀ i, IsUnit ((m i : ZMod (5 ^ r)) * u) := fun i =>
    (unit_int r (m i) (h5 _ (hP i).1)).mul hu
  have key := lemmaN_Z r hr (fun i => (m i : ZMod (5 ^ r)) * u) hunit c hε
    (P.image (fun n : ℤ => (n : ZMod (5 ^ r)) * u))
    (fun i => ⟨Finset.mem_image.2 ⟨m i, (hP i).1, rfl⟩,
      Finset.mem_image.2 ⟨-m i, (hP i).2, by push_cast; ring⟩⟩)
    (lt_of_le_of_lt Finset.card_image_le hPc) horth
  intro n hn
  have := key ((n : ZMod (5 ^ r)) * u)
  have e1 : ∀ i, ((n : ZMod (5 ^ r)) * u = (m i : ZMod (5 ^ r)) * u) ↔ n = m i := by
    intro i
    constructor
    · intro h
      have hi := hb _ (hP i).1
      have hn' := hb n hn
      exact mul_unit_inj r hr hu n (m i) (by omega) (by omega) h
    · intro h; rw [h]
  have e2 : ∀ i, (-((n : ZMod (5 ^ r)) * u) = (m i : ZMod (5 ^ r)) * u) ↔ -n = m i := by
    intro i
    have : -((n : ZMod (5 ^ r)) * u) = ((-n : ℤ) : ZMod (5 ^ r)) * u := by push_cast; ring
    rw [this]
    constructor
    · intro h
      have hi := hb _ (hP i).1
      have hn' := hb n hn
      exact mul_unit_inj r hr hu (-n) (m i) (by omega) (by omega) h
    · intro h; rw [h]
  simp only [e1, e2] at this
  exact this

end Erdos634.GA2WA

#print axioms Erdos634.GA2WA.lemmaN_Z
#print axioms Erdos634.GA2WA.lemmaN_lin
