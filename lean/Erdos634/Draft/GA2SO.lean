/-
GA2S, atom O: the 5-adic PATTERN step, per character (the T-rows of Prop K-c, r >= 2).

`five_pattern`: u, v units mod 5^r, kappa != 0, eps = +-1, c = 0 or -u-v a unit, at most four nonzero tokens (a = 0 or b = 0 or c = 0).
If for every primitive psi mod 5^r of parity eps
    a (psi(2u) - kappa psi(u)) + b (psi(2v) - kappa psi(v)) + c psi(-u-v) = 0,
then the pattern conclusion `GA2QP.Concl u v eps a b c` holds:  (a = b = c = 0) or (v = u, b = -a, c = 0) or (v = -u, c = 0, b = -eps a).
Proof: `GA2SJ.pointwise5_small` (Lemma N at 5, |N_5| = 5 > 4 tokens) turns the orthogonality into Phi + eps [-1] Phi = 0 on units;
off the units Phi vanishes; then `GA2QP.pattern_lemma` (M = 5^r >= 25).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SJ
import Erdos634.Draft.GA2QP

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SO

open DirichletCharacter Erdos634.GA2PC
open Erdos634.GA2QP (Fp Fq Concl pattern_lemma two_unit)
open Erdos634.GA2SJ (pointwise5_small)

theorem half_unit (r : ℕ) : IsUnit (2 : ZMod (5 ^ r)) := by
  have hodd : (5 ^ r) % 2 = 1 := by
    have : Odd (5 ^ r) := Odd.pow (by decide)
    exact Nat.odd_iff.1 this
  exact two_unit hodd

theorem Fp_nonunit {M : ℕ} {u v : ZMod M} (hu : IsUnit u) (hv : IsUnit v) (h2 : IsUnit (2 : ZMod M))
    {κ a b c : ℂ} (hc : c = 0 ∨ IsUnit (-u - v)) {g : ZMod M} (hg : ¬ IsUnit g) :
    Fp u v κ a b c g = 0 := by
  have n1 : g ≠ 2 * u := fun h => hg (h ▸ h2.mul hu)
  have n2 : g ≠ u := fun h => hg (h ▸ hu)
  have n3 : g ≠ 2 * v := fun h => hg (h ▸ h2.mul hv)
  have n4 : g ≠ v := fun h => hg (h ▸ hv)
  unfold Fp Fq
  rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4]
  rcases hc with rfl | hc
  · simp
  · have n5 : g ≠ -u - v := fun h => hg (h ▸ hc)
    rw [if_neg n5]; simp

theorem ite_helper (P : Prop) [Decidable P] (a : ℂ) :
    (if P then a else 0) = a * (if P then 1 else 0) := by split_ifs <;> ring

theorem ite_neg_helper (P : Prop) [Decidable P] (κ a : ℂ) :
    (if P then -κ * a else 0) = -(a * (κ * (if P then 1 else 0))) := by split_ifs <;> ring

theorem five_pattern (r : ℕ) (hr : 2 ≤ r) {u v : ZMod (5 ^ r)} (hu : IsUnit u) (hv : IsUnit v)
    {κ ε a b c : ℂ} (hκ : κ ≠ 0) (hε : ε = 1 ∨ ε = -1) (hc : c = 0 ∨ IsUnit (-u - v))
    (h4 : a = 0 ∨ b = 0 ∨ c = 0)
    (horth : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      a * (ψ (2 * u) - κ * ψ u) + b * (ψ (2 * v) - κ * ψ v) + c * ψ (-u - v) = 0) :
    Concl u v ε a b c := by
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hodd : (5 ^ r) % 2 = 1 := by
    have : Odd (5 ^ r) := Odd.pow (by decide)
    exact Nat.odd_iff.1 this
  have hM : 13 ≤ 5 ^ r := by
    calc 13 ≤ 5 ^ 2 := by norm_num
      _ ≤ 5 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have h2 : IsUnit (2 : ZMod (5 ^ r)) := half_unit r
  refine pattern_lemma hM hodd hu hv hκ hε hc ?_
  set ptsZ : Fin 5 → ZMod (5 ^ r) := ![2 * u, u, 2 * v, v, -u - v] with hptsZ
  set pts : Fin 5 → ℕ := fun t => (ptsZ t).val with hpts
  set wts : Fin 5 → ℂ := ![a, -κ * a, b, -κ * b, c] with hwts
  set V : Finset (Fin 5) := univ.filter (fun t => wts t ≠ 0) with hV
  have hcast : ∀ t, ((pts t : ℕ) : ZMod (5 ^ r)) = ptsZ t := fun t => ZMod.natCast_zmod_val _
  have hVunit : ∀ t ∈ V, IsUnit ((pts t : ℕ) : ZMod (5 ^ r)) := by
    intro t ht
    have hw : wts t ≠ 0 := (Finset.mem_filter.1 ht).2
    rw [hcast]
    fin_cases t
    · exact h2.mul hu
    · exact hu
    · exact h2.mul hv
    · exact hv
    · rcases hc with h | h
      · exfalso; apply hw; simp [hwts, h]
      · exact h
  have hVcard : V.card ≤ 4 := by
    rcases h4 with h | h | h
    · have hsub : V ⊆ {2, 3, 4} := by
        intro t ht
        have hw : wts t ≠ 0 := (Finset.mem_filter.1 ht).2
        fin_cases t
        · exfalso; apply hw; simp [hwts, h]
        · exfalso; apply hw; simp [hwts, h]
        · simp
        · simp
        · simp
      exact (Finset.card_le_card hsub).trans (by decide)
    · have hsub : V ⊆ {0, 1, 4} := by
        intro t ht
        have hw : wts t ≠ 0 := (Finset.mem_filter.1 ht).2
        fin_cases t
        · simp
        · simp
        · exfalso; apply hw; simp [hwts, h]
        · exfalso; apply hw; simp [hwts, h]
        · simp
      exact (Finset.card_le_card hsub).trans (by decide)
    · have hsub : V ⊆ {0, 1, 2, 3} := by
        intro t ht
        have hw : wts t ≠ 0 := (Finset.mem_filter.1 ht).2
        fin_cases t
        · simp
        · simp
        · simp
        · simp
        · exfalso; apply hw; simp [hwts, h]
      exact (Finset.card_le_card hsub).trans (by decide)
  have hsumV : ∀ f : Fin 5 → ℂ, (∀ t, wts t = 0 → f t = 0) →
      ∑ t ∈ V, f t = ∑ t, f t := by
    intro f hf
    rw [hV]
    refine Finset.sum_filter_of_ne (fun t _ hne => ?_)
    intro hw
    exact hne (hf t hw)
  have horthV : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ t ∈ V, wts t * ψ ((pts t : ℕ) : ZMod (5 ^ r)) = 0 := by
    intro ψ hψ h1
    rw [hsumV (fun t => wts t * ψ ((pts t : ℕ) : ZMod (5 ^ r))) (fun t ht => by show wts t * _ = 0; rw [ht, zero_mul]),
      Fin.sum_univ_five]
    simp only [hcast, hwts, hptsZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    have := horth ψ hψ h1
    linear_combination this
  have hpt := pointwise5_small r hr pts wts V hVcard hVunit hε horthV
  have hPhi : ∀ g : (ZMod (5 ^ r))ˣ, PhiV (5 ^ r) pts wts V g = Fp u v κ a b c (g : ZMod (5 ^ r)) := by
    intro g
    unfold PhiV
    rw [hsumV (fun t => if (g : ZMod (5 ^ r)) = ((pts t : ℕ) : ZMod (5 ^ r)) then wts t else 0)
      (fun t ht => by show (if _ = _ then wts t else 0) = 0; rw [ht]; simp), Fin.sum_univ_five]
    simp only [hcast, hwts, hptsZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    rw [ite_helper _ a, ite_neg_helper _ κ a, ite_helper _ b, ite_neg_helper _ κ b, ite_helper _ c]
    unfold Fp Fq
    ring
  intro g
  by_cases hg : IsUnit g
  · obtain ⟨g0, rfl⟩ := hg
    have := hpt g0
    rw [hPhi, hPhi] at this
    rw [Units.val_neg] at this
    exact this
  · rw [Fp_nonunit hu hv h2 hc hg, Fp_nonunit hu hv h2 hc (fun h => hg (by simpa using h))]
    ring

theorem concl_a0 {M : ℕ} {u v : ZMod M} {ε b c : ℂ} (h : Concl u v ε 0 b c) : b = 0 ∧ c = 0 := by
  rcases h with ⟨_, h2, h3⟩ | ⟨_, h2, h3⟩ | ⟨_, h3, h2⟩
  · exact ⟨h2, h3⟩
  · exact ⟨by simpa using h2, h3⟩
  · exact ⟨by simpa using h2, h3⟩

theorem concl_bc0 {M : ℕ} {u v : ZMod M} {ε a : ℂ} (hε : ε = 1 ∨ ε = -1) (h : Concl u v ε a 0 0) : a = 0 := by
  rcases h with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h2⟩
  · exact h1
  · have : -a = 0 := by simpa using h2
    simpa using this
  · have h3 : ε * a = 0 := by linear_combination h2
    rcases hε with rfl | rfl
    · simpa using h3
    · simpa using h3

end Erdos634.GA2SO

#print axioms Erdos634.GA2SO.five_pattern
#print axioms Erdos634.GA2SO.concl_a0
#print axioms Erdos634.GA2SO.concl_bc0
