import Mathlib.Tactic
import Erdos634.Draft.ThmDRunLattice
import Erdos634.Draft.ThmDRunRep
import Erdos634.EdgeChain

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (H2), lattice helpers: points of the diagonal, three-valued sums, unit edges  

* `onL_eq_lp` : a point `z` on the diagonal `GST = -lv s` is `lp (s - eta) eta` with `eta = z_y / hh`;
* `dist_diag` : `dist (lp (s-eta) eta) (lp (s-eta') eta') = |eta - eta'| a`;
* `lp_diag_mem_seg` : the diagonal points between two diagonal points lie on the segment;
* `sum_split3` / `all_len_a` : a sum of edge lengths `in {a,b,c}` equal to `w a`, `w < v`, forces every length `a`.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set

section lat
variable {u v : ℝ}

theorem onL_eq_lp {ε x s : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) {z : Plane}
    (hz : GST u v ε z = -lvT u v ε x s) :
    z = lpT u v ε x (s - z 1 / hhT u v) (z 1 / hhT u v) := by
  have hh := hhT_pos hu huv hv
  unfold GST lvT at hz
  rw [lin_apply] at hz
  apply plane_ext
  · unfold lpT
    rw [mkPt_zero]
    have e1 : z 1 / hhT u v * hhT u v = z 1 := by field_simp
    have key : ε * hhT u v * z 0 = ε * hhT u v * x + (u * v) * hhT u v * s - uuT u v * z 1 := by linarith
    have hε' : ε * ε = 1 := by nlinarith [hε]
    have : z 0 = ε * (ε * hhT u v * x + (u * v) * hhT u v * s - uuT u v * z 1) / hhT u v := by
      field_simp
      linear_combination (hhT u v * z 0) * (-hε') + ε * key
    rw [this]
    field_simp
    linear_combination (hhT u v * x) * hε'
  · unfold lpT
    rw [mkPt_one]
    field_simp

theorem lp_snd_eq {ε x ξ η : ℝ} : (lpT u v ε x ξ η) 1 = η * hhT u v := by
  unfold lpT; rw [mkPt_one]

theorem dist_diag {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (s η η' : ℝ) :
    dist (lpT u v ε x (s - η) η) (lpT u v ε x (s - η') η') = |η - η'| * u ^ 2 := by
  refine dist_lpT hu huv hv hε (mul_nonneg (abs_nonneg _) (sq_nonneg u)) ?_
  have h2 : (|η - η'| * u ^ 2) ^ 2 = (η - η') ^ 2 * u ^ 4 := by rw [mul_pow, sq_abs]; ring
  unfold QfT
  rw [h2]
  ring

/-- the diagonal point at height `eta` between two diagonal points -/
theorem lp_diag_mem_seg {ε x s η₁ η₂ η : ℝ} (h12 : η₁ ≠ η₂) (hη : min η₁ η₂ ≤ η) (hη' : η ≤ max η₁ η₂) :
    lpT u v ε x (s - η) η ∈ segment ℝ (lpT u v ε x (s - η₁) η₁) (lpT u v ε x (s - η₂) η₂) := by
  have hd : η₂ - η₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have hτ : 0 ≤ (η - η₁) / (η₂ - η₁) ∧ (η - η₁) / (η₂ - η₁) ≤ 1 := by
    rcases lt_or_gt_of_ne h12 with h | h
    · rw [min_eq_left h.le] at hη
      rw [max_eq_right h.le] at hη'
      have hpos : 0 < η₂ - η₁ := by linarith
      exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩
    · rw [min_eq_right h.le] at hη
      rw [max_eq_left h.le] at hη'
      have hneg : η₂ - η₁ < 0 := by linarith
      exact ⟨div_nonneg_of_nonpos (by linarith) hneg.le, (div_le_one_of_neg hneg).mpr (by linarith)⟩
  have h := lp_mem_segT (u := u) (v := v) (ε := ε) (x := x) (ξ := s - η₁) (η := η₁) (ξ' := s - η₂) (η' := η₂)
    (τ := (η - η₁) / (η₂ - η₁)) hτ.1 hτ.2
  have e1 : s - η₁ + (η - η₁) / (η₂ - η₁) * (s - η₂ - (s - η₁)) = s - η := by
    field_simp; ring
  have e2 : η₁ + (η - η₁) / (η₂ - η₁) * (η₂ - η₁) = η := by field_simp; ring
  rw [e1, e2] at h; exact h

/-- conversely every point of a diagonal segment is a diagonal point at an intermediate height -/
theorem diag_seg_param {ε x s η₁ η₂ : ℝ} {y : Plane}
    (hy : y ∈ segment ℝ (lpT u v ε x (s - η₁) η₁) (lpT u v ε x (s - η₂) η₂)) :
    ∃ η, min η₁ η₂ ≤ η ∧ η ≤ max η₁ η₂ ∧ y = lpT u v ε x (s - η) η := by
  obtain ⟨τ, h0, h1, rfl⟩ := lp_seg_paramT hy
  refine ⟨η₁ + τ * (η₂ - η₁), ?_, ?_, lpT_congr (by ring) rfl⟩
  · rcases le_total η₁ η₂ with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total η₁ η₂ with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

end lat

/-! ### Three-valued sums -/

theorem sum_split3 {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ P Q R : ℕ, ((P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = ∑ e ∈ s, len e) ∧
      (Q = 0 → R = 0 → ∀ e ∈ s, len e = a) := by
  classical
  refine ⟨(s.filter fun e => len e = a).card,
          (s.filter fun e => ¬ len e = a ∧ len e = b).card,
          (s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card, ?_, ?_⟩
  · have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (s.filter fun e => ¬ len e = a) (fun e => len e = b) len
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
    have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
        = ((s.filter fun e => len e = a).card : ℝ) * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
    have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ len e = b).card : ℝ) * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2),
        Finset.sum_const, nsmul_eq_mul]
    have hC : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      have hmem := Finset.mem_filter.mp he
      rcases h e hmem.1 with h' | h' | h'
      · exact absurd h' hmem.2.1
      · exact absurd h' hmem.2.2
      · exact h'
    rw [hA] at hsplit1
    rw [hB, hC] at hsplit2
    linarith [hsplit1, hsplit2]
  · intro hQ hR e he
    by_contra hne
    by_cases hb : len e = b
    · have : e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b) := Finset.mem_filter.mpr ⟨he, hne, hb⟩
      rw [Finset.card_eq_zero] at hQ
      rw [hQ] at this; simp at this
    · have : e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b) := Finset.mem_filter.mpr ⟨he, hne, hb⟩
      rw [Finset.card_eq_zero] at hR
      rw [hR] at this; simp at this

/-- **Rigidity window `v` for the diagonal:** edge lengths in `{a,b,c}` summing to `w a`, `w < v`, are all `a`. -/
theorem all_len_a {ι : Type*} (s : Finset ι) (len : ι → ℝ) {u v : ℕ} (hcop : Nat.Coprime u v) (hu : 0 < u)
    (huv : u < v) (w : ℕ) (hw : w < v)
    (h : ∀ e ∈ s, len e = (u : ℝ) ^ 2 ∨ len e = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∨ len e = (u : ℝ) * v)
    (hsum : ∑ e ∈ s, len e = (w : ℝ) * (u : ℝ) ^ 2) : ∀ e ∈ s, len e = (u : ℝ) ^ 2 := by
  obtain ⟨P, Q, R, hPQR, hall⟩ := sum_split3 s len _ _ _ h
  have := chord_a hcop hu huv hw (x := P) (y := Q) (z := R) (j := w) (by rw [hPQR, hsum])
  exact hall this.2.1 this.2.2

#print axioms all_len_a
end Erdos634.Draft.ThmDRun
