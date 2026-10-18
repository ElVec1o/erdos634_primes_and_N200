import Mathlib.Tactic

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (H2): a covering of `[0, w]` by unit intervals with disjoint interiors is the integer tiling  

Pure real analysis, no geometry.  `lo j` are the left ends of closed unit intervals `[lo j, lo j + 1]` inside `[0, w]`,
pairwise at distance `>= 1` (interiors disjoint), covering `[0, w]` outside a finite set `F`.  Then every integer
`m < w` is a left end.  Used for the far-side edge chain of a diagonal `PQ` (all edges have length `a`, by the rigidity
window `v`): the far edges are the lattice `a`-edges `e_i`.
-/

namespace Erdos634.Draft.ThmDRowIntervals

/-- the step: if no interval starts below `m` and reaches above `m`, some interval starts exactly at `m`. -/
theorem exists_start {ι : Type*} [Fintype ι] (lo : ι → ℝ) (w m : ℕ) (hm : m < w)
    (hrng : ∀ j, 0 ≤ lo j ∧ lo j + 1 ≤ w)
    (F : Set ℝ) (hF : F.Finite)
    (hcov : ∀ t : ℝ, 0 < t → t < w → t ∉ F → ∃ j, lo j ≤ t ∧ t ≤ lo j + 1)
    (hlow : ∀ j, lo j < m → lo j + 1 ≤ m) : ∃ j, lo j = m := by
  classical
  have hmw : (m : ℝ) < w := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- B nonempty
  have hB : (Finset.univ.filter (fun j => (m : ℝ) ≤ lo j)).Nonempty := by
    obtain ⟨t, ht, htF⟩ := (((Set.Ioo_infinite hmw).diff hF)).nonempty
    obtain ⟨j, hj1, hj2⟩ := hcov t (by linarith [ht.1]) ht.2 htF
    refine ⟨j, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hlt
    push_neg at hlt
    have := hlow j hlt
    linarith [ht.1]
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image _ lo hB
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj0 hmin
  refine ⟨j0, ?_⟩
  by_contra hne
  have hgt : (m : ℝ) < lo j0 := lt_of_le_of_ne hj0 (Ne.symm hne)
  have hj0r := hrng j0
  obtain ⟨t, ht, htF⟩ := (((Set.Ioo_infinite hgt).diff hF)).nonempty
  obtain ⟨j, hj1, hj2⟩ := hcov t (by linarith [ht.1]) (by linarith [ht.2]) htF
  by_cases hjB : (m : ℝ) ≤ lo j
  · have := hmin j hjB
    linarith [ht.2]
  · push_neg at hjB
    have := hlow j hjB
    linarith [ht.1]

/-- **Unit intervals tiling `[0,w]` start at every integer.** -/
theorem interval_tiling {ι : Type*} [Fintype ι] (lo : ι → ℝ) (w : ℕ)
    (hsep : ∀ j j', j ≠ j' → 1 ≤ |lo j - lo j'|)
    (hrng : ∀ j, 0 ≤ lo j ∧ lo j + 1 ≤ w)
    (F : Set ℝ) (hF : F.Finite)
    (hcov : ∀ t : ℝ, 0 < t → t < w → t ∉ F → ∃ j, lo j ≤ t ∧ t ≤ lo j + 1) :
    ∀ m : ℕ, m < w → ∃ j, lo j = m := by
  intro m
  induction m with
  | zero =>
    intro hm
    refine exists_start lo w 0 hm hrng F hF hcov ?_
    intro j hj
    have := (hrng j).1
    simp at hj
    linarith
  | succ i ih =>
    intro hm
    obtain ⟨ji, hji⟩ := ih (by omega)
    refine exists_start lo w (i + 1) hm hrng F hF hcov ?_
    intro j hj
    push_cast at hj ⊢
    by_cases hjj : j = ji
    · subst hjj; linarith
    · have h := hsep j ji hjj
      rw [hji] at h
      rcases le_abs'.mp h with h1 | h1
      · linarith
      · linarith

#print axioms interval_tiling

/-! ### The counting form: `w` unit intervals with disjoint interiors in `[0,w]` start at every integer -/

/-- points of a finset of unit-separated reals in `[0,t]` number at most `t + 1` -/
theorem card_le_of_sep {ι : Type*} [DecidableEq ι] (lo : ι → ℝ)
    (hsep : ∀ j j', j ≠ j' → 1 ≤ |lo j - lo j'|) :
    ∀ (n : ℕ) (S : Finset ι), S.card = n → ∀ t : ℝ, -1 ≤ t → (∀ j ∈ S, 0 ≤ lo j ∧ lo j ≤ t) →
      (S.card : ℝ) ≤ t + 1 := by
  intro n
  induction n with
  | zero => intro S hS t h1 ht; rw [hS]; simp; linarith
  | succ k ih =>
    intro S hS t h1 ht
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S lo hne
    have hcard : (S.erase m).card = k := by rw [Finset.card_erase_of_mem hm]; omega
    have hle : ∀ j ∈ S.erase m, 0 ≤ lo j ∧ lo j ≤ lo m - 1 := by
      intro j hj
      have hjm := Finset.mem_erase.mp hj
      refine ⟨(ht j hjm.2).1, ?_⟩
      have h1 := hsep j m hjm.1
      have h2 := hmax j hjm.2
      rcases le_abs'.mp h1 with h | h <;> linarith
    have := ih (S.erase m) hcard (lo m - 1) (by linarith [(ht m hm).1]) hle
    rw [hS]; push_cast
    rw [hcard] at this
    have := (ht m hm).2
    linarith

/-- the mirror image: points in `[t, w-1]` -/
theorem card_le_of_sep' {ι : Type*} [DecidableEq ι] (lo : ι → ℝ) (w : ℝ)
    (hsep : ∀ j j', j ≠ j' → 1 ≤ |lo j - lo j'|) (S : Finset ι) (t : ℝ) (ht1 : t ≤ w)
    (ht : ∀ j ∈ S, t ≤ lo j ∧ lo j ≤ w - 1) : (S.card : ℝ) ≤ w - t := by
  have := card_le_of_sep (fun j => (w - 1) - lo j) (fun j j' h => by
    have := hsep j j' h
    rw [show (w - 1 - lo j) - (w - 1 - lo j') = -(lo j - lo j') by ring, abs_neg]; exact this)
    S.card S rfl ((w - 1) - t) (by linarith) (fun j hj => ⟨by linarith [(ht j hj).2], by linarith [(ht j hj).1]⟩)
  linarith

/-- **`w` unit intervals with disjoint interiors in `[0,w]` start at every integer.** -/
theorem interval_tiling_card {ι : Type*} [Fintype ι] (lo : ι → ℝ) (w : ℕ) (hcard : Fintype.card ι = w)
    (hsep : ∀ j j', j ≠ j' → 1 ≤ |lo j - lo j'|)
    (hrng : ∀ j, 0 ≤ lo j ∧ lo j + 1 ≤ w) : ∀ m : ℕ, m < w → ∃ j, lo j = m := by
  classical
  -- rank of `j`
  set rank : ι → ℕ := fun j => (Finset.univ.filter (fun j' => lo j' < lo j)).card with hrank
  have hlow : ∀ j, (rank j : ℝ) ≤ lo j := by
    intro j
    have := card_le_of_sep lo hsep _ (insert j (Finset.univ.filter (fun j' => lo j' < lo j))) rfl (lo j)
      (by linarith [(hrng j).1]) (by
        intro j' hj'
        rcases Finset.mem_insert.mp hj' with h | h
        · rw [h]; exact ⟨(hrng j).1, le_rfl⟩
        · exact ⟨(hrng j').1, (Finset.mem_filter.mp h).2.le⟩)
    rw [Finset.card_insert_of_notMem (by simp)] at this
    push_cast at this
    simp only [hrank]; linarith
  have hhigh : ∀ j, lo j ≤ (rank j : ℝ) := by
    intro j
    have hS : (insert j (Finset.univ.filter (fun j' => lo j < lo j'))).card ≤ w - lo j := by
      have := card_le_of_sep' lo (w : ℝ) hsep (insert j (Finset.univ.filter (fun j' => lo j < lo j'))) (lo j)
        (by linarith [(hrng j).2]) (by
          intro j' hj'
          rcases Finset.mem_insert.mp hj' with h | h
          · rw [h]; exact ⟨le_rfl, by linarith [(hrng j).2]⟩
          · exact ⟨(Finset.mem_filter.mp h).2.le, by linarith [(hrng j').2]⟩)
      exact this
    -- total count
    have htot : (Finset.univ.filter (fun j' => lo j' < lo j)).card + 1 +
        (Finset.univ.filter (fun j' => lo j < lo j')).card = w := by
      have heq : Finset.univ.filter (fun j' => ¬ lo j' < lo j) =
          insert j (Finset.univ.filter (fun j' => lo j < lo j')) := by
        ext j'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_lt]
        constructor
        · intro h
          by_cases hj : j' = j
          · left; exact hj
          · right
            have := hsep j' j hj
            rcases le_abs'.mp this with h2 | h2 <;> linarith
        · rintro (h | h)
          · rw [h]
          · exact h.le
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset ι))
        (fun j' => lo j' < lo j)
      rw [heq, Finset.card_insert_of_notMem (by simp), Finset.card_univ, hcard] at this
      omega
    rw [Finset.card_insert_of_notMem (by simp)] at hS
    push_cast at hS
    have : ((rank j : ℕ) : ℝ) + 1 + ((Finset.univ.filter (fun j' => lo j < lo j')).card : ℝ) = w := by
      simp only [hrank]; exact_mod_cast htot
    linarith
  have hrk : ∀ j, lo j = (rank j : ℝ) := fun j => le_antisymm (hhigh j) (hlow j)
  have hinj : Function.Injective rank := by
    intro j j' h
    by_contra hne
    have := hsep j j' hne
    rw [hrk j, hrk j', h] at this
    simp only [sub_self, abs_zero] at this
    linarith
  have hlt : ∀ j, rank j < w := by
    intro j
    have := (hrng j).2
    rw [hrk j] at this
    have : (rank j : ℝ) < w := by linarith
    exact_mod_cast this
  -- rank is a bijection onto `Fin w`
  let f : ι → Fin w := fun j => ⟨rank j, hlt j⟩
  have hfinj : Function.Injective f := fun j j' h => hinj (by simpa [f] using congrArg Fin.val h)
  have hfbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hfinj, by simp [hcard]⟩
  intro m hm
  obtain ⟨j, hj⟩ := hfbij.2 ⟨m, hm⟩
  refine ⟨j, ?_⟩
  rw [hrk j]
  have := congrArg Fin.val hj
  simp only [f] at this
  rw [this]

#print axioms interval_tiling_card

end Erdos634.Draft.ThmDRowIntervals
