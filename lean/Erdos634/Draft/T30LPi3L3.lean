import Mathlib.Tactic
import Erdos634.Draft.T30LPi3Corner

/-!
# Edge counts (not only sums) on the far chain

* `letter_counts`: for edges with lengths in `{a,b,c}` the length sum is `x a + y b + z c` with `x,y,z` the cardinalities
  of the three (first-match) classes of edges.
* `far_chain_counts`: on a `CongruentDissection`, a chord clamped as in `ChordFar.chord_far_sum_cong` of length `L`, sides among
  `s0,s1,s2`, and the word lemma `x s0+y s1+z s2 = L → (x,y,z) = (x0,y0,z0)`: the far chain has exactly `x0` edges of length `s0`,
  `y0` of the second class (length `s1 ≠ s0`), `z0` of the third class.
* `t30_L3_far_two_c`: the instance `L = 2c = 24`: the far chain is exactly two edges, both of length `c`
  (`ChordWord.chord_2c`).
* Witness: `wall_far_counts` (real 2-tile `wallCongruentDissection`, sides (√2,5,2) as the letter list, chord `√2`):
  counts `(1,0,0)`. Control: `word_not_unique_345` (tile 3,4,5, `L = 12`: `(4,0,0)` and `(0,3,0)`, so the word hypothesis fails).
* Not proved here: a real-dissection witness with count 2 (this needs a chord of length `2·side` on a real tiling); that the first
  of the two `c`-edges has its end at `P₂` with angle `α` and the next tile has `P` there (this needs the fan order).
-/

namespace Erdos634.Pi3L3

open Erdos634.Geometry Erdos634.EdgeWordConversion Erdos634.ChordFar Erdos634.ChordWord Erdos634.Pi3Corner

theorem letter_counts {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) (a b c : ℝ)
    (h : ∀ i ∈ s, g i = a ∨ g i = b ∨ g i = c) :
    ∑ i ∈ s, g i = ((s.filter (fun i => g i = a)).card : ℝ) * a
      + ((s.filter (fun i => g i ≠ a ∧ g i = b)).card : ℝ) * b
      + ((s.filter (fun i => g i ≠ a ∧ g i ≠ b)).card : ℝ) * c := by
  classical
  have key : ∀ i ∈ s, g i = (if g i = a then a else 0) + (if g i ≠ a ∧ g i = b then b else 0)
      + (if g i ≠ a ∧ g i ≠ b then c else 0) := by
    intro i hi
    by_cases hA : g i = a
    · rw [if_pos hA, if_neg (fun h => h.1 hA), if_neg (fun h => h.1 hA)]; linarith
    · by_cases hB : g i = b
      · rw [if_neg hA, if_pos ⟨hA, hB⟩, if_neg (fun h => h.2 hB)]; linarith
      · have hC : g i = c := by
          rcases h i hi with h1 | h1 | h1
          · exact absurd h1 hA
          · exact absurd h1 hB
          · exact h1
        rw [if_neg hA, if_neg (fun h => hB h.2), if_pos ⟨hA, hB⟩]; linarith
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e : ∀ (p : ι → Prop) [DecidablePred p] (k : ℝ),
      ∑ i ∈ s, (if p i then k else 0) = ((s.filter p).card : ℝ) * k := by
    intro p _ k
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [e, e, e]

/-- **Edge counts on the far chain of a chord.** -/
theorem far_chain_counts {N : ℕ} (D : CongruentDissection N) {s0 s1 s2 L : ℝ} {x0 y0 z0 : ℕ}
    (hsides : ∀ i : Fin 3, sideLen D i = s0 ∨ sideLen D i = s1 ∨ sideLen D i = s2)
    (hword : ∀ x y z : ℕ, (x : ℝ) * s0 + y * s1 + z * s2 = L → x = x0 ∧ y = y0 ∧ z = z0)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = L) :
    let len : Fin N × Fin 3 → ℝ := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
    ((D.lineChain (-f) (-c)).filter (fun e => len e = s0)).card = x0 ∧
    ((D.lineChain (-f) (-c)).filter (fun e => len e ≠ s0 ∧ len e = s1)).card = y0 ∧
    ((D.lineChain (-f) (-c)).filter (fun e => len e ≠ s0 ∧ len e ≠ s1)).card = z0 := by
  intro len
  have hsum := chord_far_sum_cong D f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall
  rw [hdist] at hsum
  have hmem : ∀ e ∈ D.lineChain (-f) (-c), len e = s0 ∨ len e = s1 ∨ len e = s2 := by
    intro e _
    rcases edge_length_trichotomy D e.1 e.2 with h' | h' | h'
    · simp only [len]; rw [h']; exact hsides 0
    · simp only [len]; rw [h']; exact hsides 1
    · simp only [len]; rw [h']; exact hsides 2
  have hc := letter_counts (D.lineChain (-f) (-c)) len s0 s1 s2 hmem
  exact hword _ _ _ (by rw [← hc]; exact hsum)

theorem sc_ne_sa : sc ≠ sa := by
  intro h
  apply sqrt21_irrational
  refine ⟨3, ?_⟩
  unfold sc sa at h; push_cast; linarith

theorem sc_ne_sb : sc ≠ sb := by
  intro h
  apply sqrt21_irrational
  refine ⟨-3, ?_⟩
  unfold sc sb at h; push_cast; linarith

/-- **T30 L3, far side.**  If the chord has length `2c = 24`, the far chain is exactly two edges, both of length `c`. -/
theorem t30_L3_far_two_c {N : ℕ} (D : CongruentDissection N)
    (hsides : ∀ i : Fin 3, sideLen D i = sa ∨ sideLen D i = sb ∨ sideLen D i = sc)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = 2 * sc) :
    ∃ e₁ e₂, e₁ ≠ e₂ ∧ D.lineChain (-f) (-c) = {e₁, e₂} ∧
      dist ((D.tile e₁.1).pts e₁.2) ((D.tile e₁.1).pts (e₁.2 + 1)) = sc ∧
      dist ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) = sc := by
  have hcnt := far_chain_counts D (x0 := 0) (y0 := 0) (z0 := 2) hsides
    (fun x y z hxyz => by
      have := chord_2c x y z (by unfold wordLen; exact hxyz)
      omega)
    f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall hdist
  obtain ⟨h1, h2, h3⟩ := hcnt
  simp only at h1 h2 h3
  have hmem : ∀ e ∈ D.lineChain (-f) (-c),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = sc := by
    intro e he
    have n1 : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ sa := by
      intro hh1
      have : e ∈ (D.lineChain (-f) (-c)).filter (fun e => dist ((D.tile e.1).pts e.2)
          ((D.tile e.1).pts (e.2 + 1)) = sa) := Finset.mem_filter.mpr ⟨he, hh1⟩
      rw [Finset.card_eq_zero.mp h1] at this; simp at this
    have n2 : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ sb := by
      intro hh1
      have : e ∈ (D.lineChain (-f) (-c)).filter (fun e => dist ((D.tile e.1).pts e.2)
          ((D.tile e.1).pts (e.2 + 1)) ≠ sa ∧ dist ((D.tile e.1).pts e.2)
          ((D.tile e.1).pts (e.2 + 1)) = sb) := Finset.mem_filter.mpr ⟨he, n1, hh1⟩
      rw [Finset.card_eq_zero.mp h2] at this; simp at this
    rcases edge_length_trichotomy D e.1 e.2 with h' | h' | h'
    · rw [h'] at n1 n2 ⊢
      rcases hsides 0 with h'' | h'' | h'' <;> first | exact absurd h'' n1 | exact absurd h'' n2 | exact h''
    · rw [h'] at n1 n2 ⊢
      rcases hsides 1 with h'' | h'' | h'' <;> first | exact absurd h'' n1 | exact absurd h'' n2 | exact h''
    · rw [h'] at n1 n2 ⊢
      rcases hsides 2 with h'' | h'' | h'' <;> first | exact absurd h'' n1 | exact absurd h'' n2 | exact h''
  have hcard : (D.lineChain (-f) (-c)).card = 2 := by
    have : (D.lineChain (-f) (-c)).filter (fun e => dist ((D.tile e.1).pts e.2)
        ((D.tile e.1).pts (e.2 + 1)) ≠ sa ∧ dist ((D.tile e.1).pts e.2)
        ((D.tile e.1).pts (e.2 + 1)) ≠ sb) = D.lineChain (-f) (-c) := by
      apply Finset.filter_true_of_mem
      intro e he
      rw [hmem e he]
      exact ⟨sc_ne_sa, sc_ne_sb⟩
    rw [← this]; exact h3
  obtain ⟨e₁, e₂, hne, he⟩ := Finset.card_eq_two.mp hcard
  exact ⟨e₁, e₂, hne, he, hmem e₁ (by rw [he]; simp), hmem e₂ (by rw [he]; simp)⟩

section witness

open Erdos634.TPErdos Erdos634.CertCoord

theorem hword_wall (x y z : ℕ)
    (h : (x : ℝ) * Real.sqrt 2 + y * 5 + z * 2 = Real.sqrt 2) : x = 1 ∧ y = 0 ∧ z = 0 := by
  have hs := irrational_sqrt_two
  have h1 : (((x : ℤ) - 1 : ℤ) : ℝ) * Real.sqrt 2 = -(5 * y + 2 * z) := by push_cast; linarith
  have hx : (x : ℤ) - 1 = 0 := by
    by_contra hne
    apply hs
    refine ⟨(-(5 * (y : ℚ) + 2 * z)) / (((x : ℤ) - 1 : ℤ) : ℚ), ?_⟩
    have hm : (((x : ℤ) - 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
    push_cast at hm h1 ⊢
    field_simp
    linarith
  have h0 : (((x : ℤ) - 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hx
  rw [h0] at h1
  have hy : (y : ℝ) = 0 := by
    have := (Nat.cast_nonneg y : (0:ℝ) ≤ y); have := (Nat.cast_nonneg z : (0:ℝ) ≤ z); nlinarith
  have hz : (z : ℝ) = 0 := by
    have := (Nat.cast_nonneg y : (0:ℝ) ≤ y); have := (Nat.cast_nonneg z : (0:ℝ) ≤ z); nlinarith
  refine ⟨by omega, by exact_mod_cast hy, by exact_mod_cast hz⟩

/-- **WITNESS (real dissection).**  On the 2-tile wall dissection, the far chain of the median chord has exactly one edge of
length `√2` and none of the other classes: the count hypothesis/conclusion shape of `far_chain_counts` on real tiles. -/
theorem wall_far_counts :
    let D := wallCongruentDissection
    let len : Fin 2 × Fin 3 → ℝ := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
    ((D.lineChain (-wallF) (-0)).filter (fun e => len e = Real.sqrt 2)).card = 1 ∧
    ((D.lineChain (-wallF) (-0)).filter (fun e => len e ≠ Real.sqrt 2 ∧ len e = 5)).card = 0 ∧
    ((D.lineChain (-wallF) (-0)).filter (fun e => len e ≠ Real.sqrt 2 ∧ len e ≠ 5)).card = 0 :=
  far_chain_counts (wallCongruentDissection) (s0 := Real.sqrt 2) (s1 := 5) (s2 := 2) (x0 := 1) (y0 := 0) (z0 := 0)
    (fun i => by
      rcases wall_sideLen_cases i with h | h | h
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr (Or.inr h))
    hword_wall
    wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num) wall_hint wall_hwall wall_dist_uv

/-- **Control.**  Without the unique-word hypothesis the counts are not determined: on the rational tile `(3,4,5)` the length
`12` has the words `(4,0,0)` and `(0,3,0)`. -/
theorem word_not_unique_345 :
    ∃ x y z x' y' z' : ℕ, (x : ℝ) * 3 + y * 4 + z * 5 = 12 ∧ (x' : ℝ) * 3 + y' * 4 + z' * 5 = 12 ∧
      (x, y, z) ≠ (x', y', z') :=
  ⟨4, 0, 0, 0, 3, 0, by norm_num, by norm_num, by decide⟩

end witness

#print axioms letter_counts
#print axioms far_chain_counts
#print axioms t30_L3_far_two_c
#print axioms wall_far_counts

end Erdos634.Pi3L3
