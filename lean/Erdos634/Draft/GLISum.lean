import Mathlib.Tactic
import Erdos634.Draft.GLIModel
import Erdos634.Draft.GLCCorner

/-!
# Side sums and the bridge from tile edges along a wall to chain indices

* `sum_lenK_nat` (sums): `∑_{m<n} lenK k (ty m) = L` when the wall has length `s·L` and `(a,b,c) = s·(k²,2k+1,k(k+1))`.
* `unique_by_end`: a wall edge is determined by its east position.
* `edge_ends_of_vec`: a tile edge `{U,V}` with `V = U + r(b-a)`, `r>0`, `U` on the wall, is a wall edge with west end `U`, east end `V`.
* `first_of_edge`, `next_of_edge`, `last_of_edge`, `prev_of_edge`: such an edge is the chain edge `E 0`, `E (m+1)`, `E (n-1)`, `E (m-1)` when `U` is `w.a`,
  the east end of `E m`, `V = w.b`, resp. `V` is the west end of `E m`.
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG
  Erdos634.BaseChain

variable {N : ℕ}

theorem eLen_eq_lenK (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    (e : Fin N × Fin 3) :
    D.eLen e = s * ((lenK k (tyE D.toDissection a b e) : ℕ) : ℝ) := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  rcases Row4.eLen_abc D h e with h1 | h1 | h1
  · have : tyE D.toDissection a b e = TT.a := by simp [tyE, h1]
    rw [this, h1, ha]; simp [lenK]
  · have : tyE D.toDissection a b e = TT.b := by simp [tyE, h1, hab.symm]
    rw [this, h1, hb]; simp [lenK]
  · have : tyE D.toDissection a b e = TT.c := by simp [tyE, h1, hac.symm, hbc.symm]
    rw [this, h1, hc]; simp [lenK]

theorem sum_lenK (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    {w : Wall D.toDissection} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n) :
    s * ((∑ m ∈ Finset.range n, lenK k ((sideOf D α a b w.dir E n).ty m) : ℕ) : ℝ) = dist w.a w.b := by
  have hd : dist w.a w.b = w.dir w.b - w.dir w.a := by
    rw [w.hiso _ _ (w.hline _ (left_mem_segment ℝ _ _)) (w.hline _ (right_mem_segment ℝ _ _)),
      abs_of_neg (by linarith [w.dir_lt])]
    ring
  rw [hd, ← C.sum_len, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← C.dist_eq (Finset.mem_range.mp hm)]
  exact (eLen_eq_lenK D k hα h ha hb hc (E m)).symm

theorem sum_lenK_nat (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ) (hs : 0 < s)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    {w : Wall D.toDissection} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n) (L : ℕ)
    (hL : dist w.a w.b = s * (L : ℝ)) :
    ∑ m ∈ Finset.range n, lenK k ((sideOf D α a b w.dir E n).ty m) = L := by
  have := sum_lenK D k hα h ha hb hc C
  rw [hL] at this
  exact_mod_cast mul_left_cancel₀ hs.ne' this

namespace IsChain

variable {D : Dissection N} {w : Wall D} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n)
include C

theorem end_lt {m m' : ℕ} (h : m < m') (h' : m' < n) :
    edgeEnd D w.dir (E m) < edgeEnd D w.dir (E m') := by
  have h1 := C.edgePos_next (by omega : m + 1 < n)
  have h2 : edgePos D w.dir (E (m + 1)) ≤ edgePos D w.dir (E m') := by
    rcases Nat.lt_or_ge (m + 1) m' with h3 | h3
    · exact (C.pos_lt h3 h').le
    · have : m' = m + 1 := by omega
      rw [this]
  have h3 := C.nondeg m' h'
  linarith

theorem unique_by_end {p : Fin N × Fin 3} (hp : p ∈ wallList D w.g 0) {m : ℕ} (hm : m < n)
    (h : edgeEnd D w.dir p = edgeEnd D w.dir (E m)) : p = E m := by
  obtain ⟨m', hm', rfl⟩ := C.surj p hp
  rcases lt_trichotomy m' m with h1 | h1 | h1
  · have := C.end_lt h1 hm; linarith
  · rw [h1]
  · have := C.end_lt h1 hm'; linarith

end IsChain

theorem wall_dir_of_vec {D : Dissection N} (w : Wall D) {U V : Plane} {r : ℝ} (hr : 0 < r)
    (hU : w.g U = 0) (hV : V = U + r • (w.b - w.a)) : w.g V = 0 ∧ w.dir U < w.dir V := by
  have hb := w.hline _ (right_mem_segment ℝ w.a w.b)
  have ha := w.hline _ (left_mem_segment ℝ w.a w.b)
  have hlin : w.g.linear (w.b - w.a) = 0 := by
    have : w.g.linear (w.b -ᵥ w.a) = w.g w.b -ᵥ w.g w.a := AffineMap.linearMap_vsub _ _ _
    rw [vsub_eq_sub, vsub_eq_sub, hb, ha] at this
    simpa using this
  refine ⟨?_, ?_⟩
  · have : V = (r • (w.b - w.a)) +ᵥ U := by rw [vadd_eq_add, hV, add_comm]
    rw [this, AffineMap.map_vadd, map_smul, hlin, hU]; simp
  · rw [hV, map_add, map_smul, map_sub, smul_eq_mul]
    have := w.dir_lt
    nlinarith

theorem edge_ends_of_vec {D : Dissection N} (w : Wall D) {i : Fin N} {x : Fin 3} {U V : Plane} {r : ℝ}
    (hr : 0 < r) (hU : w.g U = 0) (hV : V = U + r • (w.b - w.a))
    (hends : ((D.tile i).pts x = U ∧ (D.tile i).pts (x + 1) = V) ∨
      ((D.tile i).pts x = V ∧ (D.tile i).pts (x + 1) = U)) :
    (i, x) ∈ wallList D w.g 0 ∧ edgeWest D w.dir (i, x) = U ∧ edgeEast D w.dir (i, x) = V ∧
      edgePos D w.dir (i, x) = w.dir U ∧ edgeEnd D w.dir (i, x) = w.dir V := by
  obtain ⟨hgV, hlt⟩ := wall_dir_of_vec w hr hU hV
  have hpos : edgePos D w.dir (i, x) = w.dir U ∧ edgeEnd D w.dir (i, x) = w.dir V := by
    unfold edgePos edgeEnd
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2]; exact ⟨min_eq_left hlt.le, max_eq_right hlt.le⟩
    · simp only [h1, h2]; exact ⟨min_eq_right hlt.le, max_eq_left hlt.le⟩
  refine ⟨?_, ?_, ?_, hpos⟩
  · rw [mem_wallList]
    show w.g ((D.tile i).pts x) = 0 ∧ w.g ((D.tile i).pts (x + 1)) = 0
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hU, hgV⟩
    · rw [h1, h2]; exact ⟨hgV, hU⟩
  · unfold edgeWest
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2, hlt.le, if_true]
    · simp only [h1, h2, not_le.mpr hlt, if_false]
  · unfold edgeEast
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2, hlt.le, if_true]
    · simp only [h1, h2, not_le.mpr hlt, if_false]

namespace IsChain

variable {D : Dissection N} {w : Wall D} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n)
include C

/-- A wall edge `{U, V}` with `U = w.a` is `E 0`. -/
theorem first_of_edge {i : Fin N} {x : Fin 3} {U V : Plane} {r : ℝ}
    (hr : 0 < r) (hU : w.g U = 0) (hV : V = U + r • (w.b - w.a))
    (hends : ((D.tile i).pts x = U ∧ (D.tile i).pts (x + 1) = V) ∨
      ((D.tile i).pts x = V ∧ (D.tile i).pts (x + 1) = U)) (hUa : U = w.a) :
    (i, x) = E 0 := by
  obtain ⟨hm, -, -, hp, -⟩ := edge_ends_of_vec w hr hU hV hends
  apply C.unique_by_pos hm C.n_pos
  rw [hp, ← dir_edgeWest, C.west0, hUa]

/-- A wall edge `{U, V}` with `U` the east end of `E m` is `E (m+1)`. -/
theorem next_of_edge {i : Fin N} {x : Fin 3} {U V : Plane} {r : ℝ}
    (hr : 0 < r) (hU : w.g U = 0) (hV : V = U + r • (w.b - w.a))
    (hends : ((D.tile i).pts x = U ∧ (D.tile i).pts (x + 1) = V) ∨
      ((D.tile i).pts x = V ∧ (D.tile i).pts (x + 1) = U)) {m : ℕ} (hm : m < n)
    (hUe : U = edgeEast D w.dir (E m)) : m + 1 < n ∧ (i, x) = E (m + 1) := by
  obtain ⟨hmem, -, -, hp, -⟩ := edge_ends_of_vec w hr hU hV hends
  obtain ⟨m', hm', hEm'⟩ := C.surj _ hmem
  have hpe : edgePos D w.dir (E m') = edgeEnd D w.dir (E m) := by
    rw [hEm', hp, hUe, dir_edgeEast]
  have hnd := C.nondeg m hm
  have hm'm : m < m' := by
    by_contra hc
    push Not at hc
    rcases lt_or_eq_of_le hc with h1 | h1
    · have := C.pos_lt h1 hm; linarith
    · rw [h1] at hpe; linarith
  have h1 : m' = m + 1 := by
    by_contra hc
    have hlt : m + 1 < m' := by omega
    have := C.pos_lt hlt hm'
    rw [C.edgePos_next (by omega : m + 1 < n)] at this
    linarith
  subst h1
  exact ⟨hm', hEm'.symm⟩

/-- A wall edge `{U, V}` with `V = w.b` is `E (n-1)`. -/
theorem last_of_edge {i : Fin N} {x : Fin 3} {U V : Plane} {r : ℝ}
    (hr : 0 < r) (hU : w.g U = 0) (hV : V = U + r • (w.b - w.a))
    (hends : ((D.tile i).pts x = U ∧ (D.tile i).pts (x + 1) = V) ∨
      ((D.tile i).pts x = V ∧ (D.tile i).pts (x + 1) = U)) (hVb : V = w.b) :
    (i, x) = E (n - 1) := by
  obtain ⟨hm, -, -, -, hp⟩ := edge_ends_of_vec w hr hU hV hends
  have hn : n - 1 < n := by have := C.n_pos; omega
  apply C.unique_by_end hm hn
  rw [hp, hVb, ← dir_edgeEast, C.east_last]

/-- A wall edge `{U, V}` with `V` the west end of `E m`, `m > 0`, is `E (m-1)`. -/
theorem prev_of_edge {i : Fin N} {x : Fin 3} {U V : Plane} {r : ℝ}
    (hr : 0 < r) (hU : w.g U = 0) (hV : V = U + r • (w.b - w.a))
    (hends : ((D.tile i).pts x = U ∧ (D.tile i).pts (x + 1) = V) ∨
      ((D.tile i).pts x = V ∧ (D.tile i).pts (x + 1) = U)) {m : ℕ} (hm : m < n) (hm0 : 0 < m)
    (hVw : V = edgeWest D w.dir (E m)) : (i, x) = E (m - 1) := by
  obtain ⟨hmem, -, -, -, hp⟩ := edge_ends_of_vec w hr hU hV hends
  obtain ⟨m', hm', hEm'⟩ := C.surj _ hmem
  have hpe : edgeEnd D w.dir (E m') = edgePos D w.dir (E m) := by
    rw [hEm', hp, hVw, dir_edgeWest]
  have hnd := C.nondeg m hm
  have hm'm : m' < m := by
    by_contra hc
    push Not at hc
    rcases lt_or_eq_of_le hc with h1 | h1
    · have := C.end_lt h1 hm'; linarith
    · rw [← h1] at hpe; linarith [C.nondeg m' hm']
  have h1 : m' = m - 1 := by
    by_contra hc
    have hlt : m' < m - 1 := by omega
    have := C.end_lt hlt (by omega : m - 1 < n)
    have h2 := C.edgePos_next (by omega : m - 1 + 1 < n)
    rw [show m - 1 + 1 = m by omega] at h2
    linarith
  subst h1
  exact hEm'.symm

end IsChain

end Erdos634.GLI

#print axioms Erdos634.GLI.sum_lenK_nat
#print axioms Erdos634.GLI.IsChain.next_of_edge
#print axioms Erdos634.GLI.IsChain.prev_of_edge
#print axioms Erdos634.GLI.IsChain.first_of_edge
#print axioms Erdos634.GLI.IsChain.last_of_edge
