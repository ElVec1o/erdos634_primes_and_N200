/-
Draft/InterfaceFloorGeom.lean -- the interface-floor statement for a real dissection.

A *straight interface* is taken in the form the trace-covering theorem uses: a stretch `[X + s u, X + t u]` of a
line `{φ = c}` whose open part lies in the interior of the target and meets no tile interior (it is covered by
tile boundaries), and whose two ends are not straddled from either side (no tile edge lying on the line has an end
of the stretch in its relative interior).  A maximal straight segment of the union of the tile boundaries inside
the target is of this form.

* `two_sides_sum` (from `TraceCovering.wall_sum`, both sides): the tile edges of each side lying in the stretch
  have total length `t − s`.
* `sum_count`, `len_mem`: each such edge has one of the three side lengths of the tile, so each total is
  `n_a a + n_b b + n_c c` with `n_x` the number of edges of that length.
* `interface_floor_geom`: for the tile `ν · (ef, f² − e², f²)`, `0 < e < f` coprime, a stretch shorter than
  `ν f a` and than `ν f b` carries the same number of `a`-, `b`- and `c`-edges on its two sides
  (`InterfaceFloor.interface_floor` applied to the difference of the two counts).

Any congruent dissection, any target, any scale.  No sorry, no native_decide.
-/
import Erdos634.Draft.TraceCovering
import Erdos634.PinPlumbing
import Erdos634.Congruence
import Erdos634.CongruentAngles
import Erdos634.InterfaceFloor

open scoped Classical

namespace Erdos634.Draft.InterfaceFloorGeom

open Erdos634.Geometry Erdos634.Draft.TraceCovering Erdos634.InterfaceFloor
open Set

variable {N : ℕ}

/-- the length of the edge `e` (tile `e.1`, from vertex `e.2` to the next) -/
noncomputable def len (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

/-- the edges of the side `lineChain g d` lying in the stretch `[X + s u, X + t u]` -/
noncomputable def word (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (d : ℝ) (X u : Plane) (s t : ℝ) :
    Finset (Fin N × Fin 3) :=
  (D.lineChain g d).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X + s • u) (X + t • u))

/-- a sum of terms each equal to one of three distinct values, by the number of terms of each value -/
theorem sum_count {ι : Type*} (S : Finset ι) (φ : ι → ℝ) {A B C : ℝ} (hAB : A ≠ B) (hAC : A ≠ C)
    (hBC : B ≠ C) (h : ∀ e ∈ S, φ e = A ∨ φ e = B ∨ φ e = C) :
    ∑ e ∈ S, φ e = (S.filter (fun e => φ e = A)).card * A + (S.filter (fun e => φ e = B)).card * B
      + (S.filter (fun e => φ e = C)).card * C := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    rw [Finset.sum_insert ha, ih']
    have hnA : a ∉ s.filter (fun e => φ e = A) := fun hm => ha (Finset.mem_filter.mp hm).1
    have hnB : a ∉ s.filter (fun e => φ e = B) := fun hm => ha (Finset.mem_filter.mp hm).1
    have hnC : a ∉ s.filter (fun e => φ e = C) := fun hm => ha (Finset.mem_filter.mp hm).1
    rcases h a (Finset.mem_insert_self a s) with h1 | h1 | h1
    · have e1 : (insert a s).filter (fun e => φ e = A) = insert a (s.filter (fun e => φ e = A)) := by
        rw [Finset.filter_insert, if_pos h1]
      have e2 : (insert a s).filter (fun e => φ e = B) = s.filter (fun e => φ e = B) := by
        rw [Finset.filter_insert, if_neg (by rw [h1]; exact hAB)]
      have e3 : (insert a s).filter (fun e => φ e = C) = s.filter (fun e => φ e = C) := by
        rw [Finset.filter_insert, if_neg (by rw [h1]; exact hAC)]
      rw [e1, e2, e3, Finset.card_insert_of_notMem hnA, h1]
      push_cast; ring
    · have e1 : (insert a s).filter (fun e => φ e = A) = s.filter (fun e => φ e = A) := by
        rw [Finset.filter_insert, if_neg (by rw [h1]; exact hAB.symm)]
      have e2 : (insert a s).filter (fun e => φ e = B) = insert a (s.filter (fun e => φ e = B)) := by
        rw [Finset.filter_insert, if_pos h1]
      have e3 : (insert a s).filter (fun e => φ e = C) = s.filter (fun e => φ e = C) := by
        rw [Finset.filter_insert, if_neg (by rw [h1]; exact hBC)]
      rw [e1, e2, e3, Finset.card_insert_of_notMem hnB, h1]
      push_cast; ring
    · have e1 : (insert a s).filter (fun e => φ e = A) = s.filter (fun e => φ e = A) := by
        rw [Finset.filter_insert, if_neg (by rw [h1]; exact hAC.symm)]
      have e2 : (insert a s).filter (fun e => φ e = B) = s.filter (fun e => φ e = B) := by
        rw [Finset.filter_insert, if_neg (by rw [h1]; exact hBC.symm)]
      have e3 : (insert a s).filter (fun e => φ e = C) = insert a (s.filter (fun e => φ e = C)) := by
        rw [Finset.filter_insert, if_pos h1]
      rw [e1, e2, e3, Finset.card_insert_of_notMem hnC, h1]
      push_cast; ring

theorem edist_eq_to_dist_eq {a b c d : Plane} (h : edist a b = edist c d) : dist a b = dist c d := by
  have := congr_arg ENNReal.toReal h
  rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg, edist_dist, ENNReal.toReal_ofReal dist_nonneg] at this

/-- every tile edge has one of the three side lengths of the model -/
theorem len_mem (D : CongruentDissection N) (e : Fin N × Fin 3) :
    len D.toDissection e = dist (D.model.pts 0) (D.model.pts 1) ∨
    len D.toDissection e = dist (D.model.pts 1) (D.model.pts 2) ∨
    len D.toDissection e = dist (D.model.pts 0) (D.model.pts 2) := by
  obtain ⟨i, i', hii, hd⟩ :=
    Erdos634.Geometry.congruent_corner_angles_aux ((D.tiles_congruent e.1).symm)
      e.2 (e.2 + 1) (fin3_succ_ne e.2)
  unfold len
  rcases Erdos634.PinPlumbing.model_three_lengths D.model i i' hii with h | h | h
  · left; rw [hd]; exact edist_eq_to_dist_eq h
  · right; left; rw [hd]; exact edist_eq_to_dist_eq h
  · right; right; rw [hd]; exact edist_eq_to_dist_eq h

/-- **The two sides of a straight interface have the same length in whole edges.** -/
theorem two_sides_sum (D : CongruentDissection N) (φ : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hφ : φ ≠ 0) (X u : Plane)
    (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1) {s t : ℝ} (hst : s ≤ t)
    (hint : ∀ x ∈ Ioo s t, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo s t, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (hs : ¬ Straddled D.toDissection φ c (X + s • u)) (ht : ¬ Straddled D.toDissection φ c (X + t • u))
    (hs' : ¬ Straddled D.toDissection (-φ) (-c) (X + s • u))
    (ht' : ¬ Straddled D.toDissection (-φ) (-c) (X + t • u)) :
    ∑ e ∈ word D.toDissection φ c X u s t, len D.toDissection e = t - s ∧
    ∑ e ∈ word D.toDissection (-φ) (-c) X u s t, len D.toDissection e = t - s := by
  unfold word len
  exact ⟨wall_sum hφ (fun _ => Iff.rfl) hφ hX hu hu1 hst hint hwall hs ht,
    wall_sum (neg_ne_zero.mpr hφ) (fun y => neg_iff y) hφ hX hu hu1 hst hint hwall hs' ht'⟩

/-- **`prop:interfacefloor`.**  Tile `ν · (ef, f² − e², f²)` with `0 < e < f` coprime.  A straight interface
shorter than `ν f a` and than `ν f b` carries the same number of edges of each length on its two sides. -/
theorem interface_floor_geom (D : CongruentDissection N) {e f : ℤ} {ν : ℝ} (hν : 0 < ν) (he : 0 < e)
    (hef : e < f) (hc : IsCoprime f e)
    (hA : dist (D.model.pts 0) (D.model.pts 1) = ν * ((e : ℝ) * f))
    (hB : dist (D.model.pts 1) (D.model.pts 2) = ν * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hC : dist (D.model.pts 0) (D.model.pts 2) = ν * (f : ℝ) ^ 2)
    (φ : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hφ : φ ≠ 0) (X u : Plane)
    (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1) {s t : ℝ} (hst : s ≤ t)
    (hint : ∀ x ∈ Ioo s t, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo s t, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (hs : ¬ Straddled D.toDissection φ c (X + s • u)) (ht : ¬ Straddled D.toDissection φ c (X + t • u))
    (hs' : ¬ Straddled D.toDissection (-φ) (-c) (X + s • u))
    (ht' : ¬ Straddled D.toDissection (-φ) (-c) (X + t • u))
    (hshortA : t - s < ν * ((f : ℝ) * ((e : ℝ) * f)))
    (hshortB : t - s < ν * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) :
    ((word D.toDissection φ c X u s t).filter
        (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 1))).card
      = ((word D.toDissection (-φ) (-c) X u s t).filter
        (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 1))).card ∧
    ((word D.toDissection φ c X u s t).filter
        (fun x => len D.toDissection x = dist (D.model.pts 1) (D.model.pts 2))).card
      = ((word D.toDissection (-φ) (-c) X u s t).filter
        (fun x => len D.toDissection x = dist (D.model.pts 1) (D.model.pts 2))).card ∧
    ((word D.toDissection φ c X u s t).filter
        (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 2))).card
      = ((word D.toDissection (-φ) (-c) X u s t).filter
        (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 2))).card := by
  have hf0 : (0 : ℤ) < f := lt_trans he hef
  have ha : (0 : ℤ) < e * f := mul_pos he hf0
  have hb : (0 : ℤ) < f ^ 2 - e ^ 2 := by nlinarith
  have hcc : (0 : ℤ) < f ^ 2 := by positivity
  -- the three lengths are distinct
  have hABz : e * f ≠ f ^ 2 - e ^ 2 := by
    intro h
    have h1 : e ∣ f ^ 2 := ⟨e + f, by linear_combination (-1 : ℤ) * h⟩
    have h2 : IsCoprime e (f ^ 2) := hc.symm.pow_right
    have h3 : IsUnit e := h2.isUnit_of_dvd' (dvd_refl e) h1
    have h4 : e = 1 := by
      rcases Int.isUnit_iff.mp h3 with h5 | h5 <;> omega
    rw [h4] at h
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ f - 2 by omega) (show (0 : ℤ) ≤ f + 1 by omega)]
  have hACz : e * f ≠ f ^ 2 := by
    intro h
    nlinarith [mul_pos hf0 (sub_pos.mpr hef)]
  have hBCz : f ^ 2 - e ^ 2 ≠ f ^ 2 := by
    intro h
    nlinarith [mul_pos he he]
  have hAB : dist (D.model.pts 0) (D.model.pts 1) ≠ dist (D.model.pts 1) (D.model.pts 2) := by
    rw [hA, hB]
    intro h
    apply hABz
    have h' := mul_left_cancel₀ hν.ne' h
    exact_mod_cast h'
  have hAC : dist (D.model.pts 0) (D.model.pts 1) ≠ dist (D.model.pts 0) (D.model.pts 2) := by
    rw [hA, hC]
    intro h
    apply hACz
    have h' := mul_left_cancel₀ hν.ne' h
    exact_mod_cast h'
  have hBC : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 0) (D.model.pts 2) := by
    rw [hB, hC]
    intro h
    apply hBCz
    have h' := mul_left_cancel₀ hν.ne' h
    exact_mod_cast h'
  obtain ⟨hS1, hS2⟩ := two_sides_sum D φ c hφ X u hX hu hu1 hst hint hwall hs ht hs' ht'
  rw [sum_count _ _ hAB hAC hBC (fun x _ => len_mem D x)] at hS1
  rw [sum_count _ _ hAB hAC hBC (fun x _ => len_mem D x)] at hS2
  generalize ((word D.toDissection φ c X u s t).filter
    (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 1))).card = a₁ at hS1 ⊢
  generalize ((word D.toDissection φ c X u s t).filter
    (fun x => len D.toDissection x = dist (D.model.pts 1) (D.model.pts 2))).card = b₁ at hS1 ⊢
  generalize ((word D.toDissection φ c X u s t).filter
    (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 2))).card = c₁ at hS1 ⊢
  generalize ((word D.toDissection (-φ) (-c) X u s t).filter
    (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 1))).card = a₂ at hS2 ⊢
  generalize ((word D.toDissection (-φ) (-c) X u s t).filter
    (fun x => len D.toDissection x = dist (D.model.pts 1) (D.model.pts 2))).card = b₂ at hS2 ⊢
  generalize ((word D.toDissection (-φ) (-c) X u s t).filter
    (fun x => len D.toDissection x = dist (D.model.pts 0) (D.model.pts 2))).card = c₂ at hS2 ⊢
  rw [hA, hB, hC] at hS1 hS2
  -- the integer relation between the two words
  have hrel : ((a₁ : ℤ) - a₂) * (e * f) + ((b₁ : ℤ) - b₂) * (f ^ 2 - e ^ 2) + ((c₁ : ℤ) - c₂) * f ^ 2 = 0 := by
    have h : ν * ((((a₁ : ℤ) - a₂) * (e * f) + ((b₁ : ℤ) - b₂) * (f ^ 2 - e ^ 2)
        + ((c₁ : ℤ) - c₂) * f ^ 2 : ℤ) : ℝ) = 0 := by
      push_cast
      linear_combination hS1 - hS2
    have h' := (mul_eq_zero.mp h).resolve_left hν.ne'
    exact_mod_cast h'
  have hz : (a₁ : ℤ) - a₂ = 0 ∧ (b₁ : ℤ) - b₂ = 0 ∧ (c₁ : ℤ) - c₂ = 0 := by
    by_contra hne
    have hfl := interface_floor e f _ _ _ he hef hc hrel hne
    have hM : oneSided ((a₁ : ℤ) - a₂) ((b₁ : ℤ) - b₂) ((c₁ : ℤ) - c₂) (e * f) (f ^ 2 - e ^ 2) (f ^ 2)
        ≤ a₁ * (e * f) + b₁ * (f ^ 2 - e ^ 2) + c₁ * f ^ 2 := by
      unfold oneSided
      have m1 : max ((a₁ : ℤ) - a₂) 0 ≤ a₁ := by omega
      have m2 : max ((b₁ : ℤ) - b₂) 0 ≤ b₁ := by omega
      have m3 : max ((c₁ : ℤ) - c₂) 0 ≤ c₁ := by omega
      have := mul_le_mul_of_nonneg_right m1 ha.le
      have := mul_le_mul_of_nonneg_right m2 hb.le
      have := mul_le_mul_of_nonneg_right m3 hcc.le
      linarith
    have hr : ν * (((a₁ : ℤ) * (e * f) + b₁ * (f ^ 2 - e ^ 2) + c₁ * f ^ 2 : ℤ) : ℝ) = t - s := by
      push_cast
      linear_combination hS1
    have hMlt : (a₁ : ℤ) * (e * f) + b₁ * (f ^ 2 - e ^ 2) + c₁ * f ^ 2 < f * min (e * f) (f ^ 2 - e ^ 2) := by
      rcases min_choice (e * f) (f ^ 2 - e ^ 2) with hm | hm <;> rw [hm]
      · have h1 : (((a₁ : ℤ) * (e * f) + b₁ * (f ^ 2 - e ^ 2) + c₁ * f ^ 2 : ℤ) : ℝ)
            < ((f * (e * f) : ℤ) : ℝ) := by
          refine lt_of_mul_lt_mul_left ?_ hν.le
          rw [hr]; push_cast; exact hshortA
        exact_mod_cast h1
      · have h1 : (((a₁ : ℤ) * (e * f) + b₁ * (f ^ 2 - e ^ 2) + c₁ * f ^ 2 : ℤ) : ℝ)
            < ((f * (f ^ 2 - e ^ 2) : ℤ) : ℝ) := by
          refine lt_of_mul_lt_mul_left ?_ hν.le
          rw [hr]; push_cast; exact hshortB
        exact_mod_cast h1
    exact absurd (lt_of_le_of_lt (le_trans hfl hM) hMlt) (lt_irrefl _)
  obtain ⟨z1, z2, z3⟩ := hz
  exact ⟨by omega, by omega, by omega⟩

end Erdos634.Draft.InterfaceFloorGeom

#print axioms Erdos634.Draft.InterfaceFloorGeom.interface_floor_geom
