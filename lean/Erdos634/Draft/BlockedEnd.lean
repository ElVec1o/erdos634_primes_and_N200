/-
Draft/BlockedEnd.lean -- quantization of a blocked end, and its corollary on one blocked end, for a real dissection.

Setting: a line `{φ = c}` with unit direction `u`, a point `X` on it, a tile `j` on the side `φ ≤ c` with an edge on
the line containing `X` and the points `X + x u` considered; the far side is the chain `lineChain (−φ) (−c)`.
"The extension beyond `X` is blocked" is the hypothesis that no far-side edge on the line has `X` in its relative
interior (`¬ Straddled`); `TraceCovering.not_straddled_of_outside_before` and `.not_straddled_of_near_interior`
derive it when the line leaves the target at `X` or when its continuation enters the interior of a tile.

* `vertex_not_through`: a vertex of the tiling lying in the relative interior of an edge of one tile is not in the
  relative interior of an edge of another tile (three local angles `π`, `π`, `> 0` at an interior point).
* `blocked_end_quantized`: a vertex of the tiling at `X + v u` in the relative interior of
  the edge is at distance `v = n_a a + n_b b + n_c c` from `X`.
* `blocked_end_no_vertex`: hence no such vertex at distance less than each of the three sides.
* `one_end_blocked`: for the edge `[X, Y]`, `Y = X + x₀ u`: either no far-side edge passes
  through `Y` and `|XY|` is a sum of tile sides, or a far-side edge passes through `Y`, starts at a point of
  `[X, Y)` at distance `s` from `X`, and `s` is a sum of tile sides (possibly `0`).
* `one_end_blocked_min`: if `|XY|` is at most each side, the far side of `[X, Y]` is a single edge: one inside
  `[X, Y]` of length `|XY|`, or one starting at `X` and passing through `Y`.

Any congruent dissection, any target, any tile.  No sorry, no native_decide.
-/
import Erdos634.Draft.InterfaceFloorGeom
import Erdos634.RouteOneThroughEdge
import Erdos634.RouteOneVertexKill
import Erdos634.MarchFlank

open scoped Classical

namespace Erdos634.Draft.BlockedEnd

open Erdos634.Geometry Erdos634.Draft.TraceCovering Erdos634.Draft.InterfaceFloorGeom
open Set

variable {N : ℕ}

theorem fin3_shift : ∀ x : Fin 3, x + 2 + 1 = x ∧ x + 2 + 2 = x + 1 := by decide

/-- a sum of terms each equal to one of three values -/
theorem sum_three {ι : Type*} (S : Finset ι) (ψ : ι → ℝ) (A B C : ℝ)
    (h : ∀ e ∈ S, ψ e = A ∨ ψ e = B ∨ ψ e = C) :
    ∃ na nb nc : ℕ, (na : ℝ) * A + nb * B + nc * C = ∑ e ∈ S, ψ e := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨na, nb, nc, hS⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    rcases h a (Finset.mem_insert_self a s) with h1 | h1 | h1
    · exact ⟨na + 1, nb, nc, by rw [Finset.sum_insert ha, ← hS, h1]; push_cast; ring⟩
    · exact ⟨na, nb + 1, nc, by rw [Finset.sum_insert ha, ← hS, h1]; push_cast; ring⟩
    · exact ⟨na, nb, nc + 1, by rw [Finset.sum_insert ha, ← hS, h1]; push_cast; ring⟩

/-- a combination of three positive numbers with natural coefficients that is smaller than each of them is `0` -/
theorem small_comb {A B C s : ℝ} {na nb nc : ℕ} (hA0 : 0 < A) (hB0 : 0 < B) (hC0 : 0 < C)
    (h : (na : ℝ) * A + nb * B + nc * C = s) (hA : s < A) (hB : s < B) (hC : s < C) : s = 0 := by
  have h1 : (0 : ℝ) ≤ (na : ℝ) * A := by positivity
  have h2 : (0 : ℝ) ≤ (nb : ℝ) * B := by positivity
  have h3 : (0 : ℝ) ≤ (nc : ℝ) * C := by positivity
  rcases Nat.eq_zero_or_pos na with ha | ha
  · rcases Nat.eq_zero_or_pos nb with hb | hb
    · rcases Nat.eq_zero_or_pos nc with hc | hc
      · subst ha; subst hb; subst hc
        simp at h; linarith
      · have h4 : (1 : ℝ) ≤ nc := by exact_mod_cast hc
        have h5 : C ≤ (nc : ℝ) * C := by nlinarith
        linarith
    · have h4 : (1 : ℝ) ≤ nb := by exact_mod_cast hb
      have h5 : B ≤ (nb : ℝ) * B := by nlinarith
      linarith
  · have h4 : (1 : ℝ) ≤ na := by exact_mod_cast ha
    have h5 : A ≤ (na : ℝ) * A := by nlinarith
    linarith

/-- **A vertex inside an edge is not crossed by an edge of another tile.** -/
theorem vertex_not_through (D : Dissection N) {V : Plane} (hV : V ∈ interior D.target.carrier)
    (j : Fin N) (kj : Fin 3)
    (hVj : V ∈ openSegment ℝ ((D.tile j).pts kj) ((D.tile j).pts (kj + 1)))
    (k : Fin N) (m : Fin 3) (hVk : V = (D.tile k).pts m)
    (i : Fin N) (hij : i ≠ j) (ki : Fin 3)
    (hVi : V ∈ openSegment ℝ ((D.tile i).pts ki) ((D.tile i).pts (ki + 1))) : False := by
  have hj : (D.tile j).localAngle V = Real.pi := by
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile j) (kj + 2)
    rw [(fin3_shift kj).1, (fin3_shift kj).2]; exact hVj
  have hi : (D.tile i).localAngle V = Real.pi := by
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile i) (ki + 2)
    rw [(fin3_shift ki).1, (fin3_shift ki).2]; exact hVi
  have hklt : (D.tile k).localAngle V < Real.pi := by
    rw [hVk, (D.tile k).localAngle_vertex m]
    exact Erdos634.RouteOneVertexKill.cornerAngle_lt_pi (D.tile k) m
  have hk0 : (D.tile k).localAngle V ≠ 0 :=
    Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile k)
      (by rw [hVk]; exact subset_convexHull ℝ _ ⟨m, rfl⟩)
  have hik : i ≠ k := by
    intro h; rw [h] at hi; rw [hi] at hklt; exact lt_irrefl _ hklt
  have hjk : j ≠ k := by
    intro h; rw [h] at hj; rw [hj] at hklt; exact lt_irrefl _ hklt
  exact Erdos634.RouteOne.two_through_excludes_third D hV i j k hij hik hjk hi hj hk0

section Wall

variable (D : CongruentDissection N) (φ : Plane →ₗ[ℝ] ℝ) (c : ℝ) (X u : Plane)

/-- a stretch of an edge of a tile is a wall -/
theorem wall_of_edge (j : Fin N) (kT : Fin 3) (hXT : X ∈ (D.tile j).edge kT) {v : ℝ} (hv : 0 < v)
    (hVT : X + v • u ∈ (D.tile j).edge kT) :
    ∀ x ∈ Ioo (0 : ℝ) v, ∀ i, X + x • u ∉ interior (D.tile i).carrier := by
  have hX0 : X + (0 : ℝ) • u = X := by rw [zero_smul, add_zero]
  have hseg : segment ℝ X (X + v • u) ⊆ (D.tile j).edge kT :=
    (convex_segment _ _).segment_subset hXT hVT
  intro x hx
  apply D.toDissection.edge_point_not_interior (j := j) (k := kT)
  apply hseg
  have h := segment_param (X := X) (u := u) 0 v
  rw [hX0, min_eq_left hv.le, max_eq_right hv.le] at h
  rw [h]
  exact ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩

/-- the far-side edges inside `[X, X + v u]` sum to a combination of the three sides -/
theorem far_sum (hφ : φ ≠ 0) (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1) {v : ℝ} (hv : 0 ≤ v)
    (hint : ∀ x ∈ Ioo (0 : ℝ) v, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo (0 : ℝ) v, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (h0 : ¬ Straddled D.toDissection (-φ) (-c) X)
    (hV : ¬ Straddled D.toDissection (-φ) (-c) (X + v • u)) :
    ∃ na nb nc : ℕ, (na : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      + nb * dist (D.model.pts 1) (D.model.pts 2) + nc * dist (D.model.pts 0) (D.model.pts 2) = v := by
  have hX0 : X + (0 : ℝ) • u = X := by rw [zero_smul, add_zero]
  have hsum := wall_sum (D := D.toDissection) (g := -φ) (d := -c) (neg_ne_zero.mpr hφ)
    (fun y => neg_iff y) hφ hX hu hu1 (s := 0) (t := v) hv hint hwall (by rw [hX0]; exact h0) hV
  rw [sub_zero] at hsum
  obtain ⟨na, nb, nc, hS⟩ := sum_three _ (fun e => len D.toDissection e) _ _ _ (fun e _ => len_mem D e)
  exact ⟨na, nb, nc, hS.trans hsum⟩

/-- **`lem:anchorclear`.**  A vertex of the tiling in the relative interior of an edge whose end `X` is blocked
lies at a distance from `X` that is a sum of tile sides. -/
theorem blocked_end_quantized (hφ : φ ≠ 0) (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1)
    (j : Fin N) (kT : Fin 3) (hside : ∀ i, φ ((D.tile j).pts i) ≤ c)
    (hXT : X ∈ (D.tile j).edge kT) {v : ℝ} (hv : 0 < v)
    (hVT : X + v • u ∈ openSegment ℝ ((D.tile j).pts kT) ((D.tile j).pts (kT + 1)))
    (hint : ∀ x, 0 < x → x ≤ v → X + x • u ∈ interior D.target.carrier)
    (h0 : ¬ Straddled D.toDissection (-φ) (-c) X)
    (k : Fin N) (m : Fin 3) (hVk : X + v • u = (D.tile k).pts m) :
    ∃ na nb nc : ℕ, (na : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      + nb * dist (D.model.pts 1) (D.model.pts 2) + nc * dist (D.model.pts 0) (D.model.pts 2) = v := by
  have hV' : X + v • u ∈ (D.tile j).edge kT := openSegment_subset_segment ℝ _ _ hVT
  have hVfar : ¬ Straddled D.toDissection (-φ) (-c) (X + v • u) := by
    rintro ⟨e', he', hV''⟩
    have hne : e'.1 ≠ j := by
      intro h
      obtain ⟨-, -, hall⟩ := Dissection.mem_lineChain.mp he'
      refine two_vertices_on_line (D.tile j) φ c hφ (fun i => le_antisymm (hside i) ?_)
      have h1 := hall i
      rw [h] at h1
      simp only [LinearMap.neg_apply, neg_le_neg_iff] at h1
      exact h1
    exact vertex_not_through D.toDissection (hint v hv le_rfl) j kT hVT k m hVk e'.1 hne e'.2 hV''
  exact far_sum D φ c X u hφ hX hu hu1 hv.le (fun x hx => hint x hx.1 hx.2.le)
    (wall_of_edge D X u j kT hXT hv hV') h0 hVfar

/-- **No vertex below the least side.**  Under the hypotheses of `blocked_end_quantized`, the distance `v` is
not smaller than all three sides. -/
theorem blocked_end_no_vertex (hφ : φ ≠ 0) (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1)
    (j : Fin N) (kT : Fin 3) (hside : ∀ i, φ ((D.tile j).pts i) ≤ c)
    (hXT : X ∈ (D.tile j).edge kT) {v : ℝ} (hv : 0 < v)
    (hVT : X + v • u ∈ openSegment ℝ ((D.tile j).pts kT) ((D.tile j).pts (kT + 1)))
    (hint : ∀ x, 0 < x → x ≤ v → X + x • u ∈ interior D.target.carrier)
    (h0 : ¬ Straddled D.toDissection (-φ) (-c) X)
    (k : Fin N) (m : Fin 3) (hVk : X + v • u = (D.tile k).pts m)
    (hA : v < dist (D.model.pts 0) (D.model.pts 1)) (hB : v < dist (D.model.pts 1) (D.model.pts 2))
    (hC : v < dist (D.model.pts 0) (D.model.pts 2)) : False := by
  obtain ⟨na, nb, nc, h⟩ := blocked_end_quantized D φ c X u hφ hX hu hu1 j kT hside hXT hv hVT hint h0 k m hVk
  have h0' := small_comb (lt_trans hv hA) (lt_trans hv hB) (lt_trans hv hC) h hA hB hC
  linarith

/-- **`cor:onebloc`.**  The far side of an edge `[X, Y]`, `Y = X + x₀ u`, whose end `X` is blocked. -/
theorem one_end_blocked (hφ : φ ≠ 0) (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1)
    (j : Fin N) (kT : Fin 3) (hXT : X ∈ (D.tile j).edge kT) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hYT : X + x₀ • u ∈ (D.tile j).edge kT)
    (hint : ∀ x ∈ Ioo (0 : ℝ) x₀, X + x • u ∈ interior D.target.carrier)
    (h0 : ¬ Straddled D.toDissection (-φ) (-c) X) :
    (¬ Straddled D.toDissection (-φ) (-c) (X + x₀ • u) ∧
      ∃ na nb nc : ℕ, (na : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
        + nb * dist (D.model.pts 1) (D.model.pts 2) + nc * dist (D.model.pts 0) (D.model.pts 2) = x₀) ∨
    (∃ e ∈ D.toDissection.lineChain (-φ) (-c),
      X + x₀ • u ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ∧
      ∃ s : ℝ, 0 ≤ s ∧ s < x₀ ∧
        (X + s • u = (D.tile e.1).pts e.2 ∨ X + s • u = (D.tile e.1).pts (e.2 + 1)) ∧
        ∃ na nb nc : ℕ, (na : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
          + nb * dist (D.model.pts 1) (D.model.pts 2) + nc * dist (D.model.pts 0) (D.model.pts 2) = s) := by
  have hu0 := ne_zero_of_norm hu1
  have hX0 : X + (0 : ℝ) • u = X := by rw [zero_smul, add_zero]
  have hwall := wall_of_edge D X u j kT hXT hx₀ hYT
  have hgd : ∀ y, (-φ) y = -c ↔ φ y = c := fun y => neg_iff y
  by_cases hY : Straddled D.toDissection (-φ) (-c) (X + x₀ • u)
  · right
    obtain ⟨e, he, hYe⟩ := hY
    obtain ⟨h0e, h1e⟩ := onLine hgd he
    obtain ⟨hlt, -, hopen, -⟩ := edge_data (D := D.toDissection) hφ hX hu hu0 h0e h1e
    have hYe' := hYe
    rw [hopen, (lm_injective hu0).mem_set_image] at hYe'
    obtain ⟨hlo, hhi⟩ := hYe'
    -- the far edge starts at or after `X`
    have hlo0 : 0 ≤ lo D.toDissection X u e := by
      by_contra hneg
      push_neg at hneg
      apply h0
      refine ⟨e, he, ?_⟩
      rw [hopen]
      exact ⟨0, ⟨hneg, lt_trans hx₀ hhi⟩, hX0⟩
    -- its start is an endpoint of the edge
    have hend : X + lo D.toDissection X u e • u = (D.tile e.1).pts e.2 ∨
        X + lo D.toDissection X u e • u = (D.tile e.1).pts (e.2 + 1) := by
      have e0 := par_spec (exists_param hφ hX hu hu0 h0e)
      have e1 := par_spec (exists_param hφ hX hu hu0 h1e)
      unfold lo
      rcases min_choice (par X u ((D.tile e.1).pts e.2)) (par X u ((D.tile e.1).pts (e.2 + 1))) with h | h
      · left; rw [h]; exact e0.symm
      · right; rw [h]; exact e1.symm
    -- no other far edge passes through the start
    have hPfar : ¬ Straddled D.toDissection (-φ) (-c) (X + lo D.toDissection X u e • u) := by
      rw [str_iff hgd hφ hX hu hu0]
      rintro ⟨e', he', h1, h2⟩
      have hne : e ≠ e' := by
        intro h; rw [← h] at h1; exact lt_irrefl _ h1
      have hsub := meet (neg_ne_zero.mpr hφ) hgd hφ hX hu hu0 e he e' he' hne
      have hm1 : lo D.toDissection X u e ∈ Icc (lo D.toDissection X u e) (hi D.toDissection X u e) ∩
          Icc (lo D.toDissection X u e') (hi D.toDissection X u e') := ⟨⟨le_rfl, hlt.le⟩, ⟨h1.le, h2.le⟩⟩
      have hm2 : min (hi D.toDissection X u e) (hi D.toDissection X u e') ∈
          Icc (lo D.toDissection X u e) (hi D.toDissection X u e) ∩
          Icc (lo D.toDissection X u e') (hi D.toDissection X u e') :=
        ⟨⟨(lt_min hlt h2).le, min_le_left _ _⟩, ⟨(lt_trans h1 (lt_min hlt h2)).le, min_le_right _ _⟩⟩
      have := hsub hm1 hm2
      exact absurd this (ne_of_lt (lt_min hlt h2))
    refine ⟨e, he, hYe, lo D.toDissection X u e, hlo0, hlo, hend, ?_⟩
    exact far_sum D φ c X u hφ hX hu hu1 hlo0
      (fun x hx => hint x ⟨hx.1, lt_trans hx.2 hlo⟩)
      (fun x hx => hwall x ⟨hx.1, lt_trans hx.2 hlo⟩) h0 hPfar
  · left
    exact ⟨hY, far_sum D φ c X u hφ hX hu hu1 hx₀.le hint hwall h0 hY⟩

/-- **`cor:onebloc`, last clause.**  If `|XY|` is at most each side of the tile, the far side of `[X, Y]` is a
single tile edge: one lying in `[X, Y]` of length `|XY|`, or one that starts at `X` and passes through `Y`. -/
theorem one_end_blocked_min (hφ : φ ≠ 0) (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1)
    (j : Fin N) (kT : Fin 3) (hXT : X ∈ (D.tile j).edge kT) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hYT : X + x₀ • u ∈ (D.tile j).edge kT)
    (hint : ∀ x ∈ Ioo (0 : ℝ) x₀, X + x • u ∈ interior D.target.carrier)
    (h0 : ¬ Straddled D.toDissection (-φ) (-c) X)
    (hA : x₀ ≤ dist (D.model.pts 0) (D.model.pts 1)) (hB : x₀ ≤ dist (D.model.pts 1) (D.model.pts 2))
    (hC : x₀ ≤ dist (D.model.pts 0) (D.model.pts 2)) :
    (∃ e ∈ D.toDissection.lineChain (-φ) (-c),
      (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u) ∧ len D.toDissection e = x₀) ∨
    (∃ e ∈ D.toDissection.lineChain (-φ) (-c),
      X + x₀ • u ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ∧
      (X = (D.tile e.1).pts e.2 ∨ X = (D.tile e.1).pts (e.2 + 1))) := by
  have hX0 : X + (0 : ℝ) • u = X := by rw [zero_smul, add_zero]
  have hA0 : (0 : ℝ) < dist (D.model.pts 0) (D.model.pts 1) := lt_of_lt_of_le hx₀ hA
  have hB0 : (0 : ℝ) < dist (D.model.pts 1) (D.model.pts 2) := lt_of_lt_of_le hx₀ hB
  have hC0 : (0 : ℝ) < dist (D.model.pts 0) (D.model.pts 2) := lt_of_lt_of_le hx₀ hC
  rcases one_end_blocked D φ c X u hφ hX hu hu1 j kT hXT hx₀ hYT hint h0 with ⟨hY, -⟩ | ⟨e, he, hYe, s, hs0, hsx, hend, na, nb, nc, hsum⟩
  · left
    have hwall := wall_of_edge D X u j kT hXT hx₀ hYT
    have hsum := wall_sum (D := D.toDissection) (g := -φ) (d := -c) (neg_ne_zero.mpr hφ)
      (fun y => neg_iff y) hφ hX hu hu1 (s := 0) (t := x₀) hx₀.le hint hwall (by rw [hX0]; exact h0) hY
    rw [sub_zero, hX0] at hsum
    -- the sum is positive, so some edge lies inside; each edge is at least `x₀`
    have hne : ((D.toDissection.lineChain (-φ) (-c)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u))).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sum_empty] at hsum
      linarith
    obtain ⟨e, he⟩ := hne
    refine ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2, ?_⟩
    have h1 := Finset.single_le_sum (f := fun e : Fin N × Fin 3 => len D.toDissection e)
      (fun i _ => dist_nonneg) he
    have h2 : ∑ x ∈ (D.toDissection.lineChain (-φ) (-c)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)), len D.toDissection x = x₀ := hsum
    have hle : len D.toDissection e ≤ x₀ := by
      have h3 : len D.toDissection e ≤ ∑ x ∈ (D.toDissection.lineChain (-φ) (-c)).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)), len D.toDissection x := h1
      linarith
    rcases len_mem D e with h | h | h
    · rw [h] at hle ⊢; exact le_antisymm hle hA
    · rw [h] at hle ⊢; exact le_antisymm hle hB
    · rw [h] at hle ⊢; exact le_antisymm hle hC
  · right
    refine ⟨e, he, hYe, ?_⟩
    have hs : s = 0 := small_comb hA0 hB0 hC0 hsum (lt_of_lt_of_le hsx hA) (lt_of_lt_of_le hsx hB)
      (lt_of_lt_of_le hsx hC)
    rw [hs, hX0] at hend
    exact hend

end Wall

end Erdos634.Draft.BlockedEnd

#print axioms Erdos634.Draft.BlockedEnd.blocked_end_quantized
#print axioms Erdos634.Draft.BlockedEnd.one_end_blocked_min
