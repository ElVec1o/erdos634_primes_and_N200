import Mathlib.Tactic
import Erdos634.Draft.GLCHover
import Erdos634.Draft.GLCT4Facts
import Erdos634.Draft.GLCArith2
import Erdos634.Draft.T30LL3SideTile

/-!
# G2, Case 2 (the second tile `T3` on the `b`-side has a `c`-edge on the side): no `γ`-tile with a forward edge at `Q₁`

Pure-geometry core in points `O` (corner), `X` (the `c`-side vertex of the corner tile, `|OX| = c`), `Y` (`|OY| = b`), `Z = Y + (X − O)`, `Q₁ = X + (X − O)`.  Data: the tile `T4 = K_Q` (`α` at `X`, other
vertices `Q₁, Z`), the reflected tile `T2` (carrier `hull{X,Y,Z}`), the tile `T3 = K_P` (`α` at `Y`, `c`-edge along the side ending at `Y + (c/b)(Y−O)`, `b`-edge ending at `Y + (b/c)(X−O)` strictly inside `[Y,Z]`).
Conclusion: no tile `U` has a vertex `Q₁` of angle `γ = 2α` with an edge along the forward ray.
Dichotomy on the far chain of the `a`-edge `[Q₁,Z]` of `T4` (functional `f`):
(N) no far edge crosses `Z`: the chain sums to `a`, `word_a` gives one `a`-edge `[Q₁,Z]`, `GLCFinish.no_gamma_forward`;
(P) some far edge crosses `Z`: then `Z + s(X−O)` is interior to its tile (`hover_of_edge_rel_interior`), the chain on `[Y,Z]` (line `YZ`, `T3`'s side, wall = `T2`) sums to `c`, `word_c` forces `(0,0,1)`, but
`T3`'s `b`-edge `[Y, Yb]` is among its edges: contradiction.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.ChordFar Erdos634.TPErdos Erdos634.LineParam Erdos634.C2Forward
open Erdos634.Pi3F6 Erdos634.Pi3Tile Erdos634.EdgeWordConversion

variable {N : ℕ}

set_option maxHeartbeats 6400000 in
open scoped Classical in
theorem g2_case2 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hb0 : 0 < b) (hbc' : b < c)
    (hsides : ∀ i : Fin 3, sideLen D i = a ∨ sideLen D i = b ∨ sideLen D i = c)
    (hword1 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x = 1 ∧ y = 0 ∧ z = 0)
    (hwordc : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x = 0 ∧ y = 0 ∧ z = 1)
    {O X Y : Plane} (hOX : dist O X = c) (hOY : dist O Y = b)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh0 : h ≠ 0) (hhle : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhO : h O = ch) (hhX : h X = ch) (hhY : h Y < ch)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hgle : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgY : g Y = cg) (hgO : g O = cg) (hgX : g X < cg)
    (hQ1fr : X + (X - O) ∈ frontier D.target.carrier) (hQ1nv : X + (X - O) ∉ Set.range D.target.pts)
    (hintQZ : openSegment ℝ (X + (X - O)) (Y + (X - O)) ⊆ interior D.target.carrier)
    (hintYZ : openSegment ℝ Y (Y + (X - O)) ⊆ interior D.target.carrier)
    (KQ : Fin N) (lQ : Fin 3) (hlQ : (D.tile KQ).pts lQ = X) (hangQ : (D.tile KQ).angleAt lQ = α)
    (hZQ : ((D.tile KQ).pts (lQ + 1) = X + (X - O) ∧ (D.tile KQ).pts (lQ + 2) = Y + (X - O)) ∨
      ((D.tile KQ).pts (lQ + 2) = X + (X - O) ∧ (D.tile KQ).pts (lQ + 1) = Y + (X - O)))
    (j2 : Fin N) (hT2 : (D.tile j2).carrier = convexHull ℝ {X, Y, Y + (X - O)})
    (KP : Fin N) (lP : Fin 3) (hlP : (D.tile KP).pts lP = Y)
    (hKP : ((D.tile KP).pts (lP + 1) = Y + (c / b) • (Y - O) ∧ (D.tile KP).pts (lP + 2) = Y + (b / c) • (X - O)) ∨
      ((D.tile KP).pts (lP + 2) = Y + (c / b) • (Y - O) ∧ (D.tile KP).pts (lP + 1) = Y + (b / c) • (X - O))) :
    ¬ ∃ (U : Fin N) (l : Fin 3), (D.tile U).pts l = X + (X - O) ∧ (D.tile U).angleAt l = 2 * α ∧
      (SameRay ℝ (X - O) ((D.tile U).pts (l + 1) - (X + (X - O))) ∨
       SameRay ℝ (X - O) ((D.tile U).pts (l + 2) - (X + (X - O)))) := by
  rintro ⟨U, l, hU, hUang, hUray⟩
  set Z : Plane := Y + (X - O) with hZdef
  set Q1 : Plane := X + (X - O) with hQ1def
  have hc0 : 0 < c := by linarith
  have hu : X - O ≠ 0 := by
    intro h0
    have : X = O := sub_eq_zero.mp h0
    rw [this, dist_self] at hOX; linarith
  have hnorm_u : ‖X - O‖ = c := by rw [← dist_eq_norm, dist_comm]; exact hOX
  have hnorm_y : ‖Y - O‖ = b := by rw [← dist_eq_norm, dist_comm]; exact hOY
  have hXY : X ≠ Y := by
    intro he; rw [← he] at hOY; linarith
  have hXZ : dist X Z = b := by
    rw [hZdef, dist_eq_norm]
    have : X - (Y + (X - O)) = -(Y - O) := by abel
    rw [this, norm_neg, hnorm_y]
  have e11 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e12 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  have e21 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e22 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  -- facts about `T4`
  obtain ⟨hKQloc, hangZ, hdQZ, -⟩ := T4_Q1_facts D hα hS hab hbc KQ lQ hlQ hangQ (Q1 := Q1) (Z := Z) (u := X - O) rfl hZQ hXZ
  -- supporting functional of `T4` along `[Q₁, Z]`
  obtain ⟨f, c0, hf0, hfle', hf1, hf2, hf3⟩ := exists_supporting (D.tile KQ) (lQ + 1)
  rw [e11] at hf2
  rw [e12, hlQ] at hf3
  have hfle : ∀ m, f ((D.tile KQ).pts m) ≤ c0 := fun m => hfle' _ (subset_convexHull ℝ _ ⟨m, rfl⟩)
  have hfQ1Z : f Q1 = c0 ∧ f Z = c0 := by
    rcases hZQ with ⟨z1, z2⟩ | ⟨z1, z2⟩
    · rw [z1] at hf1; rw [z2] at hf2; exact ⟨hf1, hf2⟩
    · rw [z2] at hf1; rw [z1] at hf2; exact ⟨hf2, hf1⟩
  have hfu : 0 < f (X - O) := by
    have : f Q1 = f X + f (X - O) := by rw [hQ1def, map_add]
    linarith [hfQ1Z.1]
  have hnegf : -f ≠ 0 := neg_ne_zero.mpr hf0
  have hQZne : Q1 ≠ Z := by
    intro he
    apply hXY
    have : X - Y = Q1 - Z := by rw [hQ1def, hZdef]; abel
    rw [← he, sub_self] at this
    exact sub_eq_zero.mp this
  have hwallQZ : ∀ y ∈ openSegment ℝ Q1 Z, ∀ i, y ∉ interior (D.tile i).carrier := by
    obtain ⟨k, hk⟩ := Erdos634.C2Forward.pair_edge (D.tile KQ) (lQ + 1) (lQ + 2) (by
      have := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) lQ; exact this)
    intro y hy
    have hyseg : y ∈ segment ℝ Q1 Z := openSegment_subset_segment ℝ _ _ hy
    rcases hZQ with ⟨z1, z2⟩ | ⟨z1, z2⟩
    · exact Dissection.edge_point_not_interior D.toDissection (j := KQ) (k := k) (by rw [hk, z1, z2]; exact hyseg)
    · exact Dissection.edge_point_not_interior D.toDissection (j := KQ) (k := k)
        (by rw [hk, z1, z2, segment_symm]; exact hyseg)
  by_cases hclaim : ∀ e ∈ D.lineChain (-f) (-c0), (∃ y, y ∈ (D.tile e.1).edge e.2 ∧ y ∈ openSegment ℝ Q1 Z) →
      (D.tile e.1).edge e.2 ⊆ segment ℝ Q1 Z
  · -- (N) no far edge crosses `Z`
    have hsum := chain_sum_open_end' D.toDissection (-f) hnegf (-c0) hQZne (by simp [hfQ1Z.1]) (by simp [hfQ1Z.2])
      hintQZ hwallQZ hclaim
    have hwL : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = dist Q1 Z → x = 1 ∧ y = 0 ∧ z = 0 := by
      rw [hdQZ]; exact hword1
    obtain ⟨hcnt1, -, -⟩ := open_chain_counts D (x0 := 1) (y0 := 0) (z0 := 0) hsides hwL dist_nonneg _ hsum
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcnt1
    have hemem : e ∈ ((D.lineChain (-f) (-c0)).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ Q1 Z)).filter
        (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a) := by
      rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp hemem
    obtain ⟨heC, hesub⟩ := Finset.mem_filter.mp he1
    obtain ⟨hlk, hlk1, hle'⟩ := Dissection.mem_lineChain.mp heC
    have hthird := third_strict (D.tile e.1) (-f) hnegf (-c0) hle' e.2 hlk hlk1
    have hXE : (D.tile e.1).pts e.2 ∈ segment ℝ Q1 Z := hesub (left_mem_segment ℝ _ _)
    have hYE : (D.tile e.1).pts (e.2 + 1) ∈ segment ℝ Q1 Z := hesub (right_mem_segment ℝ _ _)
    have hend := seg_endpoints hQZne hXE hYE (by rw [he2, hdQZ])
    have hne : e.1 ≠ KQ := by
      intro hEq
      have h1 := hfle (e.2 + 2)
      rw [hEq] at hthird
      have h2 : -(f ((D.tile KQ).pts (e.2 + 2))) < -c0 := hthird
      linarith
    exact no_gamma_forward D hα hS hab hac hQ1fr hQ1nv hu hangZ KQ hKQloc e.1 e.2 hend hdQZ hne U l hU hUang hUray
  · -- (P) some far edge crosses `Z`
    push_neg at hclaim
    obtain ⟨e, he, ⟨y, hye, hyo⟩, hns⟩ := hclaim
    obtain ⟨x, hx, hxS⟩ := Set.not_subset.mp hns
    obtain ⟨hlk, hlk1, hle'⟩ := Dissection.mem_lineChain.mp he
    have hthird := third_strict (D.tile e.1) (-f) hnegf (-c0) hle' e.2 hlk hlk1
    have hfx : f x = c0 := by
      have : (-f) x = -c0 := D.lineChain_edge_subset he x hx
      simpa using this
    have hhQ1 : h Q1 = ch := by rw [hQ1def, map_add, map_sub, hhX, hhO]; ring
    have hhZ : h Z = h Y := by rw [hZdef, map_add, map_sub, hhX, hhO]; ring
    have hgl : ∀ τ : ℝ, h (AffineMap.lineMap Q1 Z τ) = ch + τ * (h Z - ch) := by
      intro τ
      simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, map_add, map_smul, map_sub,
        smul_eq_mul, hhQ1]
      ring
    have hxT : x ∈ D.target.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection e.1
      ((D.tile e.1).edge_subset_carrier e.2 hx)
    obtain ⟨t, rfl⟩ := line_eq_lineMap f hf0 c0 hfQ1Z.1 hfQ1Z.2 hQZne hfx
    have ht0 : 0 ≤ t := by
      have := hhle _ hxT
      rw [hgl] at this
      nlinarith
    rw [openSegment_eq_image_lineMap] at hyo
    obtain ⟨ty, ⟨hty0, hty1⟩, rfl⟩ := hyo
    have ht1 : 1 < t := by
      by_contra hle
      push_neg at hle
      exact hxS (by rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht0, hle⟩, rfl⟩)
    have hZmem : Z ∈ openSegment ℝ (AffineMap.lineMap Q1 Z ty) (AffineMap.lineMap Q1 Z t) := by
      have hd : 0 < t - ty := by linarith
      refine ⟨(t - 1) / (t - ty), (1 - ty) / (t - ty), div_pos (by linarith) hd, div_pos (by linarith) hd,
        by field_simp; ring, ?_⟩
      ext i
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
    have hyx : AffineMap.lineMap Q1 Z ty ≠ AffineMap.lineMap Q1 Z t := by
      intro hh
      have := lineMap_injective_of_ne hQZne hh
      linarith
    obtain ⟨hZ0, hZ1⟩ := relint_of_openSegment (D.tile e.1) e.2 (by simpa [Tri.edge] using hye)
      (by simpa [Tri.edge] using hx) hyx hZmem
    have hk0 : f ((D.tile e.1).pts e.2) = c0 := by simpa using hlk
    have hk1 : f ((D.tile e.1).pts (e.2 + 1)) = c0 := by simpa using hlk1
    have hk2 : c0 < f ((D.tile e.1).pts (e.2 + 2)) := by simpa using hthird
    obtain ⟨s0, hs0, hover⟩ := hover_of_edge_rel_interior (D.tile e.1) e.2 f c0 hk0 hk1 hk2 hZ0 hZ1 hfQ1Z.2 hfu
    -- the chain on `[Y, Z]` (line `YZ`, on `T3`'s side; wall = `T2`)
    have hYZne : Y ≠ Z := by
      intro he'
      apply hu
      have : Z - Y = X - O := by rw [hZdef]; abel
      rw [← he', sub_self] at this
      exact this.symm
    have hgZ : g Z < cg := by rw [hZdef, map_add, map_sub, hgY, hgO]; linarith
    have hwallYZ := wall_of_hull_func D.toDissection j2 (P := X) (Q := Y) (Z := Z) hT2 h hh0 (h Y) rfl hhZ
      (by linarith)
    have hlineMap : ∀ s : ℝ, AffineMap.lineMap Y Z (1 + s) = Z + s • (X - O) := by
      intro s
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      rw [hZdef]; module
    obtain ⟨-, hsum2⟩ := chain_sum_open_end D.toDissection h hh0 (h Y) hYZne rfl hhZ g cg hgle hgY hgZ
      hintYZ hwallYZ ⟨s0, hs0, fun s hs hsle => ⟨e.1, by rw [hlineMap]; exact hover s hs hsle⟩⟩
    have hdYZ : dist Y Z = c := by
      rw [hZdef, dist_eq_norm]
      have : Y - (Y + (X - O)) = -(X - O) := by abel
      rw [this, norm_neg, hnorm_u]
    have hwL2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = dist Y Z → x = 0 ∧ y = 0 ∧ z = 1 := by
      rw [hdYZ]; exact hwordc
    obtain ⟨-, hcnt2, -⟩ := open_chain_counts D (x0 := 0) (y0 := 0) (z0 := 1) hsides hwL2 dist_nonneg _ hsum2
    -- `T3`'s `b`-edge `[Y, Yb]`
    have hbcpos : 0 < b / c := div_pos hb0 hc0
    have hYb : Y + (b / c) • (X - O) ∈ segment ℝ Y Z := by
      refine ⟨1 - b / c, b / c, ?_, hbcpos.le, by ring, ?_⟩
      · have : b / c < 1 := (div_lt_one hc0).mpr hbc'
        linarith
      · rw [hZdef]; module
    have hhYb : h (Y + (b / c) • (X - O)) = h Y := by
      rw [map_add, map_smul, map_sub, hhX, hhO]; simp
    have hY3 : h (Y + (c / b) • (Y - O)) ≤ h Y := by
      rw [map_add, map_smul, map_sub, hhO, smul_eq_mul]
      have : 0 < c / b := div_pos hc0 hb0
      nlinarith
    obtain ⟨k3, hk3⟩ : ∃ k3 : Fin 3, ((D.tile KP).pts k3 = Y ∧ (D.tile KP).pts (k3 + 1) = Y + (b / c) • (X - O)) ∨
        ((D.tile KP).pts k3 = Y + (b / c) • (X - O) ∧ (D.tile KP).pts (k3 + 1) = Y) := by
      rcases hKP with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact ⟨lP + 2, Or.inr ⟨k2, by rw [e21]; exact hlP⟩⟩
      · exact ⟨lP, Or.inl ⟨hlP, k2⟩⟩
    have hcov : ∀ m t : Fin 3, t = m ∨ t = m + 1 ∨ t = m + 2 := by decide
    have hle3 : ∀ m : Fin 3, h ((D.tile KP).pts m) ≤ h Y := by
      intro m
      rcases hcov lP m with rfl | rfl | rfl
      · rw [hlP]
      · rcases hKP with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · rw [k1]; exact hY3
        · rw [k2, hhYb]
      · rcases hKP with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · rw [k2, hhYb]
        · rw [k1]; exact hY3
    have hmem3 : ((KP, k3) : Fin N × Fin 3) ∈ D.lineChain h (h Y) := by
      rw [Dissection.mem_lineChain]
      refine ⟨?_, ?_, hle3⟩
      · rcases hk3 with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · show h _ = h Y; rw [k1]
        · show h _ = h Y; rw [k1, hhYb]
      · rcases hk3 with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · show h ((D.tile KP).pts (k3 + 1)) = h Y; rw [k2, hhYb]
        · show h ((D.tile KP).pts (k3 + 1)) = h Y; rw [k2]
    have hsub3 : (D.tile KP).edge k3 ⊆ segment ℝ Y Z := by
      unfold Tri.edge
      rcases hk3 with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · rw [k1, k2]; exact (convex_segment Y Z).segment_subset (left_mem_segment ℝ _ _) hYb
      · rw [k1, k2]; exact (convex_segment Y Z).segment_subset hYb (left_mem_segment ℝ _ _)
    have hlen3 : dist ((D.tile KP).pts k3) ((D.tile KP).pts (k3 + 1)) = b := by
      have hd : dist Y (Y + (b / c) • (X - O)) = b := by
        rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hbcpos, hnorm_u]
        field_simp
      rcases hk3 with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · rw [k1, k2]; exact hd
      · rw [k1, k2, dist_comm]; exact hd
    have hmemS : ((KP, k3) : Fin N × Fin 3) ∈ ((D.lineChain h (h Y)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ Y Z)).filter
        (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ a ∧
          dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem3, hsub3⟩, by rw [hlen3]; exact ⟨hab.symm, rfl⟩⟩
    rw [Finset.card_eq_zero.mp hcnt2] at hmemS
    simp at hmemS

end Erdos634.GLC

#print axioms Erdos634.GLC.g2_case2
