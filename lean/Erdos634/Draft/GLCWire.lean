import Mathlib.Tactic
import Erdos634.Draft.GLCGeom
import Erdos634.Draft.GLCT3
import Erdos634.Draft.GLCFwdEdge

/-!
# Wiring of G2 (Cases 1, 2) to the corner data of a real dissection

`g2_wire`: with the corner tile `T = tile i` (vertex `j` at the target vertex `O = target.pts v`, `X = pts m1` on the ray to `target.pts wX` with `|OX| = c`, `Y = pts m2` on the ray to `target.pts wY` with `|OY| = b`, `|XY| = a`),
the reflected tile `T2` (carrier `hull{X,Y,X+Y−O}`), the second tile `K_Q` on the `c`-side with side edge `c` (the `(c,c)` configuration), the second tile `K_P` on the `b`-side with a side edge along the side
(`b`: Case 1, `T3 = T + (Y−O)`; `c`: Case 2), and `Q₁ = 2X − O`, `Y₂ = 2Y − O` not target vertices: no tile has a vertex `Q₁` of angle `γ` with an edge along the forward ray.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.C2Forward Erdos634.Pi3F6 Erdos634.Pi3Tile Erdos634.EdgeWordConversion

variable {N : ℕ}

set_option maxHeartbeats 6400000 in
open scoped Classical in
theorem g2_wire (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hb0 : 0 < b) (hbc' : b < c)
    (hsides : ∀ i : Fin 3, sideLen D i = a ∨ sideLen D i = b ∨ sideLen D i = c)
    (hword1 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x = 1 ∧ y = 0 ∧ z = 0)
    (hword2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = 2 * a → x = 2 ∧ y = 0 ∧ z = 0)
    (hwordc : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x = 0 ∧ y = 0 ∧ z = 1)
    (i : Fin N) (j : Fin 3) (v wX wY : Fin 3) (hvX : v ≠ wX) (hvY : v ≠ wY) (hXY' : wX ≠ wY)
    (m1 m2 : Fin 3) (hm : (m1 = j + 1 ∧ m2 = j + 2) ∨ (m1 = j + 2 ∧ m2 = j + 1))
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = α)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hXr : (D.tile i).pts m1 - D.target.pts v = r • (D.target.pts wX - D.target.pts v))
    (hYp : (D.tile i).pts m2 - D.target.pts v = p • (D.target.pts wY - D.target.pts v))
    (hOX : dist (D.target.pts v) ((D.tile i).pts m1) = c) (hOY : dist (D.target.pts v) ((D.tile i).pts m2) = b)
    (hXYa : dist ((D.tile i).pts m1) ((D.tile i).pts m2) = a)
    (j2 : Fin N) (hT2 : (D.tile j2).carrier = convexHull ℝ {(D.tile i).pts m1, (D.tile i).pts m2,
      (D.tile i).pts m1 + (D.tile i).pts m2 - D.target.pts v})
    (KQ : Fin N) (lQ : Fin 3) (hQpt : (D.tile KQ).pts lQ = (D.tile i).pts m1) (hQang : (D.tile KQ).angleAt lQ = α)
    (hQray : (SameRay ℝ ((D.tile i).pts m1 - D.target.pts v) ((D.tile KQ).pts (lQ + 1) - (D.tile i).pts m1) ∧
        dist ((D.tile i).pts m1) ((D.tile KQ).pts (lQ + 1)) = c) ∨
      (SameRay ℝ ((D.tile i).pts m1 - D.target.pts v) ((D.tile KQ).pts (lQ + 2) - (D.tile i).pts m1) ∧
        dist ((D.tile i).pts m1) ((D.tile KQ).pts (lQ + 2)) = c))
    (KP : Fin N) (lP : Fin 3) (hPpt : (D.tile KP).pts lP = (D.tile i).pts m2) (hPang : (D.tile KP).angleAt lP = α)
    (hPray : (SameRay ℝ ((D.tile i).pts m2 - D.target.pts v) ((D.tile KP).pts (lP + 1) - (D.tile i).pts m2)) ∨
      (SameRay ℝ ((D.tile i).pts m2 - D.target.pts v) ((D.tile KP).pts (lP + 2) - (D.tile i).pts m2)))
    (hQ1v : ∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts v))
    (hY2v : ∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m2 + ((D.tile i).pts m2 - D.target.pts v)) :
    (¬ ∃ (U : Fin N) (l : Fin 3), (D.tile U).pts l = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts v) ∧
      (D.tile U).angleAt l = 2 * α ∧
      (SameRay ℝ ((D.tile i).pts m1 - D.target.pts v)
          ((D.tile U).pts (l + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts v))) ∨
       SameRay ℝ ((D.tile i).pts m1 - D.target.pts v)
          ((D.tile U).pts (l + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts v))))) ∧
    ∃ (K' : Fin N) (l' : Fin 3), (D.tile K').pts l' = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts v) ∧
      (D.tile K').angleAt l' = α ∧
      (SameRay ℝ ((D.tile i).pts m1 - D.target.pts v)
          ((D.tile K').pts (l' + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts v))) ∨
       SameRay ℝ ((D.tile i).pts m1 - D.target.pts v)
          ((D.tile K').pts (l' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts v)))) := by
  have hpi := Real.pi_pos
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D hS
  set T := D.target with hT
  set O : Plane := T.pts v with hO
  set X : Plane := (D.tile i).pts m1 with hXdef
  set Y : Plane := (D.tile i).pts m2 with hYdef
  have hc0 : 0 < c := by linarith
  have hcb : 1 < c / b := by rw [one_lt_div hb0]; exact hbc'
  have hnorm_u : ‖X - O‖ = c := by rw [← dist_eq_norm, dist_comm]; exact hOX
  have hnorm_y : ‖Y - O‖ = b := by rw [← dist_eq_norm, dist_comm]; exact hOY
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  -- coordinates of `X, Y` in the frame `(O; A = target.pts wY, B = target.pts wX)`
  have hXc : X = T.pts v + (0 : ℝ) • (T.pts wY - T.pts v) + r • (T.pts wX - T.pts v) := by
    rw [zero_smul, add_zero, ← hXr]; abel
  have hYc : Y = T.pts v + p • (T.pts wY - T.pts v) + (0 : ℝ) • (T.pts wX - T.pts v) := by
    rw [zero_smul, add_zero, ← hYp]; abel
  have hQ1c : X + (X - O) = T.pts v + (0 : ℝ) • (T.pts wY - T.pts v) + (2 * r) • (T.pts wX - T.pts v) := by
    have : X + (X - O) = O + (2 : ℝ) • (X - O) := by module
    rw [this, hXr, zero_smul, add_zero, smul_smul]
  have hZc : Y + (X - O) = T.pts v + p • (T.pts wY - T.pts v) + r • (T.pts wX - T.pts v) := by
    have : Y + (X - O) = O + (Y - O) + (X - O) := by abel
    rw [this, hYp, hXr]
  have hY2c : Y + (Y - O) = T.pts v + (2 * p) • (T.pts wY - T.pts v) + (0 : ℝ) • (T.pts wX - T.pts v) := by
    have : Y + (Y - O) = O + (2 : ℝ) • (Y - O) := by module
    rw [this, hYp, zero_smul, add_zero, smul_smul]
  -- the two side functionals
  obtain ⟨h, ch, hh0, hhle, hhv, hhwX, hhwY⟩ := supp_pair T v wX wY hvX hvY hXY'
  obtain ⟨g, cg, hg0, hgle, hgv, hgwY, hgwX⟩ := supp_pair T v wY wX hvY hvX hXY'.symm
  have hhX : h X = ch := by
    rw [hXc, map_add, map_add, map_smul, map_smul, map_sub, map_sub, hhv, hhwX]; simp
  have hhY : h Y < ch := by
    rw [hYc, map_add, map_add, map_smul, map_smul, map_sub, map_sub, hhv]
    simp only [smul_eq_mul]; nlinarith [mul_pos hp0 (sub_pos.mpr hhwY)]
  have hgY : g Y = cg := by
    rw [hYc, map_add, map_add, map_smul, map_smul, map_sub, map_sub, hgv, hgwY]; simp
  have hgX : g X < cg := by
    rw [hXc, map_add, map_add, map_smul, map_smul, map_sub, map_sub, hgv]
    simp only [smul_eq_mul]; nlinarith [mul_pos hr0 (sub_pos.mpr hgwX)]
  have hhO : h O = ch := hhv
  have hgO : g O = cg := hgv
  -- `T4 = K_Q`
  obtain ⟨hQ1', hQ2'⟩ := T4_tile_side D hα hS i j hang m1 m2 hm KQ lQ hQpt hQang h ch hhle hhX
    (by rw [hjv]; exact hhO) hhY
  rw [hjv] at hQ1' hQ2'
  have hZQ : ((D.tile KQ).pts (lQ + 1) = X + (X - O) ∧ (D.tile KQ).pts (lQ + 2) = Y + (X - O)) ∨
      ((D.tile KQ).pts (lQ + 2) = X + (X - O) ∧ (D.tile KQ).pts (lQ + 1) = Y + (X - O)) := by
    rcases hQray with ⟨hr1, hd1⟩ | ⟨hr2, hd2⟩
    · have := hQ1' hr1 (by rw [hd1]; exact hOX.symm)
      refine Or.inl ⟨this.1, ?_⟩
      rw [this.2]; abel
    · have := hQ2' hr2 (by rw [hd2]; exact hOX.symm)
      refine Or.inr ⟨this.1, ?_⟩
      rw [this.2]; abel
  have hQ1mem : X + (X - O) ∈ T.carrier := by
    rcases hZQ with ⟨z1, -⟩ | ⟨z1, -⟩
    · rw [← z1]
      exact Erdos634.BaseSelection.tile_subset_target D.toDissection KQ (subset_convexHull ℝ _ ⟨lQ + 1, rfl⟩)
    · rw [← z1]
      exact Erdos634.BaseSelection.tile_subset_target D.toDissection KQ (subset_convexHull ℝ _ ⟨lQ + 2, rfl⟩)
  have hr2 : 2 * r ≤ 1 := by
    have hmem := hQ1mem
    rw [T.carrier_eq_nonneg_coord] at hmem
    have := hmem v
    rw [hQ1c, tri_coords T v wY wX hvY hvX hXY'.symm] at this
    simp [hvY, hvX] at this
    linarith
  have hr2' : 2 * r < 1 := by
    rcases lt_or_eq_of_le hr2 with h' | h'
    · exact h'
    · exfalso
      apply hQ1v wX
      rw [hQ1c, h']; simp
  -- `K_P`: the side edge is `b` (Case 1, `T3 = T + (Y − O)`) or `c` (Case 2)
  have hKt := edges_at_alpha hα (tile_twoalpha D hS KP) hab hac lP hPang
  rw [hPpt] at hKt
  have hm' : (m2 = j + 1 ∧ m1 = j + 2) ∨ (m2 = j + 2 ∧ m1 = j + 1) := by
    rcases hm with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inr ⟨a2, a1⟩
    · exact Or.inl ⟨a2, a1⟩
  obtain ⟨hP1', hP2'⟩ := T4_tile_side D hα hS i j hang m2 m1 hm' KP lP hPpt hPang g cg hgle hgY
    (by rw [hjv]; exact hgO) hgX
  rw [hjv] at hP1' hP2'
  obtain ⟨hT3a, hT3b⟩ := T3_tile_side D hα hS i j hang m2 m1 hm' KP lP hPpt hPang g cg hgle hgY
    (by rw [hjv]; exact hgv) hgX
  rw [hjv] at hT3a hT3b
  rw [hnorm_u, hnorm_y] at hT3a hT3b
  have hP3 : (((D.tile KP).pts (lP + 1) = Y + (Y - O) ∧ (D.tile KP).pts (lP + 2) = Y + (X - O)) ∨
        ((D.tile KP).pts (lP + 2) = Y + (Y - O) ∧ (D.tile KP).pts (lP + 1) = Y + (X - O))) ∨
      (((D.tile KP).pts (lP + 1) = Y + (c / b) • (Y - O) ∧ (D.tile KP).pts (lP + 2) = Y + (b / c) • (X - O)) ∨
        ((D.tile KP).pts (lP + 2) = Y + (c / b) • (Y - O) ∧ (D.tile KP).pts (lP + 1) = Y + (b / c) • (X - O))) := by
    rcases hPray with hr1 | hr2
    · rcases hKt with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have := hT3a hr1 (by rw [e1, hOX])
        exact Or.inr (Or.inl this)
      · have := hP1' hr1 (by rw [e1, hOY])
        refine Or.inl (Or.inl ⟨this.1, ?_⟩)
        rw [this.2]; abel
    · rcases hKt with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have := hP2' hr2 (by rw [e2, hOY])
        refine Or.inl (Or.inr ⟨this.1, ?_⟩)
        rw [this.2]; abel
      · have := hT3b hr2 (by rw [e2, hOX])
        exact Or.inr (Or.inr this)
  -- `2p < 1`
  have hp2 : 2 * p < 1 := by
    rcases hP3 with hC1 | hC2
    · have hY2mem : Y + (Y - O) ∈ T.carrier := by
        rcases hC1 with ⟨z1, -⟩ | ⟨z1, -⟩
        · rw [← z1]
          exact Erdos634.BaseSelection.tile_subset_target D.toDissection KP (subset_convexHull ℝ _ ⟨lP + 1, rfl⟩)
        · rw [← z1]
          exact Erdos634.BaseSelection.tile_subset_target D.toDissection KP (subset_convexHull ℝ _ ⟨lP + 2, rfl⟩)
      have hmem := hY2mem
      rw [T.carrier_eq_nonneg_coord] at hmem
      have := hmem v
      rw [hY2c, tri_coords T v wY wX hvY hvX hXY'.symm] at this
      simp [hvY, hvX] at this
      rcases lt_or_eq_of_le (by linarith : 2 * p ≤ 1) with h' | h'
      · exact h'
      · exfalso
        apply hY2v wY
        rw [hY2c, h']; simp
    · have hY3mem : Y + (c / b) • (Y - O) ∈ T.carrier := by
        rcases hC2 with ⟨z1, -⟩ | ⟨z1, -⟩
        · rw [← z1]
          exact Erdos634.BaseSelection.tile_subset_target D.toDissection KP (subset_convexHull ℝ _ ⟨lP + 1, rfl⟩)
        · rw [← z1]
          exact Erdos634.BaseSelection.tile_subset_target D.toDissection KP (subset_convexHull ℝ _ ⟨lP + 2, rfl⟩)
      have hmem := hY3mem
      rw [T.carrier_eq_nonneg_coord] at hmem
      have := hmem v
      have e3 : Y + (c / b) • (Y - O) = T.pts v + (p * (1 + c / b)) • (T.pts wY - T.pts v)
          + (0 : ℝ) • (T.pts wX - T.pts v) := by
        have : Y + (c / b) • (Y - O) = O + (1 + c / b) • (Y - O) := by module
        rw [this, hYp, zero_smul, add_zero, smul_smul]; congr 2; ring
      rw [e3, tri_coords T v wY wX hvY hvX hXY'.symm] at this
      simp [hvY, hvX] at this
      nlinarith
  have hp1 : p < 1 := by linarith
  -- non-vertex frontier point `Q₁`
  obtain ⟨-, -, -, hfrQ, hnvQ, -, -⟩ := clamps T v wX wY hvX hvY hXY' (p := 2 * r) (r := p) (by positivity) hr2' hp0 hp1
  have hQ1e : X + (X - O) = (1 - 2 * r) • T.pts v + (2 * r) • T.pts wX := by rw [hQ1c]; module
  have hQ1fr : X + (X - O) ∈ frontier T.carrier := by rw [hQ1e]; exact hfrQ
  have hQ1nv : X + (X - O) ∉ Set.range T.pts := by rw [hQ1e]; exact hnvQ
  have hFrame := openSeg_interior3 T v wY wX hvY hvX hXY'.symm
  have hintQZ : openSegment ℝ (X + (X - O)) (Y + (X - O)) ⊆ interior T.carrier := by
    rw [hQ1c, hZc]
    exact hFrame 0 (2 * r) p r (by linarith) le_rfl (by positivity) (by linarith) hp0.le hr0.le
      (Or.inl (by linarith)) (Or.inr hp0) (Or.inl (by positivity))
  have hintYZ : openSegment ℝ Y (Y + (X - O)) ⊆ interior T.carrier := by
    rw [hZc]; nth_rewrite 1 [hYc]
    exact hFrame p 0 p r (by linarith) hp0.le le_rfl (by linarith) hp0.le hr0.le
      (Or.inl (by linarith)) (Or.inl hp0) (Or.inr hr0)
  have hintC : openSegment ℝ (X + (X - O)) (Y + (Y - O)) ⊆ interior T.carrier := by
    rw [hQ1c, hY2c]
    exact hFrame 0 (2 * r) (2 * p) 0 (by linarith) le_rfl (by positivity) (by linarith) (by positivity) le_rfl
      (Or.inl (by linarith)) (Or.inr (by positivity)) (Or.inl (by positivity))
  have hZeq : (D.tile i).pts m1 + (D.tile i).pts m2 - O = Y + (X - O) := by
    show X + Y - O = Y + (X - O)
    abel
  have hneg : ¬ ∃ (U : Fin N) (l : Fin 3), (D.tile U).pts l = X + (X - O) ∧ (D.tile U).angleAt l = 2 * α ∧
      (SameRay ℝ (X - O) ((D.tile U).pts (l + 1) - (X + (X - O))) ∨
       SameRay ℝ (X - O) ((D.tile U).pts (l + 2) - (X + (X - O)))) := by
    rcases hP3 with hC1 | hC2
    · exact g2_case1 D hα hS hab hac hbc hb0 hbc' hsides hword2 hOX hOY hXYa h ch hh0 hhle hhO hhX hhY g cg hgle
        hgY hgO hgX hQ1fr hQ1nv hintC KQ lQ hQpt hQang hZQ KP lP hPpt hC1
    · have hT2' := hT2
      rw [hZeq] at hT2'
      exact g2_case2 D hα hS hab hac hbc hb0 hbc' hsides hword1 hwordc hOX hOY h ch hh0 hhle hhO hhX hhY g cg hgle
        hgY hgO hgX hQ1fr hQ1nv hintQZ hintYZ KQ lQ hQpt hQang hZQ j2 hT2' KP lP hPpt hC2
  refine ⟨hneg, ?_⟩
  -- positive form: the tile at `Q₁` with a forward edge presents `α`
  have hXZ : dist X (Y + (X - O)) = b := by
    have : X - (Y + (X - O)) = -(Y - O) := by abel
    rw [dist_eq_norm, this, norm_neg, hnorm_y]
  have hu : X - O ≠ 0 := by
    intro h0
    have : ‖X - O‖ = 0 := by rw [h0, norm_zero]
    rw [hnorm_u] at this; linarith
  obtain ⟨hKQloc, -, -, -⟩ := T4_Q1_facts D hα hS hab hbc KQ lQ hQpt hQang (Q1 := X + (X - O))
    (Z := Y + (X - O)) (u := X - O) rfl hZQ hXZ
  have hhQ1 : h (X + (X - O)) = ch := by rw [map_add, map_sub, hhX, hhO]; ring
  have hhu : h (X - O) = 0 := by rw [map_sub, hhX, hhO]; ring
  have hnβ : ∀ ε : ℝ, 0 < ε → ε ≤ (1 - 2 * r) / r → X + (X - O) + ε • (X - O) ∉ (D.tile KQ).carrier := by
    intro ε hε _
    have e : X + (X - O) - X = X - O := by abel
    rcases hZQ with ⟨z1, z2⟩ | ⟨z1, z2⟩
    · have := fwd_not_mem (D.tile KQ) lQ (lQ + 1) (lQ + 1) ((by decide : ∀ x : Fin 3, x ≠ x + 1) lQ)
        ((by decide : ∀ x : Fin 3, x ≠ x + 1) lQ) hε
      rw [z1, hQpt, e] at this
      exact this
    · have := fwd_not_mem (D.tile KQ) lQ (lQ + 2) (lQ + 2) ((by decide : ∀ x : Fin 3, x ≠ x + 2) lQ)
        ((by decide : ∀ x : Fin 3, x ≠ x + 2) lQ) hε
      rw [z1, hQpt, e] at this
      exact this
  have hε0 : 0 < (1 - 2 * r) / r := div_pos (by linarith) hr0
  have hin : ∀ ε : ℝ, 0 < ε → ε ≤ (1 - 2 * r) / r → X + (X - O) + ε • (X - O) ∈ D.target.carrier := by
    intro ε hε hεle
    have hre : r * ε ≤ 1 - 2 * r := by rwa [le_div_iff₀ hr0, mul_comm] at hεle
    have hconv : Convex ℝ T.carrier := by unfold Tri.carrier; exact convex_convexHull ℝ _
    have key := hconv.add_smul_sub_mem (subset_convexHull ℝ _ ⟨v, rfl⟩ : T.pts v ∈ T.carrier)
      (subset_convexHull ℝ _ ⟨wX, rfl⟩ : T.pts wX ∈ T.carrier) (t := r * (2 + ε))
      ⟨by positivity, by nlinarith⟩
    convert key using 1
    have e1 : X + (X - O) + ε • (X - O) = O + (2 + ε) • (X - O) := by module
    rw [e1, hXr]; module
  obtain ⟨K', l', hl', hang', hray'⟩ := forward_edge_2a D hα hS (P := X + (X - O)) (u := X - O) hQ1fr hQ1nv hu
    h hh0 ch hhle hhQ1 hhu hε0 hin KQ hKQloc hnβ
  rcases hang' with h' | h'
  · exact ⟨K', l', hl', h', hray'⟩
  · exact absurd ⟨K', l', hl', h', hray'⟩ hneg

end Erdos634.GLC

#print axioms Erdos634.GLC.g2_wire
