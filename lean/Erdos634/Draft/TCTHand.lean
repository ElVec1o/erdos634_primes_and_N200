-- No sorry, no native_decide.
-- Applies `TraceCovering.wall_sum` and `TraceCovering.trace_covering` at a real T-junction: the hand-built
-- bare `Dissection 3` of `TJCHand` (T = (0,0),(4,0),(0,4); P = (0,0),(2,0),(1,2); Q = (0,0),(1,2),(0,4);
-- R = (2,0),(4,0),(0,4)).  The line is `2x + y = 4` (R's long edge (0,4)-(2,0)); the T-junction vertex is
-- (1,2): a vertex of Q and P (near side `{2x+y ≤ 4}`: edges Q1 = (1,2)-(0,4), P1 = (2,0)-(1,2)) and an
-- interior point of R's edge 2 (far side: one edge (0,4)-(2,0)).  Parametrization X = (0,4),
-- u = (1,-2)/√5, so X + x•u = ((x/√5), 4 - 2x/√5); (1,2) is at x = √5, (2,0) at x = 2√5.
import Erdos634.Draft.TJCHandApp
import Erdos634.Draft.TraceCovering

namespace Erdos634.Draft.TCT

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.Draft.TJCHand
  Erdos634.Draft.TJCHandApp Erdos634.Draft.TraceCovering Set

noncomputable def r : ℝ := Real.sqrt 5

theorem r_sq : r ^ 2 = 5 := Real.sq_sqrt (by norm_num)
theorem r_pos : 0 < r := Real.sqrt_pos.mpr (by norm_num)

noncomputable def X0 : Plane := mkPt 0 4
noncomputable def uu : Plane := mkPt (1 / r) (-(2 / r))
/-- the line functional `2x + y` and the near-side chain level `4` -/
noncomputable def F : Plane →ₗ[ℝ] ℝ := lin 2 1

theorem F_ne : F ≠ 0 := lin_ne_zero (Or.inl (by norm_num))
theorem F_X : F X0 = 4 := by simp [F, X0]
theorem F_u : F uu = 0 := by simp [F, uu]; ring

theorem uu_norm : ‖uu‖ = 1 := by
  rw [uu, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]
  have := r_sq
  have h0 := r_pos.ne'
  field_simp
  nlinarith

theorem pt_eq (x : ℝ) : X0 + x • uu = mkPt (x / r) (4 - 2 * x / r) := by
  rw [X0, uu, mkPt_smul, mkPt_add]
  congr 1 <;> ring

theorem pt_r : X0 + r • uu = mkPt 1 2 := by
  rw [pt_eq]; have := r_pos.ne'
  congr 1 <;> field_simp <;> norm_num

theorem pt_2r : X0 + (2 * r) • uu = mkPt 2 0 := by
  rw [pt_eq]; have := r_pos.ne'
  congr 1 <;> field_simp <;> norm_num

theorem pt_0 : X0 + (0 : ℝ) • uu = mkPt 0 4 := by
  rw [pt_eq]; congr 1 <;> simp

theorem openSeg_mk {a b c d : ℝ} {z : Plane} (h : z ∈ openSegment ℝ (mkPt a b) (mkPt c d)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = mkPt ((1 - t) * a + t * c) ((1 - t) * b + t * d) := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  refine ⟨q, hq, by linarith, ?_⟩
  have : p = 1 - q := by linarith
  subst this
  rw [mkPt_smul, mkPt_smul, mkPt_add]

/-! ## the two chains, computed -/

theorem chain_near : D.lineChain F 4 = {((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (1 : Fin 3))} := by
  ext ⟨i, k⟩
  rw [Dissection.mem_lineChain]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  fin_cases i <;> fin_cases k <;>
    simp [F, D_tile, tile, P, Q, R, Fin.forall_fin_succ] <;> norm_num

theorem chain_far : D.lineChain (-F) (-4) = {((2 : Fin 3), (2 : Fin 3))} := by
  ext ⟨i, k⟩
  rw [Dissection.mem_lineChain]
  simp only [Finset.mem_singleton, Prod.mk.injEq]
  fin_cases i <;> fin_cases k <;>
    simp [F, D_tile, tile, P, Q, R, Fin.forall_fin_succ] <;> norm_num

/-! ## Straddling, in the parameter `x` -/

theorem straddled_near_imp (x : ℝ) (h : Straddled D F 4 (X0 + x • uu)) :
    (0 < x ∧ x < r) ∨ (r < x ∧ x < 2 * r) := by
  obtain ⟨⟨i, k⟩, he, hx⟩ := h
  rw [chain_near] at he
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at he
  have hr := r_pos; have hr0 := hr.ne'
  rw [pt_eq] at hx
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- P edge 1 = (2,0)-(1,2)
    have hx' : mkPt (x / r) (4 - 2 * x / r) ∈ openSegment ℝ (mkPt 2 0) (mkPt 1 2) := by
      simpa [D_tile, tile, P] using hx
    obtain ⟨t, ht0, ht1, e⟩ := openSeg_mk hx'
    have := (mkPt_inj e).1
    right
    have h2 : x / r = 2 - t := by linarith
    have h3 : 1 < x / r := by linarith
    have h4 : x / r < 2 := by linarith
    rw [lt_div_iff₀ hr] at h3
    rw [div_lt_iff₀ hr] at h4
    constructor <;> linarith
  · -- Q edge 1 = (1,2)-(0,4)
    have hx' : mkPt (x / r) (4 - 2 * x / r) ∈ openSegment ℝ (mkPt 1 2) (mkPt 0 4) := by
      simpa [D_tile, tile, Q] using hx
    obtain ⟨t, ht0, ht1, e⟩ := openSeg_mk hx'
    have := (mkPt_inj e).1
    left
    constructor
    · have : 0 < x / r := by nlinarith
      exact (div_pos_iff_of_pos_right hr).mp this
    · have : x / r < 1 := by nlinarith
      rw [div_lt_iff₀ hr] at this; linarith

theorem straddled_far_iff (x : ℝ) : Straddled D (-F) (-4) (X0 + x • uu) ↔ 0 < x ∧ x < 2 * r := by
  have hr := r_pos; have hr0 := hr.ne'
  unfold Straddled
  rw [chain_far]
  simp only [Finset.mem_singleton, exists_eq_left, D_tile, tile, R]
  rw [pt_eq]
  show _ ∈ openSegment ℝ (mkPt 0 4) (mkPt 2 0) ↔ _
  constructor
  · intro hx
    obtain ⟨t, ht0, ht1, e⟩ := openSeg_mk hx
    have h1 := (mkPt_inj e).1
    have h2 : x / r = 2 * t := by linarith
    have : 0 < x / r := by rw [h2]; linarith
    have h3 : x / r < 2 := by rw [h2]; linarith
    refine ⟨(div_pos_iff_of_pos_right hr).mp this, ?_⟩
    rw [div_lt_iff₀ hr] at h3; linarith
  · rintro ⟨h0, h1⟩
    have := mkPt_mem_openSegment 0 4 2 0 (x / (2 * r)) (by positivity)
      (by rw [div_lt_one (by positivity)]; exact h1)
    convert this using 2 <;> field_simp <;> ring

/-! ## hypotheses of the two theorems, from coordinates -/

theorem F_pt (x : ℝ) : F (X0 + x • uu) = 4 := by
  rw [map_add, map_smul, F_X, F_u]; simp

theorem hint_all (x : ℝ) (hx : x ∈ Ioo 0 (2 * r)) :
    X0 + x • uu ∈ interior D.target.carrier := by
  have hr := r_pos
  rw [D_target, pt_eq]
  have h1 : 0 < x / r := div_pos hx.1 hr
  have h2 : x / r < 2 := by rw [div_lt_iff₀ hr]; linarith [hx.2]
  have h3 : 2 * x / r = 2 * (x / r) := by ring
  exact T_interior _ _ h1 (by linarith) (by linarith)

theorem hwall_all (x : ℝ) (hx : x ∈ Ioo 0 (2 * r)) (i : Fin 3) :
    X0 + x • uu ∉ interior (D.tile i).carrier := by
  intro hyi
  have hfy := F_pt x
  fin_cases i
  · refine not_interior_on_line F_ne (c := 4) (A := (D.tile 0).carrier) ?_ hyi hfy
    refine carrier_le (D.tile 0) (f := F) (c := 4) ?_
    intro k; fin_cases k <;> simp [F, D_tile, tile, P] <;> norm_num
  · refine not_interior_on_line F_ne (c := 4) (A := (D.tile 1).carrier) ?_ hyi hfy
    refine carrier_le (D.tile 1) (f := F) (c := 4) ?_
    intro k; fin_cases k <;> simp [F, D_tile, tile, Q] <;> norm_num
  · refine not_interior_on_line_ge F_ne (c := 4) (A := (D.tile 2).carrier) ?_ hyi hfy
    refine carrier_ge (D.tile 2) (f := F) (c := 4) ?_
    intro k; fin_cases k <;> simp [F, D_tile, tile, R] <;> norm_num

theorem near_not_at (x : ℝ) (hx : x = 0 ∨ x = r ∨ x = 2 * r) : ¬ Straddled D F 4 (X0 + x • uu) := by
  intro h
  have hr := r_pos
  rcases straddled_near_imp x h with h | h <;> rcases hx with rfl | rfl | rfl <;> linarith [h.1, h.2]

theorem far_not_at (x : ℝ) (hx : x = 0 ∨ x = 2 * r) : ¬ Straddled D (-F) (-4) (X0 + x • uu) := by
  intro h
  have hr := r_pos
  have := (straddled_far_iff x).mp h
  rcases hx with rfl | rfl <;> linarith [this.1, this.2]

/-- THE T-JUNCTION: the point (1,2) = X + √5•u is a vertex of Q and P (the near chain does NOT pass through
it) and an interior point of R's edge 2 (the far chain DOES). -/
theorem tjunction_one_sided :
    X0 + r • uu = mkPt 1 2 ∧ ¬ Straddled D F 4 (X0 + r • uu) ∧ Straddled D (-F) (-4) (X0 + r • uu) := by
  refine ⟨pt_r, near_not_at r (Or.inr (Or.inl rfl)), ?_⟩
  exact (straddled_far_iff r).mpr ⟨r_pos, by linarith [r_pos]⟩

/-! ## distances -/

theorem dist_mk (a b c d : ℝ) :
    dist (mkPt a b) (mkPt c d) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq]; simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem d_Q1 : dist (mkPt 1 2) (mkPt 0 4) = r := by rw [dist_mk]; unfold r; norm_num
theorem d_P1 : dist (mkPt 2 0) (mkPt 1 2) = r := by rw [dist_mk]; unfold r; norm_num
theorem d_R2 : dist (mkPt 0 4) (mkPt 2 0) = 2 * r := by
  rw [dist_mk, show ((0:ℝ) - 2) ^ 2 + (4 - 0) ^ 2 = (2 * r) ^ 2 by nlinarith [r_sq]]
  exact Real.sqrt_sq (by linarith [r_pos])

/-! ## segments -/

theorem m12_mem : mkPt 1 2 ∈ segment ℝ (mkPt 0 4) (mkPt 2 0) := by
  have := mkPt_mem_segment 0 4 2 0 (1/2) (by norm_num) (by norm_num)
  have e : mkPt (1 : ℝ) 2 = mkPt ((1 - 1/2) * 0 + 1/2 * 2) ((1 - 1/2) * 4 + 1/2 * 0) := by norm_num
  rw [e]; exact this

theorem seg_full : segment ℝ X0 (X0 + (2 * r) • uu) = segment ℝ (mkPt 0 4) (mkPt 2 0) := by
  rw [pt_2r]; rfl

open Classical in
theorem filter_near_full :
    (D.lineChain F 4).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X0 (X0 + (2 * r) • uu)) =
      {((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (1 : Fin 3))} := by
  rw [chain_near]
  apply Finset.filter_true_of_mem
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rw [seg_full]
  rcases he with rfl | rfl
  · show segment ℝ (mkPt 2 0) (mkPt 1 2) ⊆ _
    exact (convex_segment _ _).segment_subset (right_mem_segment ℝ _ _) m12_mem
  · show segment ℝ (mkPt 1 2) (mkPt 0 4) ⊆ _
    exact (convex_segment _ _).segment_subset m12_mem (left_mem_segment ℝ _ _)

open Classical in
theorem filter_far_full :
    (D.lineChain (-F) (-4)).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X0 (X0 + (2 * r) • uu)) =
      {((2 : Fin 3), (2 : Fin 3))} := by
  rw [chain_far]
  apply Finset.filter_true_of_mem
  intro e he
  simp only [Finset.mem_singleton] at he
  subst he
  rw [seg_full]
  exact fun y hy => hy

/-! ## TRACE COVERING at the T-junction -/

open Classical in
/-- `trace_covering` applied from X = (0,4) along the line `2x + y = 4`, seed edge Q1 = [X, X + √5•u].
All hypotheses proved from coordinates.  Conclusion extracted: the first common junction is x₀ = 2√5 = L
(the T-junction (1,2) at x = √5 is NOT common: R's edge passes through it), the near-side covering word is
{P1, Q1} (two edges), the far-side word is {R2} (one edge), and both have total length x₀. -/
theorem tct_trace_covering :
    ∃ x₀ : ℝ, x₀ = 2 * r ∧ r ≤ x₀ ∧
      (∀ y ∈ Ioo 0 x₀, Straddled D F 4 (X0 + y • uu) ∨ Straddled D (-F) (-4) (X0 + y • uu)) ∧
      (D.lineChain F 4).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X0 (X0 + x₀ • uu)) =
        {((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (1 : Fin 3))} ∧
      (D.lineChain (-F) (-4)).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X0 (X0 + x₀ • uu)) =
        {((2 : Fin 3), (2 : Fin 3))} ∧
      ∑ e ∈ (D.lineChain F 4).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X0 (X0 + x₀ • uu)),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = x₀ ∧
      ∑ e ∈ (D.lineChain (-F) (-4)).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X0 (X0 + x₀ • uu)),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = x₀ := by
  have hr := r_pos
  have h0n : ¬ Straddled D F 4 X0 := by
    have := near_not_at 0 (Or.inl rfl); rwa [zero_smul, add_zero] at this
  have h0f : ¬ Straddled D (-F) (-4) X0 := by
    have := far_not_at 0 (Or.inl rfl); rwa [zero_smul, add_zero] at this
  obtain ⟨x₀, hl, hL, hn, hf', hcov, hs1, hs2⟩ := trace_covering (D := D) (X := X0) (u := uu)
    (f := F) (c := 4) F_ne F_X F_u uu_norm (ℓ := r) (L := 2 * r) hr (by linarith) hint_all
    ⟨h0n, h0f⟩ ⟨near_not_at _ (Or.inr (Or.inr rfl)), far_not_at _ (Or.inr rfl)⟩
    ⟨((1 : Fin 3), (1 : Fin 3)), by rw [chain_near]; simp, by
      show segment ℝ (mkPt 1 2) (mkPt 0 4) = _
      rw [pt_r, segment_symm]; rfl⟩
  have hx : x₀ = 2 * r := by
    by_contra hne
    exact hf' ((straddled_far_iff x₀).mpr ⟨by linarith, lt_of_le_of_ne hL hne⟩)
  subst hx
  refine ⟨_, rfl, hl, hcov, filter_near_full, filter_far_full, hs1, hs2⟩

/-- by-hand check of the sums in `tct_trace_covering`: √5 + √5 = 2√5 and the single far edge has length 2√5. -/
theorem tct_trace_covering_byhand :
    dist (mkPt 1 2) (mkPt 0 4) + dist (mkPt 2 0) (mkPt 1 2) = 2 * r ∧ dist (mkPt 0 4) (mkPt 2 0) = 2 * r := by
  rw [d_Q1, d_P1, d_R2]; exact ⟨by ring, rfl⟩

/-- With `L = √5` the end point is the T-junction (1,2), which is straddled from the far side, so the hypothesis `hend` of `trace_covering` fails. -/
theorem tct_trace_covering_negative :
    ¬ (¬ Straddled D F 4 (X0 + r • uu) ∧ ¬ Straddled D (-F) (-4) (X0 + r • uu)) :=
  fun h => h.2 tjunction_one_sided.2.2

/-! ## WALL_SUM at the T-junction: sub-stretches cut at (1,2) -/

theorem ioo_sub {s t : ℝ} (h0 : 0 ≤ s) (h1 : t ≤ 2 * r) : ∀ x ∈ Ioo s t, x ∈ Ioo 0 (2 * r) :=
  fun x hx => ⟨lt_of_le_of_lt h0 hx.1, lt_of_lt_of_le hx.2 h1⟩

theorem xle_seg {a b c d : ℝ} {y : Plane} (h1 : a ≤ 1) (h2 : c ≤ 1)
    (hy : y ∈ segment ℝ (mkPt a b) (mkPt c d)) : y ∈ {z : Plane | lin 1 0 z ≤ 1} := by
  have := seg_le (f := lin 1 0) (c := 1) (p := mkPt a b) (q := mkPt c d) (by simpa using h1) (by simpa using h2) hy
  exact this

open Classical in
/-- near side, stretch `[X, (1,2)]` (s = 0, t = √5): the two ends are non-straddled (X is the end of Q1; (1,2)
is a vertex of Q and P).  Extracted: the covering set is exactly {Q1}, with sum √5 = t - s. -/
theorem tct_wall_near_left :
    (D.lineChain F 4).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + r • uu)) =
      {((1 : Fin 3), (1 : Fin 3))} ∧
    ∑ e ∈ (D.lineChain F 4).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + r • uu)),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = r - 0 := by
  have hr := r_pos
  have hsum := wall_sum (D := D) (X := X0) (u := uu) (f := F) (c := 4) (g := F) (d := 4) F_ne
    (fun _ => Iff.rfl) F_ne F_X F_u uu_norm (s := 0) (t := r) hr.le
    (fun x hx => hint_all x (ioo_sub le_rfl (by linarith) x hx))
    (fun x hx => hwall_all x (ioo_sub le_rfl (by linarith) x hx))
    (near_not_at 0 (Or.inl rfl)) (near_not_at r (Or.inr (Or.inl rfl)))
  have hfil : (D.lineChain F 4).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + r • uu)) =
        {((1 : Fin 3), (1 : Fin 3))} := by
    rw [chain_near, pt_0, pt_r]
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he | he, hsub⟩
      · subst he
        exfalso
        have h2 : mkPt 2 0 ∈ (D.tile 0).edge 1 := left_mem_segment ℝ _ _
        have := xle_seg (a := 0) (b := 4) (c := 1) (d := 2) (by norm_num) (by norm_num) (hsub h2)
        simp at this
      · exact he
    · rintro rfl
      refine ⟨Or.inr rfl, ?_⟩
      show segment ℝ (mkPt 1 2) (mkPt 0 4) ⊆ _
      rw [segment_symm]
  exact ⟨hfil, hsum⟩

open Classical in
/-- near side, stretch `[(1,2), (2,0)]` (s = √5, t = 2√5): covering set exactly {P1}. -/
theorem tct_wall_near_right :
    (D.lineChain F 4).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + r • uu) (X0 + (2 * r) • uu)) =
      {((0 : Fin 3), (1 : Fin 3))} ∧
    ∑ e ∈ (D.lineChain F 4).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + r • uu) (X0 + (2 * r) • uu)),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = 2 * r - r := by
  have hr := r_pos
  have hsum := wall_sum (D := D) (X := X0) (u := uu) (f := F) (c := 4) (g := F) (d := 4) F_ne
    (fun _ => Iff.rfl) F_ne F_X F_u uu_norm (s := r) (t := 2 * r) (by linarith)
    (fun x hx => hint_all x (ioo_sub hr.le le_rfl x hx))
    (fun x hx => hwall_all x (ioo_sub hr.le le_rfl x hx))
    (near_not_at r (Or.inr (Or.inl rfl))) (near_not_at _ (Or.inr (Or.inr rfl)))
  have hfil : (D.lineChain F 4).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + r • uu) (X0 + (2 * r) • uu)) =
        {((0 : Fin 3), (1 : Fin 3))} := by
    rw [chain_near, pt_2r, pt_r]
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he | he, hsub⟩
      · exact he
      · subst he
        exfalso
        have h2 : mkPt 0 4 ∈ (D.tile 1).edge 1 := right_mem_segment ℝ _ _
        have := seg_le (f := lin (-1) 0) (c := -1) (p := mkPt 1 2) (q := mkPt 2 0)
          (by simp) (by simp) (hsub h2)
        norm_num at this
    · rintro rfl
      refine ⟨Or.inl rfl, ?_⟩
      show segment ℝ (mkPt 2 0) (mkPt 1 2) ⊆ _
      rw [segment_symm]
  exact ⟨hfil, hsum⟩

/-- by-hand check: the two sub-stretch sums are `√5` each (P1 and Q1), adding to `2√5 = L`. -/
theorem tct_wall_byhand :
    dist (mkPt 1 2) (mkPt 0 4) = r - 0 ∧ dist (mkPt 2 0) (mkPt 1 2) = 2 * r - r := by
  rw [d_Q1, d_P1]; constructor <;> ring

open Classical in
/-- far side, the whole stretch `[X, (2,0)]`: both ends non-straddled, the single edge R2 of length 2√5. -/
theorem tct_wall_far_full :
    (D.lineChain (-F) (-4)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + (2 * r) • uu)) =
      {((2 : Fin 3), (2 : Fin 3))} ∧
    ∑ e ∈ (D.lineChain (-F) (-4)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + (2 * r) • uu)),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = 2 * r - 0 := by
  have hr := r_pos
  have hsum := wall_sum (D := D) (X := X0) (u := uu) (f := F) (c := 4) (g := -F) (d := -4)
    (neg_ne_zero.mpr F_ne) neg_iff F_ne F_X F_u uu_norm (s := 0) (t := 2 * r) (by linarith)
    (fun x hx => hint_all x (ioo_sub le_rfl le_rfl x hx))
    (fun x hx => hwall_all x (ioo_sub le_rfl le_rfl x hx))
    (far_not_at 0 (Or.inl rfl)) (far_not_at _ (Or.inr rfl))
  have hfil : (D.lineChain (-F) (-4)).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + (2 * r) • uu)) =
        {((2 : Fin 3), (2 : Fin 3))} := by
    rw [chain_far, pt_2r, pt_0]
    apply Finset.filter_true_of_mem
    intro e he
    simp only [Finset.mem_singleton] at he
    subst he
    exact fun y hy => hy
  exact ⟨hfil, hsum⟩

open Classical in
/-- Failure of the hypotheses of `wall_sum`: far side, stretch `[X, (1,2)]`.  The end hypothesis `ht` fails (R2 passes
through (1,2)), and so does the conclusion: no far edge lies inside the stretch, the sum is 0 ≠ √5 - 0. -/
theorem tct_wall_far_negative :
    Straddled D (-F) (-4) (X0 + r • uu) ∧
    (D.lineChain (-F) (-4)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + r • uu)) = ∅ ∧
    ∑ e ∈ (D.lineChain (-F) (-4)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + r • uu)),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ r - 0 := by
  have hr := r_pos
  have hfil : (D.lineChain (-F) (-4)).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X0 + (0 : ℝ) • uu) (X0 + r • uu)) = ∅ := by
    rw [chain_far, pt_0, pt_r]
    apply Finset.filter_false_of_mem
    intro e he hsub
    simp only [Finset.mem_singleton] at he
    subst he
    have h2 : mkPt 2 0 ∈ (D.tile 2).edge 2 := right_mem_segment ℝ _ _
    have := xle_seg (a := 0) (b := 4) (c := 1) (d := 2) (by norm_num) (by norm_num) (hsub h2)
    simp at this
  refine ⟨tjunction_one_sided.2.2, hfil, ?_⟩
  rw [hfil, Finset.sum_empty]
  linarith

end Erdos634.Draft.TCT
