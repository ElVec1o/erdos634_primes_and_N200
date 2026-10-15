-- Non-vacuity witness for Draft/TraceCovering.lean.
-- This witness is degenerate: ℓ = L (x₀ forced = √2), one edge per side, no T-junction.
-- The T-junction case (an edge on one side passing through a vertex of the other) is controlled by Draft/TCTHand.lean.
import Erdos634.Draft.TraceCovering
import Erdos634.TP_erdos

/-!
# Every hypothesis of `trace_covering` / `wall_sum` / `near_interior_of_across`, jointly, on a real
# dissection

The dissection is the corpus's `TPErdos.wallDissection` (the triangle `(0,0) (2,0) (0,2)` cut along
the median `x = y` into two tiles).  The line is `{x − y = 0}`, parametrized from the target vertex
`X = (0,0)` by the unit vector `u = (√2/2, √2/2)`; the ray leaves the target at `x = √2`, i.e. at
`(1,1)`.  All of `trace_covering`'s hypotheses are discharged: the open stretch is interior
(`TPErdos.wall_hint`), no edge on the line passes through `X` (`vertex_ray_out` +
`not_straddled_of_outside_before`) or through `(1,1)` (`not_straddled_of_outside_after`, with the
hypotenuse bound `TPErdos.hHyp_bound`), and the far tile's edge `[(0,0),(1,1)]` is the seed.  So the
theorem is not vacuous; its conclusion there is the first common junction `x₀ ∈ [√2, √2]`, i.e. the
base point, with both one-edge words of length `√2`.
-/

namespace Erdos634.Draft.TraceCoveringWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.TPErdos Erdos634.Draft.TraceCovering Set

/-- The unit direction of the median. -/
noncomputable def uW : Plane := mkPt (Real.sqrt 2 / 2) (Real.sqrt 2 / 2)

theorem half_sqrt_sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem uW_norm : ‖uW‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [uW, mkPt_zero, mkPt_one, Real.norm_eq_abs, sq_abs, half_sqrt_sq]
  norm_num

theorem wallF_uW : wallF uW = 0 := by simp [uW]

theorem pt_param (x : ℝ) :
    mkPt 0 0 + x • uW = mkPt (x * (Real.sqrt 2 / 2)) (x * (Real.sqrt 2 / 2)) := by
  ext i; fin_cases i <;> simp [uW]

theorem sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt2_mul : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
  rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- The open stretch `(X, X + √2·u)` is the open median `((0,0),(1,1))`, interior to the target. -/
theorem w_hint : ∀ x ∈ Ioo 0 (Real.sqrt 2),
    mkPt 0 0 + x • uW ∈ interior wallDissection.target.carrier := by
  intro x hx
  apply wall_hint
  have hs := sqrt2_pos
  refine ⟨1 - x * (Real.sqrt 2 / 2), x * (Real.sqrt 2 / 2), ?_, ?_, by ring, ?_⟩
  · have : x * (Real.sqrt 2 / 2) < Real.sqrt 2 * (Real.sqrt 2 / 2) :=
      mul_lt_mul_of_pos_right hx.2 (by positivity)
    rw [sqrt2_mul] at this; linarith
  · exact mul_pos hx.1 (by positivity)
  · rw [pt_param]; ext i; fin_cases i <;> simp [wallU, wallV]

theorem w_mem (x : ℝ) (hx : x ∈ Ioo 0 (Real.sqrt 2)) :
    mkPt 0 0 + x • uW ∈ wallDissection.target.carrier := interior_subset (w_hint x hx)

/-- Behind the target vertex `(0,0)` the line is outside the target. -/
theorem w_back : ∀ t : ℝ, t < 0 → mkPt 0 0 + t • uW ∉ wallDissection.target.carrier := by
  intro t ht
  have hv : uW ≠ 0 := ne_zero_of_norm uW_norm
  have h1 : (1 : ℝ) ∈ Ioo 0 (Real.sqrt 2) :=
    ⟨one_pos, by rw [Real.lt_sqrt zero_le_one]; norm_num⟩
  have hin : wallTarget.pts 0 + uW ∈ wallTarget.carrier := by
    have := w_mem 1 h1; rw [one_smul] at this; exact this
  exact vertex_ray_out wallTarget 0 hv hin ht

/-- Beyond `(1,1)` the line is outside the target (`x + y ≤ 2` there). -/
theorem w_fwd : ∀ t : ℝ, Real.sqrt 2 < t → mkPt 0 0 + t • uW ∉ wallDissection.target.carrier := by
  intro t ht hmem
  have hb := hHyp_bound _ hmem
  rw [pt_param, hHyp_pt] at hb
  have hs := sqrt2_pos
  have : Real.sqrt 2 * Real.sqrt 2 < t * Real.sqrt 2 := mul_lt_mul_of_pos_right ht hs
  rw [Real.mul_self_sqrt (by norm_num)] at this
  linarith

theorem w_hgd₁ : ∀ y, wallF y = 0 ↔ wallF y = 0 := fun _ => Iff.rfl
theorem w_hgd₂ : ∀ y, (-wallF) y = -0 ↔ wallF y = 0 := neg_iff

/-- The far tile `(0,0) (1,1) (2,0)`'s edge `[(0,0),(1,1)]` is on the far side of the median. -/
theorem w_seed : ∃ e ∈ wallDissection.lineChain wallF 0 ∪ wallDissection.lineChain (-wallF) (-0),
    (wallDissection.tile e.1).edge e.2 = segment ℝ (mkPt 0 0) (mkPt 0 0 + Real.sqrt 2 • uW) := by
  refine ⟨(0, 0), Finset.mem_union_right _ ?_, ?_⟩
  · rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, fun i => ?_⟩
    · show -wallF (mkPt 0 0) = -0; simp
    · show -wallF (mkPt 1 1) = -0; simp
    · fin_cases i <;> simp [wallTiles, wallTileA, mkTri]
  · rw [pt_param, sqrt2_mul]
    show segment ℝ (mkPt 0 0) (mkPt 1 1) = _
    rfl

/-- **`trace_covering` is not vacuous**: all its hypotheses hold jointly on `wallDissection`. -/
theorem trace_covering_witness :
    ∃ x₀, Real.sqrt 2 ≤ x₀ ∧ x₀ ≤ Real.sqrt 2 ∧
      ¬ Straddled wallDissection wallF 0 (mkPt 0 0 + x₀ • uW) ∧
      ¬ Straddled wallDissection (-wallF) (-0) (mkPt 0 0 + x₀ • uW) := by
  have hX : wallF (mkPt 0 0) = 0 := by simp
  have hstart : ¬ Straddled wallDissection wallF 0 (mkPt 0 0) ∧
      ¬ Straddled wallDissection (-wallF) (-0) (mkPt 0 0) := by
    have h1 := not_straddled_of_outside_before (D := wallDissection) w_hgd₁ wallF_ne hX wallF_uW
      (ne_zero_of_norm uW_norm) (x₀ := 0) w_back
    have h2 := not_straddled_of_outside_before (D := wallDissection) w_hgd₂ wallF_ne hX wallF_uW
      (ne_zero_of_norm uW_norm) (x₀ := 0) w_back
    rw [zero_smul, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have hend := And.intro
    (not_straddled_of_outside_after (D := wallDissection) w_hgd₁ wallF_ne hX wallF_uW
      (ne_zero_of_norm uW_norm) w_fwd)
    (not_straddled_of_outside_after (D := wallDissection) w_hgd₂ wallF_ne hX wallF_uW
      (ne_zero_of_norm uW_norm) w_fwd)
  obtain ⟨x₀, h1, h2, h3, h4, -⟩ := trace_covering (D := wallDissection) wallF_ne hX wallF_uW
    uW_norm sqrt2_pos le_rfl w_hint hstart hend w_seed
  exact ⟨x₀, h1, h2, h3, h4⟩

/-- **`near_interior_of_across` is not vacuous**: the target contains `(0,0)` and has `(0,2)`,
`(2,0)` strictly on the two sides of the median. -/
theorem near_interior_witness :
    ∀ δ > 0, ∃ x : ℝ, |x - 0| < δ ∧ mkPt 0 0 + x • uW ∈ interior wallTarget.carrier :=
  near_interior_of_across (c := 0) (X := mkPt 0 0) (x₀ := 0) wallTarget wallF_ne (by simp)
    wallF_uW (ne_zero_of_norm uW_norm) (by rw [zero_smul, add_zero]; exact A_mem) C_mem B_mem
    (by simp) (by simp)

open Classical in
/-- **`wall_sum` is not vacuous**: one side of the median between its two (non-straddled) ends. -/
theorem wall_sum_witness :
    ∑ e ∈ (wallDissection.lineChain (-wallF) (-0)).filter
        (fun e => (wallDissection.tile e.1).edge e.2 ⊆
          segment ℝ (mkPt 0 0 + (0 : ℝ) • uW) (mkPt 0 0 + Real.sqrt 2 • uW)),
      dist ((wallDissection.tile e.1).pts e.2) ((wallDissection.tile e.1).pts (e.2 + 1))
      = Real.sqrt 2 - 0 := by
  classical
  have hX : wallF (mkPt 0 0) = 0 := by simp
  have hf' : (-wallF : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => wallF_ne (neg_eq_zero.mp h)
  have hwall : ∀ x ∈ Ioo 0 (Real.sqrt 2), ∀ i,
      mkPt 0 0 + x • uW ∉ interior (wallDissection.tile i).carrier := by
    intro x hx
    apply wall_hwall
    have hs := sqrt2_pos
    refine ⟨1 - x * (Real.sqrt 2 / 2), x * (Real.sqrt 2 / 2), ?_, ?_, by ring, ?_⟩
    · have : x * (Real.sqrt 2 / 2) < Real.sqrt 2 * (Real.sqrt 2 / 2) :=
        mul_lt_mul_of_pos_right hx.2 (by positivity)
      rw [sqrt2_mul] at this; linarith
    · exact mul_pos hx.1 (by positivity)
    · rw [pt_param]; ext i; fin_cases i <;> simp [wallU, wallV]
  have hs0 := not_straddled_of_outside_before (D := wallDissection) w_hgd₂ wallF_ne hX wallF_uW
    (ne_zero_of_norm uW_norm) (x₀ := 0) w_back
  have hs1 := not_straddled_of_outside_after (D := wallDissection) w_hgd₂ wallF_ne hX wallF_uW
    (ne_zero_of_norm uW_norm) w_fwd
  exact wall_sum (D := wallDissection) hf' w_hgd₂ wallF_ne hX wallF_uW uW_norm sqrt2_pos.le
    w_hint hwall hs0 hs1

theorem w_far_mem : ((0 : Fin 2), (0 : Fin 3)) ∈ wallDissection.lineChain (-wallF) (-0) := by
  rw [Dissection.mem_lineChain]
  refine ⟨?_, ?_, fun i => ?_⟩
  · show -wallF (mkPt 0 0) = -0; simp
  · show -wallF (mkPt 1 1) = -0; simp
  · fin_cases i <;> simp [wallTiles, wallTileA, mkTri]

theorem w_end : mkPt 0 0 + Real.sqrt 2 • uW = mkPt 1 1 := by rw [pt_param, sqrt2_mul]

open Classical in
/-- **`junction_partial_sum` is not vacuous**: the far edge `[(0,0),(1,1)]` and its endpoint
`(1,1)` on `wallDissection`. -/
theorem junction_partial_sum_witness :
    ∑ e' ∈ (wallDissection.lineChain (-wallF) (-0)).filter
        (fun e' => (wallDissection.tile e'.1).edge e'.2 ⊆
          segment ℝ (mkPt 0 0) ((wallDissection.tile 0).pts (0 + 1))),
      dist ((wallDissection.tile e'.1).pts e'.2) ((wallDissection.tile e'.1).pts (e'.2 + 1))
      = dist (mkPt 0 0) ((wallDissection.tile 0).pts (0 + 1)) := by
  classical
  have hX : wallF (mkPt 0 0) = 0 := by simp
  have hf' : (-wallF : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => wallF_ne (neg_eq_zero.mp h)
  have hwall : ∀ x ∈ Ioo 0 (Real.sqrt 2), ∀ i,
      mkPt 0 0 + x • uW ∉ interior (wallDissection.tile i).carrier := by
    intro x hx
    apply wall_hwall
    have hs := sqrt2_pos
    refine ⟨1 - x * (Real.sqrt 2 / 2), x * (Real.sqrt 2 / 2), ?_, ?_, by ring, ?_⟩
    · have : x * (Real.sqrt 2 / 2) < Real.sqrt 2 * (Real.sqrt 2 / 2) :=
        mul_lt_mul_of_pos_right hx.2 (by positivity)
      rw [sqrt2_mul] at this; linarith
    · exact mul_pos hx.1 (by positivity)
    · rw [pt_param]; ext i; fin_cases i <;> simp [wallU, wallV]
  have h0 := not_straddled_of_outside_before (D := wallDissection) w_hgd₂ wallF_ne hX wallF_uW
    (ne_zero_of_norm uW_norm) (x₀ := 0) w_back
  rw [zero_smul, add_zero] at h0
  have hin : (wallDissection.tile (0 : Fin 2)).edge (0 : Fin 3) ⊆
      segment ℝ (mkPt 0 0) (mkPt 0 0 + Real.sqrt 2 • uW) := by
    rw [w_end]
    show segment ℝ (mkPt 0 0) (mkPt 1 1) ⊆ _
    exact le_rfl
  exact junction_partial_sum (D := wallDissection) (e := ((0 : Fin 2), (0 : Fin 3))) hf' w_hgd₂
    wallF_ne hX wallF_uW uW_norm sqrt2_pos.le w_hint hwall h0 w_far_mem hin (Or.inr rfl)

end Erdos634.Draft.TraceCoveringWitness

#print axioms Erdos634.Draft.TraceCoveringWitness.trace_covering_witness
#print axioms Erdos634.Draft.TraceCoveringWitness.near_interior_witness
#print axioms Erdos634.Draft.TraceCoveringWitness.wall_sum_witness
#print axioms Erdos634.Draft.TraceCoveringWitness.junction_partial_sum_witness
