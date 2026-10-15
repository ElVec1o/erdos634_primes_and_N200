/-
Draft/PI3FBal.lean -- Theorem T, step (c): **the chain-balance lemma L1**,
for an arbitrary `Dissection` (no congruence, no angle hypothesis).

Setting.  `D : Dissection N`, a type function `τ : (Fin N × Fin 3) → Fin 3` and lengths `ℓ : Fin 3 → ℝ` with
`eLen e = ℓ (τ e)` for every tile edge, `ℓ ≥ 0`; `B` bounds the diameter of the target; and a **floor hypothesis**
(the shape of `InterfaceFloor.interface_floor`): every nonzero integer relation `Σ nᵢ ℓᵢ = 0` has one-sided length `> B`.

Result `interior_type_balance`: for every direction-odd integer weight `ω` and every `ρ : Fin 3 → ℤ`,
`Σ_{e interior} ρ(τ e) · ω(eDir e) = 0`.  The proof is the line-by-line count: group the interior edges by the
geometric line carrying them (`lineKey`); on a line all edges point in `±d`; the overlap matrix (`opposite_cover_real`)
shows the `d`-edges and the `−d`-edges of the line have EQUAL TOTAL LENGTH; both totals are `≤ B` (the line meets the
target in a segment: `hausdorff_line_le` + `sameDir_subsingleton`); hence the difference of the type-count vectors is a
relation of one-sided length `≤ B`, which the floor forces to vanish: `fibre_balance`.

This avoids connected components of the overlap graph: a whole LINE (not a maximal segment) already has near-side total
length `≤ diam(target)`.
No sorry, no native_decide.
-/
import Erdos634.Draft.FluxCancel

open scoped Classical
open MeasureTheory Set Erdos634.Geometry

namespace Erdos634.Draft.PI3F

variable {N : ℕ}

/-! ### Unit vectors -/

theorem dir_sq (d : Dir) : d.1 0 ^ 2 + d.1 1 ^ 2 = 1 := by
  have h := d.2
  have h2 : ‖d.1‖ ^ 2 = 1 := by rw [h]; norm_num
  rw [EuclideanSpace.norm_sq_eq] at h2
  simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using h2

theorem plane_ext {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i; fin_cases i
  · exact h0
  · exact h1

/-- Parallel unit vectors are equal or opposite. -/
theorem dir_eq_or_neg_of_cross (u v : Dir) (h : cross u.1 v.1 = 0) : v = u ∨ v = Dir.neg u := by
  have hu := dir_sq u
  have hv := dir_sq v
  simp only [cross] at h
  have key : ((v.1 0 - u.1 0) ^ 2 + (v.1 1 - u.1 1) ^ 2) * ((v.1 0 + u.1 0) ^ 2 + (v.1 1 + u.1 1) ^ 2) = 0 := by
    linear_combination ((v.1 0 ^ 2 + v.1 1 ^ 2) - (u.1 0 ^ 2 + u.1 1 ^ 2)) * (hv - hu)
      + 4 * (u.1 0 * v.1 1 - u.1 1 * v.1 0) * h
  rcases mul_eq_zero.mp key with h1 | h1
  · left
    have a0 : v.1 0 - u.1 0 = 0 := by nlinarith [sq_nonneg (v.1 0 - u.1 0), sq_nonneg (v.1 1 - u.1 1)]
    have a1 : v.1 1 - u.1 1 = 0 := by nlinarith [sq_nonneg (v.1 0 - u.1 0), sq_nonneg (v.1 1 - u.1 1)]
    exact Subtype.ext (plane_ext (by linarith) (by linarith))
  · right
    have a0 : v.1 0 + u.1 0 = 0 := by nlinarith [sq_nonneg (v.1 0 + u.1 0), sq_nonneg (v.1 1 + u.1 1)]
    have a1 : v.1 1 + u.1 1 = 0 := by nlinarith [sq_nonneg (v.1 0 + u.1 0), sq_nonneg (v.1 1 + u.1 1)]
    exact Subtype.ext (plane_ext (by simp [Dir.neg]; linarith) (by simp [Dir.neg]; linarith))

/-! ### The line carrying a tile edge -/

/-- The line carrying tile edge `e`. -/
noncomputable def lineKey (D : Dissection N) (e : Fin N × Fin 3) : Set Plane :=
  {x | cross (D.eDir e).1 x = cross (D.eDir e).1 ((D.tile e.1).pts e.2)}

theorem cross_leftUnit_edge (T : Tri) (k : Fin 3) :
    cross (T.leftUnit k).1 (T.pts (k + 1) - T.pts k) = 0 := by
  have hl : (T.leftUnit k).1 = ‖T.leftDir k‖⁻¹ • T.leftDir k := rfl
  rcases T.leftDir_eq_or k with h | h
  · rw [hl, h]
    simp only [cross, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  · rw [hl, h]
    simp only [cross, PiLp.smul_apply, PiLp.neg_apply, PiLp.sub_apply, smul_eq_mul]; ring

/-- The whole edge lies on its line. -/
theorem edge_cross (D : Dissection N) (e : Fin N × Fin 3) {z : Plane} (hz : z ∈ D.eSet e) :
    cross (D.eDir e).1 z = cross (D.eDir e).1 ((D.tile e.1).pts e.2) := by
  have hz' : z ∈ segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := hz
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz'
  have q := cross_leftUnit_edge (D.tile e.1) e.2
  have hQ : cross (D.eDir e).1 ((D.tile e.1).pts (e.2 + 1)) = cross (D.eDir e).1 ((D.tile e.1).pts e.2) := by
    have := cross_add_right (D.eDir e).1 ((D.tile e.1).pts e.2)
      ((D.tile e.1).pts (e.2 + 1) - (D.tile e.1).pts e.2)
    rw [add_sub_cancel] at this
    have q' : cross (D.eDir e).1 ((D.tile e.1).pts (e.2 + 1) - (D.tile e.1).pts e.2) = 0 := q
    linarith
  rw [cross_add_right, cross_smul_right, cross_smul_right, hQ]
  have : a * cross (D.eDir e).1 ((D.tile e.1).pts e.2) + b * cross (D.eDir e).1 ((D.tile e.1).pts e.2)
      = (a + b) * cross (D.eDir e).1 ((D.tile e.1).pts e.2) := by ring
  rw [this, hab, one_mul]

theorem startPt_mem (D : Dissection N) (e : Fin N × Fin 3) : (D.tile e.1).pts e.2 ∈ D.eSet e :=
  left_mem_segment ℝ _ _

theorem endPt_mem (D : Dissection N) (e : Fin N × Fin 3) : (D.tile e.1).pts (e.2 + 1) ∈ D.eSet e :=
  right_mem_segment ℝ _ _

theorem mem_lineKey_of_mem (D : Dissection N) (e : Fin N × Fin 3) {z : Plane} (hz : z ∈ D.eSet e) :
    z ∈ lineKey D e := edge_cross D e hz

/-- Two edges that touch, with opposite directions, lie on the same line. -/
theorem lineKey_eq_of_common (D : Dissection N) {e e' : Fin N × Fin 3} {z : Plane}
    (hz : z ∈ D.eSet e) (hz' : z ∈ D.eSet e') (hd : D.eDir e' = Dir.neg (D.eDir e)) :
    lineKey D e = lineKey D e' := by
  have h1 := edge_cross D e hz
  have h2 := edge_cross D e' hz'
  have hneg : (D.eDir e').1 = -(D.eDir e).1 := by rw [hd]; rfl
  rw [hneg] at h2
  simp only [cross_neg_left] at h2
  have h2' : cross (D.eDir e).1 z = cross (D.eDir e).1 ((D.tile e'.1).pts e'.2) := by linarith
  ext x
  simp only [lineKey, Set.mem_setOf_eq]
  rw [hneg, cross_neg_left, cross_neg_left]
  constructor
  · intro hx; linarith
  · intro hx; linarith

/-- Two edges on the same line point in the same or in opposite directions. -/
theorem dir_eq_or_neg_of_lineKey_eq (D : Dissection N) {e e' : Fin N × Fin 3}
    (h : lineKey D e = lineKey D e') : D.eDir e' = D.eDir e ∨ D.eDir e' = Dir.neg (D.eDir e) := by
  have hP : (D.tile e'.1).pts e'.2 ∈ lineKey D e' := mem_lineKey_of_mem D e' (startPt_mem D e')
  have hQ : (D.tile e'.1).pts (e'.2 + 1) ∈ lineKey D e' := mem_lineKey_of_mem D e' (endPt_mem D e')
  rw [← h] at hP hQ
  simp only [lineKey, Set.mem_setOf_eq] at hP hQ
  have hc : cross (D.eDir e).1 ((D.tile e'.1).pts (e'.2 + 1) - (D.tile e'.1).pts e'.2) = 0 := by
    simp only [cross, PiLp.sub_apply] at hP hQ ⊢
    linarith
  have hl : (D.eDir e').1 = ‖(D.tile e'.1).leftDir e'.2‖⁻¹ • (D.tile e'.1).leftDir e'.2 := rfl
  have hcd : cross (D.eDir e).1 (D.eDir e').1 = 0 := by
    rw [hl]
    rcases (D.tile e'.1).leftDir_eq_or e'.2 with h' | h'
    · rw [h', cross_smul_right, hc, mul_zero]
    · rw [h', cross_smul_right]
      have : cross (D.eDir e).1 (-((D.tile e'.1).pts (e'.2 + 1) - (D.tile e'.1).pts e'.2)) = 0 := by
        simp only [cross, PiLp.sub_apply, PiLp.neg_apply] at hc ⊢
        linarith
      rw [this, mul_zero]
  exact dir_eq_or_neg_of_cross _ _ hcd

/-! ### A line meets the target in a short set -/

/-- `μH¹` of a set contained in a line and of diameter `≤ B` is `≤ B`. -/
theorem hausdorff_line_le {X : Set Plane} (d : Dir) (c : ℝ) (hX : ∀ x ∈ X, cross d.1 x = c)
    {B : ℝ} (hB : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ B) :
    (Measure.hausdorffMeasure 1 : Measure Plane) X ≤ ENNReal.ofReal B := by
  have hd := dir_sq d
  let ψ : ℝ → Plane := fun t => WithLp.toLp 2 ![t * d.1 0 - c * d.1 1, t * d.1 1 + c * d.1 0]
  let φ : Plane → ℝ := fun x => x 0 * d.1 0 + x 1 * d.1 1
  have hψ : Isometry ψ := by
    refine Isometry.of_dist_eq fun s t => ?_
    have e0 : (ψ s) 0 - (ψ t) 0 = (s - t) * d.1 0 := by simp [ψ]; ring
    have e1 : (ψ s) 1 - (ψ t) 1 = (s - t) * d.1 1 := by simp [ψ]; ring
    rw [EuclideanSpace.dist_eq, Real.dist_eq]
    simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
    rw [e0, e1]
    rw [show ((s - t) * d.1 0) ^ 2 + ((s - t) * d.1 1) ^ 2 = |s - t| ^ 2 by
      rw [sq_abs]; linear_combination (s - t) ^ 2 * hd]
    exact Real.sqrt_sq (abs_nonneg _)
  have hsub : X ⊆ ψ '' (φ '' X) := by
    intro x hx
    refine ⟨φ x, ⟨x, hx, rfl⟩, ?_⟩
    have hc := hX x hx
    simp only [cross] at hc
    apply plane_ext
    · simp only [ψ, φ]
      show (x 0 * d.1 0 + x 1 * d.1 1) * d.1 0 - c * d.1 1 = x 0
      rw [← hc]; linear_combination (x 0) * hd
    · simp only [ψ, φ]
      show (x 0 * d.1 0 + x 1 * d.1 1) * d.1 1 + c * d.1 0 = x 1
      rw [← hc]; linear_combination (x 1) * hd
  calc (Measure.hausdorffMeasure 1 : Measure Plane) X
      ≤ (Measure.hausdorffMeasure 1 : Measure Plane) (ψ '' (φ '' X)) := measure_mono hsub
    _ = (Measure.hausdorffMeasure 1 : Measure ℝ) (φ '' X) :=
        hψ.hausdorffMeasure_image (Or.inl zero_le_one) _
    _ = volume (φ '' X) := by rw [hausdorffMeasure_real]
    _ ≤ Metric.ediam (φ '' X) := Real.volume_le_diam _
    _ ≤ ENNReal.ofReal B := by
        refine Metric.ediam_le ?_
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [edist_dist, Real.dist_eq]
        apply ENNReal.ofReal_le_ofReal
        have hxy := hB x hx y hy
        rw [EuclideanSpace.dist_eq] at hxy
        simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hxy
        have h1 : |φ x - φ y| ≤ Real.sqrt ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
          apply Real.abs_le_sqrt
          simp only [φ]
          nlinarith [sq_nonneg ((x 0 - y 0) * d.1 1 - (x 1 - y 1) * d.1 0)]
        linarith

/-! ### Counting by type -/

theorem sum_by_type {M : Type*} [AddCommMonoid M] {V : Type*} (τ : V → Fin 3) (s : Finset V) (f : Fin 3 → M) :
    ∑ e ∈ s, f (τ e) = ∑ i : Fin 3, (s.filter (fun e => τ e = i)).card • f i := by
  rw [← Finset.sum_fiberwise s τ (fun e => f (τ e))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_const]
  exact Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.mp he).2]

/-! ### The fibre (one line) -/

section Fibre

variable (D : Dissection N) (τ : Fin N × Fin 3 → Fin 3) (ℓ : Fin 3 → ℝ)

/-- The interior edges on the same line as `e0`. -/
noncomputable def lineEdges (e0 : Fin N × Fin 3) : Finset (Fin N × Fin 3) :=
  D.intEdges.filter (fun e => lineKey D e = lineKey D e0)

theorem overlap_ne_zero_common {e e' : Fin N × Fin 3} (h : D.overlap e e' ≠ 0) :
    ∃ z, z ∈ D.eSet e ∧ z ∈ D.eSet e' := by
  by_contra hne
  push Not at hne
  apply h
  have : D.eSet e ∩ D.eSet e' = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact hne z
  unfold Dissection.overlap
  rw [this]
  simp

/-- The length of an edge is the sum of its overlaps with the opposite edges of its own line. -/
theorem eLen_eq_sum_line (e0 : Fin N × Fin 3) {e : Fin N × Fin 3} (he : e ∈ lineEdges D e0) :
    D.eLen e = ∑ e' ∈ (lineEdges D e0).filter (fun e' => D.eDir e' = Dir.neg (D.eDir e)), D.overlap e' e := by
  have heI : e ∈ D.intEdges := (Finset.mem_filter.mp he).1
  have hek : lineKey D e = lineKey D e0 := (Finset.mem_filter.mp he).2
  rw [← D.opposite_cover_real heI]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro e' he'
    obtain ⟨he'1, he'2⟩ := Finset.mem_filter.mp he'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he'1).1, he'2⟩
  · intro e' he'I he'n
    by_contra hne
    apply he'n
    obtain ⟨he'I', he'd⟩ := Finset.mem_filter.mp he'I
    have hov : D.overlap e' e ≠ 0 := by
      intro h0
      exact hne h0
    obtain ⟨z, hz', hz⟩ := overlap_ne_zero_common D hov
    have hkey := lineKey_eq_of_common D hz hz' he'd
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he'I', ?_⟩, he'd⟩
    rw [← hkey, hek]

/-- **Balance of the two sides of a line (lengths).** -/
theorem line_length_balance (e0 : Fin N × Fin 3) :
    ∑ e ∈ (lineEdges D e0).filter (fun e => D.eDir e = D.eDir e0), D.eLen e
      = ∑ e ∈ (lineEdges D e0).filter (fun e => D.eDir e = Dir.neg (D.eDir e0)), D.eLen e := by
  set K := lineEdges D e0 with hK
  set Kd := K.filter (fun e => D.eDir e = D.eDir e0) with hKd
  set Kn := K.filter (fun e => D.eDir e = Dir.neg (D.eDir e0)) with hKn
  have h1 : ∑ e ∈ Kd, D.eLen e = ∑ e ∈ Kd, ∑ e' ∈ Kn, D.overlap e' e := by
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨heK, hed⟩ := Finset.mem_filter.mp he
    rw [eLen_eq_sum_line D e0 heK, hed]
  have h2 : ∑ e' ∈ Kn, D.eLen e' = ∑ e' ∈ Kn, ∑ e ∈ Kd, D.overlap e e' := by
    refine Finset.sum_congr rfl fun e' he' => ?_
    obtain ⟨he'K, he'd⟩ := Finset.mem_filter.mp he'
    rw [eLen_eq_sum_line D e0 he'K, he'd, Dir.neg_involutive]
  rw [h1, h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun e _ => ?_
  exact D.overlap_comm e' e

/-- **Total length of the `d`-edges of one line is at most the diameter bound.** -/
theorem line_length_le (e0 : Fin N × Fin 3) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ D.target.carrier, ∀ y ∈ D.target.carrier, dist x y ≤ B) :
    ∑ e ∈ (lineEdges D e0).filter (fun e => D.eDir e = D.eDir e0), D.eLen e ≤ B := by
  set Kd := (lineEdges D e0).filter (fun e => D.eDir e = D.eDir e0) with hKd
  set U : Set Plane := ⋃ e ∈ Kd, D.eSet e with hU
  have hmeas : ∀ e ∈ Kd, MeasurableSet (D.eSet e) :=
    fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet
  have hsum := sum_hausdorff_of_partition Kd D.eSet U ∅ Set.finite_empty hmeas
    (fun e₁ h₁ e₂ h₂ hne => D.sameDir_subsingleton hne
      (((Finset.mem_filter.mp h₁).2).trans ((Finset.mem_filter.mp h₂).2).symm))
    (fun e he => Set.subset_biUnion_of_mem (u := D.eSet) he)
    (fun x hx => hx.1)
  have hUle : (Measure.hausdorffMeasure 1 : Measure Plane) U ≤ ENNReal.ofReal B := by
    refine hausdorff_line_le (D.eDir e0) (cross (D.eDir e0).1 ((D.tile e0.1).pts e0.2)) ?_ ?_
    · intro x hx
      obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨heK, hed⟩ := Finset.mem_filter.mp he
      have hk : lineKey D e = lineKey D e0 := (Finset.mem_filter.mp heK).2
      have := mem_lineKey_of_mem D e hxe
      rw [hk] at this
      exact this
    · intro x hx y hy
      obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨e', he', hye⟩ := Set.mem_iUnion₂.mp hy
      exact hB x (tile_subset_target D e.1 ((D.tile e.1).edge_subset_carrier e.2 hxe)) y
        (tile_subset_target D e'.1 ((D.tile e'.1).edge_subset_carrier e'.2 hye))
  have hfin : ∀ e ∈ Kd, (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e) ≠ ⊤ := by
    intro e _
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  have hreal : ∑ e ∈ Kd, D.eLen e = ((Measure.hausdorffMeasure 1 : Measure Plane) U).toReal := by
    rw [← hsum, ENNReal.toReal_sum hfin]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg]
    rfl
  rw [hreal]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hUle

variable {D τ ℓ}

/-- **Fibre balance (L1 for one line).**  The `d`-edges and the `−d`-edges of a line carry the same number of edges of
each type. -/
theorem fibre_balance (hlen : ∀ e, D.eLen e = ℓ (τ e)) (hℓ : ∀ i, 0 ≤ ℓ i) {B : ℝ}
    (hB : ∀ x ∈ D.target.carrier, ∀ y ∈ D.target.carrier, dist x y ≤ B)
    (hfloor : ∀ n : Fin 3 → ℤ, (∃ i, n i ≠ 0) → ∑ i, (n i : ℝ) * ℓ i = 0 →
      B < ∑ i, ((max (n i) 0 : ℤ) : ℝ) * ℓ i)
    (e0 : Fin N × Fin 3) (he0 : e0 ∈ D.intEdges) (i : Fin 3) :
    (((lineEdges D e0).filter (fun e => D.eDir e = D.eDir e0)).filter (fun e => τ e = i)).card
      = (((lineEdges D e0).filter (fun e => D.eDir e = Dir.neg (D.eDir e0))).filter (fun e => τ e = i)).card := by
  set Kd := (lineEdges D e0).filter (fun e => D.eDir e = D.eDir e0) with hKd
  set Kn := (lineEdges D e0).filter (fun e => D.eDir e = Dir.neg (D.eDir e0)) with hKn
  have hB0 : 0 ≤ B := by
    have he0' : e0 ∈ lineEdges D e0 := Finset.mem_filter.mpr ⟨he0, rfl⟩
    have hx := startPt_mem D e0
    have hx' := tile_subset_target D e0.1 ((D.tile e0.1).edge_subset_carrier e0.2 hx)
    have := hB _ hx' _ hx'
    simpa using this
  have hbal := line_length_balance D e0
  have hle := line_length_le D e0 hB0 hB
  have hlen_sum : ∀ s : Finset (Fin N × Fin 3), ∑ e ∈ s, D.eLen e
      = ∑ j : Fin 3, ((s.filter (fun e => τ e = j)).card : ℝ) * ℓ j := by
    intro s
    simp_rw [hlen]
    rw [sum_by_type τ s (fun j => ℓ j)]
    simp
  set cd : Fin 3 → ℕ := fun j => (Kd.filter (fun e => τ e = j)).card with hcd
  set cn : Fin 3 → ℕ := fun j => (Kn.filter (fun e => τ e = j)).card with hcn
  have hd' : ∑ j : Fin 3, (cd j : ℝ) * ℓ j = ∑ j : Fin 3, (cn j : ℝ) * ℓ j := by
    rw [← hlen_sum, ← hlen_sum]; exact hbal
  have hd'' : ∑ j : Fin 3, (cd j : ℝ) * ℓ j ≤ B := by rw [← hlen_sum]; exact hle
  by_contra hne
  have hex : ∃ j, ((cd j : ℤ) - cn j) ≠ 0 := by
    refine ⟨i, ?_⟩
    intro h0
    apply hne
    have : (cd i : ℤ) = cn i := by linarith
    exact_mod_cast this
  have hrel : ∑ j, (((cd j : ℤ) - cn j : ℤ) : ℝ) * ℓ j = 0 := by
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  have hfl := hfloor (fun j => (cd j : ℤ) - cn j) hex hrel
  have hmax : ∑ j, ((max ((cd j : ℤ) - cn j) 0 : ℤ) : ℝ) * ℓ j ≤ ∑ j : Fin 3, (cd j : ℝ) * ℓ j := by
    refine Finset.sum_le_sum fun j _ => ?_
    apply mul_le_mul_of_nonneg_right _ (hℓ j)
    have : max ((cd j : ℤ) - cn j) 0 ≤ (cd j : ℤ) := by
      apply max_le
      · have : (0 : ℤ) ≤ cn j := by positivity
        linarith
      · positivity
    exact_mod_cast this
  linarith

end Fibre

/-! ### The interior balance -/

/-- **Chain-balance lemma (L1) for the interior of a dissection.**  Under the floor hypothesis, every direction-odd integer
weight with a type-dependent integer coefficient sums to zero over the interior edges. -/
theorem interior_type_balance (D : Dissection N) (τ : Fin N × Fin 3 → Fin 3) (ℓ : Fin 3 → ℝ)
    (hlen : ∀ e, D.eLen e = ℓ (τ e)) (hℓ : ∀ i, 0 ≤ ℓ i) {B : ℝ}
    (hB : ∀ x ∈ D.target.carrier, ∀ y ∈ D.target.carrier, dist x y ≤ B)
    (hfloor : ∀ n : Fin 3 → ℤ, (∃ i, n i ≠ 0) → ∑ i, (n i : ℝ) * ℓ i = 0 →
      B < ∑ i, ((max (n i) 0 : ℤ) : ℝ) * ℓ i)
    (ρ : Fin 3 → ℤ) (ω : Dir → ℤ) (hω : ∀ d, ω (Dir.neg d) = - ω d) :
    ∑ e ∈ D.intEdges, ρ (τ e) * ω (D.eDir e) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := lineKey D) (t := D.intEdges.image (lineKey D))
    (fun e he => Finset.mem_image_of_mem _ he)]
  apply Finset.sum_eq_zero
  intro L hL
  obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp hL
  set K := lineEdges D e0 with hK
  have hK' : D.intEdges.filter (fun e => lineKey D e = lineKey D e0) = K := rfl
  rw [hK']
  set Kd := K.filter (fun e => D.eDir e = D.eDir e0) with hKd
  set Kn := K.filter (fun e => D.eDir e = Dir.neg (D.eDir e0)) with hKn
  have hne : D.eDir e0 ≠ Dir.neg (D.eDir e0) := fun h => Dir.neg_ne_self _ h.symm
  have hsplit : ∑ e ∈ K, ρ (τ e) * ω (D.eDir e)
      = ∑ e ∈ Kd, ρ (τ e) * ω (D.eDir e) + ∑ e ∈ Kn, ρ (τ e) * ω (D.eDir e) := by
    rw [← Finset.sum_filter_add_sum_filter_not K (fun e => D.eDir e = D.eDir e0)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp only [Finset.mem_filter, hKn]
    constructor
    · rintro ⟨heK, hn⟩
      refine ⟨heK, ?_⟩
      have hk : lineKey D e = lineKey D e0 := (Finset.mem_filter.mp heK).2
      rcases dir_eq_or_neg_of_lineKey_eq D hk.symm with h | h
      · exact absurd h hn
      · exact h
    · rintro ⟨heK, hn⟩
      refine ⟨heK, ?_⟩
      rw [hn]
      exact fun h => hne h.symm
  have hd : ∑ e ∈ Kd, ρ (τ e) * ω (D.eDir e) = ω (D.eDir e0) * ∑ j : Fin 3, ((Kd.filter (fun e => τ e = j)).card : ℤ) * ρ j := by
    have : ∀ e ∈ Kd, ρ (τ e) * ω (D.eDir e) = ω (D.eDir e0) * ρ (τ e) := by
      intro e he
      rw [(Finset.mem_filter.mp he).2]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_by_type τ Kd (fun j => ρ j)]
    simp
  have hn : ∑ e ∈ Kn, ρ (τ e) * ω (D.eDir e) = - (ω (D.eDir e0) * ∑ j : Fin 3, ((Kn.filter (fun e => τ e = j)).card : ℤ) * ρ j) := by
    have : ∀ e ∈ Kn, ρ (τ e) * ω (D.eDir e) = - (ω (D.eDir e0) * ρ (τ e)) := by
      intro e he
      rw [(Finset.mem_filter.mp he).2, hω]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib, ← Finset.mul_sum, sum_by_type τ Kn (fun j => ρ j)]
    simp
  have hcnt : ∀ j : Fin 3, (Kd.filter (fun e => τ e = j)).card = (Kn.filter (fun e => τ e = j)).card :=
    fun j => fibre_balance hlen hℓ hB hfloor e0 he0 j
  rw [hsplit, hd, hn]
  have : ∑ j : Fin 3, ((Kd.filter (fun e => τ e = j)).card : ℤ) * ρ j
      = ∑ j : Fin 3, ((Kn.filter (fun e => τ e = j)).card : ℤ) * ρ j :=
    Finset.sum_congr rfl fun j _ => by rw [hcnt j]
  rw [this]; ring

end Erdos634.Draft.PI3F

#print axioms Erdos634.Draft.PI3F.hausdorff_line_le
#print axioms Erdos634.Draft.PI3F.fibre_balance
#print axioms Erdos634.Draft.PI3F.interior_type_balance
