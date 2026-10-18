import Mathlib.Tactic
import Erdos634.AngleSumDissection
import Erdos634.PinPlumbing
import Erdos634.VertexSector
import Erdos634.Draft.APrimeLeg
import Erdos634.CongruentAngles

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D': the fan on ONE SIDE of an interior line  

The infrastructure the R-mirror row step needs (see the plan of the formalization):
the analogue of `PinPlumbing.junction_equation` / `APrimeLeg.junction_fan` for a point `p` of an interior
segment, with the tiles lying in the closed left half-plane of the directed line `(p, u)`.

* `volume_halfBall`  — the half disc `LeftHP p u ∩ ball p r` has area `π r² / 2`;
* `halfplane_sum_localAngle` — if the half disc near `p` lies in the target, `S` is a set of tiles whose trace on
  the ball lies in the half plane, and every other tile has null trace on the half plane, then the local
  angles of the tiles of `S` at `p` sum to exactly `π` (measure argument of `Dissection.sum_localAngle_eq`);
* `halfplane_fan` — the corner-angle version (`junction_equation` for one side), with two distinguished tiles;
* `halfplane_junction_fan` — the `Fan` form for the `γ = 2α` tile via `straight_vertex`.
-/

open MeasureTheory Set Metric

namespace Erdos634.Draft.ThmDHalf

open Erdos634.Geometry Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

/-- The closed left half plane of the directed line through `p` with direction `u`. -/
def LeftHP (p u : Plane) : Set Plane := {y | 0 ≤ cross u (y - p)}
/-- The closed right half plane. -/
def RightHP (p u : Plane) : Set Plane := {y | cross u (y - p) ≤ 0}

theorem leftHP_measurable (p u : Plane) : MeasurableSet (LeftHP p u) := by
  have hc : Continuous fun y : Plane => cross u (y - p) := by
    unfold cross
    fun_prop
  exact (isClosed_le continuous_const hc).measurableSet

theorem rightHP_measurable (p u : Plane) : MeasurableSet (RightHP p u) := by
  have hc : Continuous fun y : Plane => cross u (y - p) := by
    unfold cross
    fun_prop
  exact (isClosed_le hc continuous_const).measurableSet

/-- The dividing line is null (`u ≠ 0`). -/
theorem volume_line_null (p u : Plane) (hu : u ≠ 0) :
    volume {y : Plane | cross u (y - p) = 0} = 0 := by
  have hne : cross u (rot90 u) ≠ 0 := by
    have h0 : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hu
      ext i; fin_cases i
      · exact hcon.1
      · exact hcon.2
    have : cross u (rot90 u) = u 0 ^ 2 + u 1 ^ 2 := by
      unfold cross; simp only [rot90_apply0, rot90_apply1]; ring
    rw [this]
    rcases h0 with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  have h := volume_cross_zero u (rot90 u) hne
  have hpre : {y : Plane | cross u (y - p) = 0}
      = (fun y : Plane => y + (-p)) ⁻¹' {z : Plane | cross u z = 0} := by
    ext y; simp [sub_eq_add_neg]
  rw [hpre, measure_preimage_add_right]
  exact h

/-- Reflection in `p` swaps the two closed half planes (as measures on the ball). -/
theorem volume_reflect (p : Plane) (A : Set Plane) (hA : MeasurableSet A) :
    volume ((fun y : Plane => (2 : ℝ) • p - y) ⁻¹' A) = volume A := by
  have h1 : (fun y : Plane => (2 : ℝ) • p - y) = (fun y : Plane => y + (2 : ℝ) • p) ∘ (fun y => -y) := by
    funext y; simp [sub_eq_add_neg, add_comm]
  rw [h1, Set.preimage_comp, ← Measure.map_apply measurable_neg ((measurable_add_const _) hA),
    Measure.map_neg_eq_self, measure_preimage_add_right]

/-- **The half disc.**  `|LeftHP p u ∩ B(p,r)| = π r² / 2`. -/
theorem volume_halfBall (p u : Plane) (hu : u ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    volume (LeftHP p u ∩ ball p r) = ENNReal.ofReal (Real.pi * r ^ 2 / 2) := by
  have hball : MeasurableSet (ball p r) := (isOpen_ball : IsOpen (ball p r)).measurableSet
  have hLm := (leftHP_measurable p u).inter hball
  have hRm := (rightHP_measurable p u).inter hball
  have hunion : (LeftHP p u ∩ ball p r) ∪ (RightHP p u ∩ ball p r) = ball p r := by
    ext y
    simp only [LeftHP, RightHP, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro h
      rcases le_total 0 (cross u (y - p)) with h0 | h0
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h0, h⟩
  have hinter : volume ((LeftHP p u ∩ ball p r) ∩ (RightHP p u ∩ ball p r)) = 0 := by
    apply measure_mono_null _ (volume_line_null p u hu)
    intro y hy
    simp only [LeftHP, RightHP, mem_inter_iff, mem_setOf_eq] at hy
    exact le_antisymm hy.2.1 hy.1.1
  have hrefl : volume (RightHP p u ∩ ball p r) = volume (LeftHP p u ∩ ball p r) := by
    rw [← volume_reflect p _ hLm]
    congr 1
    ext y
    simp only [LeftHP, RightHP, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_ball, dist_eq_norm]
    have hc : cross u ((2 : ℝ) • p - y - p) = - cross u (y - p) := by
      unfold cross; simp; ring
    have hn : ‖(2 : ℝ) • p - y - p‖ = ‖y - p‖ := by
      rw [show (2 : ℝ) • p - y - p = -(y - p) by
        rw [two_smul]; abel, norm_neg]
    rw [hc, hn]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  have hsum := measure_union_add_inter (μ := volume) (LeftHP p u ∩ ball p r) hRm
  rw [hunion, hinter, add_zero, hrefl, volume_ball_plane p hr] at hsum
  have h2 : (2 : ENNReal) * volume (LeftHP p u ∩ ball p r)
      = 2 * ENNReal.ofReal (Real.pi * r ^ 2 / 2) := by
    rw [two_mul, hsum.symm.trans (by rfl : _ = _)]
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2


/-- **The half-plane angle sum.**  `p` a point with the half disc `LeftHP p u ∩ B(p,r0)` inside the target;
`S` a set of tiles whose trace on `B(p,r0)` lies in the half plane; every other tile has null trace on the
half plane.  Then the local angles at `p` of the tiles of `S` sum to `π`. -/
theorem halfplane_sum_localAngle {N : ℕ} (D : Dissection N) (p u : Plane) (hu : u ≠ 0)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hfill : LeftHP p u ∩ ball p r0 ⊆ D.target.carrier)
    (S : Finset (Fin N))
    (hS : ∀ i ∈ S, (D.tile i).carrier ∩ ball p r0 ⊆ LeftHP p u)
    (hout : ∀ i, i ∉ S → volume ((D.tile i).carrier ∩ ball p r0 ∩ LeftHP p u) = 0) :
    ∑ i ∈ S, (D.tile i).localAngle p = Real.pi := by
  classical
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle p
  obtain ⟨r1, hr1, hr1le⟩ := exists_common_radius D.pos ri hri
  set r : ℝ := min r0 r1 with hrdef
  have hrpos : 0 < r := lt_min hr0 hr1
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hball_sub : ball p r ⊆ ball p r0 := ball_subset_ball hrr0
  have hball : MeasurableSet (ball p r) := (isOpen_ball : IsOpen (ball p r)).measurableSet
  have hcov : LeftHP p u ∩ ball p r
      = ⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ ball p r ∩ LeftHP p u) := by
    ext y
    constructor
    · rintro ⟨hyL, hyB⟩
      have hy : y ∈ D.target.carrier := hfill ⟨hyL, hball_sub hyB⟩
      rw [← D.covers] at hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact mem_biUnion (Finset.mem_univ i) ⟨⟨hi, hyB⟩, hyL⟩
    · intro hy
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hy
      exact ⟨hi.2, hi.1.2⟩
  have hmeas := measure_biUnion_finset₀ (μ := volume) (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ ball p r ∩ LeftHP p u)
    (fun i _ j _ hij => (D.aedisjoint hij).mono (fun y hy => hy.1.1) (fun y hy => hy.1.1))
    (fun i _ => (((D.tile i).nullMeasurableSet).inter hball.nullMeasurableSet).inter
      (leftHP_measurable p u).nullMeasurableSet)
  rw [← hcov, volume_halfBall p u hu hrpos.le] at hmeas
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ S →
      volume ((D.tile i).carrier ∩ ball p r ∩ LeftHP p u) = 0 := by
    intro i _ hi
    have hsub : (D.tile i).carrier ∩ ball p r ∩ LeftHP p u ⊆ (D.tile i).carrier ∩ ball p r0 ∩ LeftHP p u :=
      fun y hy => ⟨⟨hy.1.1, hball_sub hy.1.2⟩, hy.2⟩
    exact measure_mono_null hsub (hout i hi)
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero] at hmeas
  have hterm : ∀ i ∈ S, volume ((D.tile i).carrier ∩ ball p r ∩ LeftHP p u)
      = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r ^ 2) := by
    intro i hi
    have hsub : (D.tile i).carrier ∩ ball p r ∩ LeftHP p u = (D.tile i).carrier ∩ ball p r := by
      ext y
      exact ⟨fun h => h.1, fun h => Set.mem_inter h (hS i hi ⟨h.1, hball_sub h.2⟩)⟩
    rw [hsub]
    exact hcontrib i r hrpos ((min_le_right _ _).trans (hr1le i))
  rw [Finset.sum_congr rfl hterm] at hmeas
  have hnn : ∀ i ∈ S, 0 ≤ (D.tile i).localAngle p / 2 * r ^ 2 := fun i _ => by
    have := (D.tile i).localAngle_nonneg p
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at hmeas
  have hreal := (ENNReal.ofReal_eq_ofReal_iff (by positivity)
    (Finset.sum_nonneg hnn)).mp hmeas
  have hfact : ∑ i ∈ S, (D.tile i).localAngle p / 2 * r ^ 2
      = (∑ i ∈ S, (D.tile i).localAngle p) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at hreal
  have hr2 : (0 : ℝ) < r ^ 2 / 2 := by positivity
  have hkey : (∑ i ∈ S, (D.tile i).localAngle p) * (r ^ 2 / 2) = Real.pi * (r ^ 2 / 2) := by
    rw [← hreal]; ring
  exact mul_right_cancel₀ hr2.ne' hkey

/-- **The half-plane equation** (`junction_equation` for one side of an interior line): two distinct tiles of
`S` with positive local angle at `p`; the others contribute `0` or a model corner angle, and
`x·A₀ + y·A₁ + z·A₂ = π − θ_W − θ_E`. -/
theorem halfplane_equation {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (p u : Plane) (hu : u ≠ 0)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hfill : LeftHP p u ∩ ball p r0 ⊆ D.target.carrier)
    (S : Finset (Fin N))
    (hS : ∀ i ∈ S, (D.tile i).carrier ∩ ball p r0 ⊆ LeftHP p u)
    (hout : ∀ i, i ∉ S → volume ((D.tile i).carrier ∩ ball p r0 ∩ LeftHP p u) = 0)
    (iW iE : Fin N) (hW : iW ∈ S) (hE : iE ∈ S) (hWE : iW ≠ iE)
    (hAW : 0 < (D.tile iW).localAngle p) (hAE : 0 < (D.tile iE).localAngle p) :
    ∃ x y z : ℕ,
      (x : ℝ) * cornerAngle (model.pts 1) (model.pts 0) (model.pts 2)
        + y * cornerAngle (model.pts 2) (model.pts 1) (model.pts 0)
        + z * cornerAngle (model.pts 0) (model.pts 2) (model.pts 1)
      = Real.pi - (D.tile iW).localAngle p - (D.tile iE).localAngle p := by
  classical
  have hsum := halfplane_sum_localAngle D p u hu hr0 hfill S hS hout
  set S' : Finset (Fin N) := (S.erase iW).erase iE with hS'
  have hEm : iE ∈ S.erase iW := Finset.mem_erase.mpr ⟨Ne.symm hWE, hE⟩
  have hsplit : ∑ i ∈ S', (D.tile i).localAngle p
      = Real.pi - (D.tile iW).localAngle p - (D.tile iE).localAngle p := by
    have h1 := Finset.add_sum_erase S (fun i => (D.tile i).localAngle p) hW
    have h2 := Finset.add_sum_erase (S.erase iW) (fun i => (D.tile i).localAngle p) hEm
    rw [hS']; linarith
  have hcases : ∀ i ∈ S', (D.tile i).localAngle p = 0 ∨
      (D.tile i).localAngle p = cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) ∨
      (D.tile i).localAngle p = cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) ∨
      (D.tile i).localAngle p = cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) := by
    intro i hi
    have hnneg : ∀ m ∈ S'.erase i, 0 ≤ (D.tile m).localAngle p :=
      fun m _ => (D.tile m).localAngle_nonneg p
    have hge : (D.tile i).localAngle p ≤ ∑ m ∈ S', (D.tile m).localAngle p := by
      have := Finset.add_sum_erase S' (fun m => (D.tile m).localAngle p) hi
      have hrest : 0 ≤ ∑ m ∈ S'.erase i, (D.tile m).localAngle p := Finset.sum_nonneg hnneg
      linarith [this]
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) p with ⟨j, hj, hval⟩ | h2pi | hpi | h0
    · obtain ⟨k, hk⟩ := congruent_corner_angles (hcong i) j
      right
      rw [hval, hk]
      fin_cases k
      · left; rfl
      · right; left; rfl
      · right; right; rfl
    · exfalso
      rw [h2pi, hsplit] at hge
      linarith [Real.pi_pos]
    · exfalso
      rw [hpi, hsplit] at hge
      linarith
    · exact Or.inl h0
  obtain ⟨x, y, z, hxyz⟩ := Erdos634.PinPlumbing.sum_of_values_real S' (fun i => (D.tile i).localAngle p) _ _ _ hcases
  exact ⟨x, y, z, by rw [← hxyz, hsplit]⟩

/-- **The half-plane fan** for the `γ = 2α` tile (angles `α, π − 3α, 2α`): two distinct tiles of `S` presenting
the abstract angles `a`, `a'` at `p`; with the remaining tiles the counts form a `Fan` (`β` once,
`α + 2γ = 3`). -/
theorem halfplane_junction_fan {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi)
    (p u : Plane) (hu : u ≠ 0) {r0 : ℝ} (hr0 : 0 < r0)
    (hfill : LeftHP p u ∩ ball p r0 ⊆ D.target.carrier)
    (S : Finset (Fin N))
    (hS : ∀ i ∈ S, (D.tile i).carrier ∩ ball p r0 ⊆ LeftHP p u)
    (hout : ∀ i, i ∉ S → volume ((D.tile i).carrier ∩ ball p r0 ∩ LeftHP p u) = 0)
    (tW tE : Fin N) (hW : tW ∈ S) (hE : tE ∈ S) (hWE : tW ≠ tE) (a a' : Ang)
    (hWa : (D.tile tW).localAngle p = angVal α a) (hEa : (D.tile tE).localAngle p = angVal α a') :
    ∃ m : Cnt, Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m) := by
  have hpos : ∀ b : Ang, 0 < angVal α b := by
    intro b; cases b <;> simp only [angVal] <;> linarith
  obtain ⟨x, y, z, hxyz⟩ := halfplane_equation D model hcong p u hu hr0 hfill S hS hout tW tE hW hE hWE
    (by rw [hWa]; exact hpos _) (by rw [hEa]; exact hpos _)
  rw [hA0, hA1, hA2, hWa, hEa] at hxyz
  refine ⟨(x, y, z), fan_of_cval α hirr _ ?_⟩
  rw [cval_add, cval_add, cval_ang, cval_ang]
  simp only [cval]
  linarith

/-- Forbidden pairs: two `γ`'s, or two `β`'s, cannot both occur in a half-plane fan. -/
theorem no_two_gamma (a a' : Ang) (m : Cnt) (hF : Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m))
    (h : a = Ang.ga ∧ a' = Ang.ga) : False := by
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, y, z⟩ := m
  simp [Fan, Cnt.add, Ang.cnt] at hF
  omega

theorem no_two_beta (a a' : Ang) (m : Cnt) (hF : Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m))
    (h : a = Ang.be ∧ a' = Ang.be) : False := by
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, y, z⟩ := m
  simp [Fan, Cnt.add, Ang.cnt] at hF
  omega

#print axioms halfplane_sum_localAngle
#print axioms halfplane_equation
#print axioms halfplane_junction_fan
#print axioms no_two_gamma
end Erdos634.Draft.ThmDHalf
