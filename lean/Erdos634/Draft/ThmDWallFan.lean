import Mathlib.Tactic
import Erdos634.Draft.ThmDWall
import Erdos634.Draft.ThmDSector

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4), layer 2: fan, east angle sum and residue at a wall point  

For a point `P` interior to the target with `WestCover D Φ P` (`Φ` the linear functional whose level lines are the wall; the east side is
`Φ ≥ Φ P`, `cross u = κ Φ`, `κ > 0`):
* `wall_hcov`   : the line near `P` is covered by the west tile (`hcov` of `farside_fan_vertex`);
* `pinfan_wall` : the fan at `P` for two distinct east tiles (replaces `pinfan_ang` at a frontier non-vertex);
* `wall_east_sum` : the tiles of the east half-disc have angle sum `π` at `P`, and every tile with all vertices on the east side is among them;
* `residue_alpha_in` : the residue lemma inside a finite universe `𝒰` (replaces `residue_alpha_total` with `Σ_all = Θ`).
-/

open scoped Classical
open Metric
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RunPartition Set Erdos634.Draft.ThmDHalf Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg Erdos634.Draft.APrimeLegBuild

variable {N : ℕ}

theorem leftHP_iff_Phi {Φ : Plane →ₗ[ℝ] ℝ} {u : Plane} {κ : ℝ} (hκ : 0 < κ)
    (hcross : ∀ y, cross u y = κ * Φ y) (P y : Plane) : y ∈ LeftHP P u ↔ Φ P ≤ Φ y := by
  unfold LeftHP
  simp only [mem_setOf_eq]
  rw [hcross, map_sub]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem rightHP_iff_Phi {Φ : Plane →ₗ[ℝ] ℝ} {u : Plane} {κ : ℝ} (hκ : 0 < κ)
    (hcross : ∀ y, cross u y = κ * Φ y) (P y : Plane) : y ∈ RightHP P u ↔ Φ y ≤ Φ P := by
  unfold RightHP
  simp only [mem_setOf_eq]
  rw [hcross, map_sub]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- the line near `P` lies in the west tile -/
theorem wall_hcov {D : Dissection N} {Φ : Plane →ₗ[ℝ] ℝ} {u : Plane} {κ : ℝ} (hκ : 0 < κ) (hu : u ≠ 0)
    (hcross : ∀ y, cross u y = κ * Φ y) {P : Plane} (hW : WestCover D Φ P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : Plane, cross u (c - P) = 0 → c ∈ ball P δ →
      ∃ j, c ∈ (D.tile j).carrier ∧ (D.tile j).carrier ⊆ RightHP P u := by
  obtain ⟨tC, δ, hδ, hcov, hle⟩ := hW
  refine ⟨δ, hδ, fun c hc hcB => ⟨tC, ?_, fun y hy => ?_⟩⟩
  · -- c is a limit of interior points of the west tile
    have hΦc : Φ c = Φ P := by
      rw [hcross, map_sub] at hc
      have : Φ c - Φ P = 0 := by
        rcases mul_eq_zero.mp hc with h | h
        · exact absurd h hκ.ne'
        · exact h
      linarith
    set n : Plane := mkPt (-(u 1)) (u 0) with hn
    have hcn : cross u n = (u 0) ^ 2 + (u 1) ^ 2 := by
      simp only [cross, hn, mkPt_zero, mkPt_one]; ring
    have hupos : 0 < (u 0) ^ 2 + (u 1) ^ 2 := by
      by_contra hneg
      push_neg at hneg
      have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      apply hu
      ext i; fin_cases i <;> simp [h0, h1]
    have hΦn : 0 < Φ n := by
      have := hcross n; rw [hcn] at this
      have : 0 < κ * Φ n := by rw [← this]; exact hupos
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonneg hκ.le (neg_nonneg.mpr hneg)]
    have hclos : c ∈ closure (interior (D.tile tC).carrier) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hcP : dist c P < δ := mem_ball.mp hcB
      set m : ℝ := ‖n‖ + 1 with hm
      have hmpos : 0 < m := by positivity
      set s : ℝ := min (ε / (2 * m)) ((δ - dist c P) / (2 * m)) with hs
      have hs0 : 0 < s := lt_min (by positivity) (div_pos (by linarith) (by positivity))
      have hsm : s * ‖n‖ < min ε (δ - dist c P) := by
        have h1 : s ≤ ε / (2 * m) := min_le_left _ _
        have h2 : s ≤ (δ - dist c P) / (2 * m) := min_le_right _ _
        have hnm : ‖n‖ < m := by rw [hm]; linarith
        have e1 : s * ‖n‖ ≤ s * m := mul_le_mul_of_nonneg_left hnm.le hs0.le
        have e2 : s * m ≤ ε / (2 * m) * m := mul_le_mul_of_nonneg_right h1 hmpos.le
        have e3 : s * m ≤ (δ - dist c P) / (2 * m) * m := mul_le_mul_of_nonneg_right h2 hmpos.le
        have f1 : ε / (2 * m) * m = ε / 2 := by field_simp
        have f2 : (δ - dist c P) / (2 * m) * m = (δ - dist c P) / 2 := by field_simp
        rw [lt_min_iff]
        constructor <;> linarith
      refine ⟨c - s • n, hcov _ ?_ ?_, ?_⟩
      · calc dist (c - s • n) P ≤ dist (c - s • n) c + dist c P := dist_triangle _ _ _
          _ = s * ‖n‖ + dist c P := by
              rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
          _ < δ := by
              have := (lt_min_iff.mp hsm).2
              linarith
      · rw [map_sub, map_smul, hΦc, smul_eq_mul]
        nlinarith
      · rw [dist_comm, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
        exact (lt_min_iff.mp hsm).1
    have hcl : closure (interior (D.tile tC).carrier) ⊆ (D.tile tC).carrier :=
      closure_minimal interior_subset (D.tile tC).isCompact.isClosed
    exact hcl hclos
  · rw [rightHP_iff_Phi hκ hcross]; exact hle y hy

theorem wall_radius {D : CongruentDissection N} {Φ : Plane →ₗ[ℝ] ℝ} {u : Plane} {κ : ℝ} (hκ : 0 < κ) (hu : u ≠ 0)
    (hcross : ∀ y, cross u y = κ * Φ y) {P : Plane} (hP : P ∈ interior D.target.carrier)
    (hW : WestCover D.toDissection Φ P) :
    ∃ r0 : ℝ, 0 < r0 ∧ ball P r0 ⊆ D.target.carrier ∧
      ∀ c : Plane, cross u (c - P) = 0 → c ∈ ball P r0 →
        ∃ j, c ∈ (D.tile j).carrier ∧ (D.tile j).carrier ⊆ RightHP P u := by
  obtain ⟨δ, hδ, hcov⟩ := wall_hcov hκ hu hcross hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hP)
  refine ⟨min δ ε, lt_min hδ hε, fun y hy => interior_subset (hball (ball_subset_ball (min_le_right _ _) hy)),
    fun c hc hcB => hcov c hc (ball_subset_ball (min_le_left _ _) hcB)⟩

/-- **The fan at a wall point.** -/
theorem pinfan_wall (D : CongruentDissection N) {α : ℝ} (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hA1 : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi)
    {Φ : Plane →ₗ[ℝ] ℝ} {u : Plane} {κ : ℝ} (hκ : 0 < κ) (hu : u ≠ 0)
    (hcross : ∀ y, cross u y = κ * Φ y) {P : Plane} (hP : P ∈ interior D.target.carrier)
    (hW : WestCover D.toDissection Φ P)
    (tW tE : Fin N) (hWE : tW ≠ tE)
    (hWe : ∀ i, Φ P ≤ Φ ((D.tile tW).pts i)) (hEe : ∀ i, Φ P ≤ Φ ((D.tile tE).pts i)) (a a' : Ang)
    (hWa : (D.tile tW).localAngle P = angVal α a) (hEa : (D.tile tE).localAngle P = angVal α a') :
    ∃ m : Cnt, Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m) := by
  obtain ⟨r0, hr0, hball, hcov⟩ := wall_radius hκ hu hcross hP hW
  refine farside_fan_vertex D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α hirr hA0 hA1 hA2 hα h3α
    P u hu hr0 hball hcov tW tE hWE ?_ ?_ a a' hWa hEa
  · exact carrier_subset_of_pts (convex_leftHP P u) _ (fun k => (leftHP_iff_Phi hκ hcross P _).mpr (hWe k))
  · exact carrier_subset_of_pts (convex_leftHP P u) _ (fun k => (leftHP_iff_Phi hκ hcross P _).mpr (hEe k))

/-- **The east angle sum at a wall point.** -/
theorem wall_east_sum (D : CongruentDissection N) {Φ : Plane →ₗ[ℝ] ℝ} {u : Plane} {κ : ℝ} (hκ : 0 < κ)
    (hu : u ≠ 0) (hcross : ∀ y, cross u y = κ * Φ y) {P : Plane} (hP : P ∈ interior D.target.carrier)
    (hW : WestCover D.toDissection Φ P) :
    ∃ S : Finset (Fin N), ∑ i ∈ S, (D.tile i).localAngle P = Real.pi ∧
      ∀ i, (∀ k, Φ P ≤ Φ ((D.tile i).pts k)) → i ∈ S := by
  classical
  obtain ⟨r0, hr0, hball, hcov⟩ := wall_radius hκ hu hcross hP hW
  let S : Finset (Fin N) := Finset.univ.filter fun i => (D.tile i).carrier ∩ ball P r0 ⊆ LeftHP P u
  have hmemS : ∀ i, i ∈ S ↔ (D.tile i).carrier ∩ ball P r0 ⊆ LeftHP P u := by
    intro i; simp [S]
  refine ⟨S, ?_, ?_⟩
  · refine halfplane_sum_localAngle D.toDissection P u hu hr0 (fun y hy => hball hy.2) S
      (fun i hi => (hmemS i).mp hi) ?_
    intro i hi
    rcases not_straddle D.toDissection P u hu hcov i with h | h
    · exact absurd ((hmemS i).mpr h) hi
    · exact h
  · intro i hi
    rw [hmemS]
    intro y hy
    exact carrier_subset_of_pts (convex_leftHP P u) _
      (fun k => (leftHP_iff_Phi hκ hcross P _).mpr (hi k)) hy.1

/-- **The residue inside a universe.** -/
theorem residue_alpha_in {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) {x : Plane} {Θ : ℝ} (hΘ : α < Θ)
    (U : Finset (Fin N)) (htot : ∑ i ∈ U, (D.tile i).localAngle x = Θ)
    (S : Finset (Fin N)) (hSU : S ⊆ U) (hS : ∑ i ∈ S, (D.tile i).localAngle x = Θ - α) :
    ∀ G ∈ U, G ∉ S → (D.tile G).localAngle x ≠ 0 → (D.tile G).localAngle x = α := by
  have hpi := Real.pi_pos
  set T : Finset (Fin N) := U \ S with hT
  have hTsum : ∑ i ∈ T, (D.tile i).localAngle x = α := by
    have := Finset.sum_sdiff hSU (f := fun i => (D.tile i).localAngle x)
    linarith
  have hnn : ∀ i, 0 ≤ (D.tile i).localAngle x := fun i => (D.tile i).localAngle_nonneg x
  have hle : ∀ i ∈ T, (D.tile i).localAngle x ≤ α := by
    intro i hi
    have := Finset.single_le_sum (fun m _ => hnn m) hi
    linarith
  have hcases : ∀ i ∈ T, (D.tile i).localAngle x = 0 ∨ (D.tile i).localAngle x = α ∨
      (D.tile i).localAngle x = Real.pi - 3 * α ∨ (D.tile i).localAngle x = 2 * α := by
    intro i hi
    have hle' := hle i hi
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) x with ⟨j, hj, hval⟩ | h2pi | hpi' | h0
    · obtain ⟨k, hk⟩ := congruent_corner_angles (hcong i) j
      rw [hval, hk]
      fin_cases k
      · right; left; exact hA0
      · right; right; left; exact hA1
      · right; right; right; exact hA2
    · exfalso; rw [h2pi] at hle'; linarith
    · exfalso; rw [hpi'] at hle'; linarith
    · exact Or.inl h0
  intro G hGU hG hne
  have hGT : G ∈ T := Finset.mem_sdiff.mpr ⟨hGU, hG⟩
  have hrest : ∑ i ∈ T.erase G, (D.tile i).localAngle x = α - (D.tile G).localAngle x := by
    have := Finset.add_sum_erase T (fun i => (D.tile i).localAngle x) hGT
    beta_reduce at this
    linarith
  obtain ⟨X, Y, Z, hXYZ⟩ := Erdos634.PinPlumbing.sum_of_values_real (T.erase G) (fun i => (D.tile i).localAngle x)
    α (Real.pi - 3 * α) (2 * α) (fun i hi => hcases i (Finset.mem_of_mem_erase hi))
  rw [hrest] at hXYZ
  rcases hcases G hGT with h0 | hαv | hβv | hγv
  · exact absurd h0 hne
  · exact hαv
  · exfalso
    rw [hβv] at hXYZ
    have := cnt_eq α hirr X Y Z 4 (-1) (by push_cast; linarith)
    omega
  · exfalso
    rw [hγv] at hXYZ
    have := cnt_eq α hirr X Y Z (-1) 0 (by push_cast; linarith)
    omega

#print axioms pinfan_wall
#print axioms wall_east_sum
#print axioms residue_alpha_in

end Erdos634.Draft.ThmDRun
