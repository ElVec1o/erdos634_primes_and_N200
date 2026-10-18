import Mathlib.Tactic
import Erdos634.Draft.ThmDRunSector
import Erdos634.Draft.ThmDHalfFan
import Erdos634.PinPlumbing
import Erdos634.CongruentAngles

/-!
# Theorem D' (R5 sector step 1): the residue tile at an interior vertex  

`residue_alpha` : at an interior point `x` of the target, a finite set `S` of tiles whose local angles at `x` add up to `2π - α`
leaves exactly one further tile `G`, with angle `α` at `x`, all other tiles having angle `0` there.  (The angle sum `2π` at an
interior point, the figure arithmetic `sector_alpha`: `α` is atomic.)  This is the existence half of the `G_j` of Lemmas 32/33
(Beeson-Rosu pp. 26-29): the five tiles `Δ_{s-j-1,j}, Δ_{s-j,j-1}, ∇_{s-j-1,j-1}, ∇_{s-j-1,j}, ∇_{s-j,j-1}` show `β,γ,α,γ,β`,
i.e. `2π - α`.
-/

open scoped Classical

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.Draft.APrimeLegBuild

/-- **Residue tile, any total angle.**  If the tiles of `S` have angles at `x` adding up to `Θ - α` and all tiles add up to `Θ`
(`Θ = 2π` at an interior point, `π` at a frontier non-vertex), every tile outside `S` with a nonzero angle at `x` has angle `α`. -/
theorem residue_alpha_total {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) {x : Plane} {Θ : ℝ} (hΘ : α < Θ)
    (htot : ∑ i, (D.tile i).localAngle x = Θ)
    (S : Finset (Fin N)) (hS : ∑ i ∈ S, (D.tile i).localAngle x = Θ - α) :
    ∀ G : Fin N, G ∉ S → (D.tile G).localAngle x ≠ 0 → (D.tile G).localAngle x = α := by
  have hpi := Real.pi_pos
  set T : Finset (Fin N) := Finset.univ \ S with hT
  have hTsum : ∑ i ∈ T, (D.tile i).localAngle x = α := by
    have := Finset.sum_sdiff (Finset.subset_univ S) (f := fun i => (D.tile i).localAngle x)
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
  intro G hG hne
  have hGT : G ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hG⟩
  have hrest : ∑ i ∈ T.erase G, (D.tile i).localAngle x = α - (D.tile G).localAngle x := by
    have := Finset.add_sum_erase T (fun i => (D.tile i).localAngle x) hGT
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

/-- **Residue tile for `β`.**  Like `residue_alpha_total`: tiles of `S` adding up to `Θ - β` leave every other tile with a nonzero angle
with the angle `β`. -/
theorem residue_beta_total {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) {x : Plane} {Θ : ℝ}
    (htot : ∑ i, (D.tile i).localAngle x = Θ)
    (S : Finset (Fin N)) (hS : ∑ i ∈ S, (D.tile i).localAngle x = Θ - (Real.pi - 3 * α)) :
    ∀ G : Fin N, G ∉ S → (D.tile G).localAngle x ≠ 0 → (D.tile G).localAngle x = Real.pi - 3 * α := by
  have hpi := Real.pi_pos
  set β : ℝ := Real.pi - 3 * α with hβ
  have hβpos : 0 < β := by rw [hβ]; linarith
  set T : Finset (Fin N) := Finset.univ \ S with hT
  have hTsum : ∑ i ∈ T, (D.tile i).localAngle x = β := by
    have := Finset.sum_sdiff (Finset.subset_univ S) (f := fun i => (D.tile i).localAngle x)
    linarith
  have hnn : ∀ i, 0 ≤ (D.tile i).localAngle x := fun i => (D.tile i).localAngle_nonneg x
  have hle : ∀ i ∈ T, (D.tile i).localAngle x ≤ β := by
    intro i hi
    have := Finset.single_le_sum (fun m _ => hnn m) hi
    linarith
  have hcases : ∀ i ∈ T, (D.tile i).localAngle x = 0 ∨ (D.tile i).localAngle x = α ∨
      (D.tile i).localAngle x = β ∨ (D.tile i).localAngle x = 2 * α := by
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
  intro G hG hne
  have hGT : G ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hG⟩
  have hrest : ∑ i ∈ T.erase G, (D.tile i).localAngle x = β - (D.tile G).localAngle x := by
    have := Finset.add_sum_erase T (fun i => (D.tile i).localAngle x) hGT
    linarith
  obtain ⟨X, Y, Z, hXYZ⟩ := Erdos634.PinPlumbing.sum_of_values_real (T.erase G) (fun i => (D.tile i).localAngle x)
    α β (2 * α) (fun i hi => hcases i (Finset.mem_of_mem_erase hi))
  rw [hrest] at hXYZ
  rcases hcases G hGT with h0 | hαv | hβv | hγv
  · exact absurd h0 hne
  · exfalso
    rw [hαv] at hXYZ
    have := cnt_eq α hirr X Y Z (-4) 1 (by push_cast; rw [hβ] at hXYZ; linarith)
    omega
  · exact hβv
  · exfalso
    rw [hγv] at hXYZ
    have := cnt_eq α hirr X Y Z (-5) 1 (by push_cast; rw [hβ] at hXYZ; linarith)
    omega

theorem residue_alpha {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) (α : ℝ) (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) {x : Plane} (hx : x ∈ interior D.target.carrier)
    (S : Finset (Fin N)) (hS : ∑ i ∈ S, (D.tile i).localAngle x = 2 * Real.pi - α) :
    ∃ G : Fin N, G ∉ S ∧ (D.tile G).localAngle x = α ∧
      ∀ i, i ∉ S → i ≠ G → (D.tile i).localAngle x = 0 := by
  have hpi := Real.pi_pos
  set T : Finset (Fin N) := Finset.univ \ S with hT
  have hsum := Erdos634.PinPlumbing.pin_angle_sum_interior D hx
  have hTsum : ∑ i ∈ T, (D.tile i).localAngle x = α := by
    have := Finset.sum_sdiff (Finset.subset_univ S) (f := fun i => (D.tile i).localAngle x)
    linarith
  have hnn : ∀ i, 0 ≤ (D.tile i).localAngle x := fun i => (D.tile i).localAngle_nonneg x
  -- each tile of T contributes 0, alpha, beta or gamma
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
  -- some tile of T is nonzero
  obtain ⟨i0, hi0T, hi0⟩ : ∃ i0 ∈ T, (D.tile i0).localAngle x ≠ 0 := by
    by_contra hno
    push_neg at hno
    have : ∑ i ∈ T, (D.tile i).localAngle x = 0 := Finset.sum_eq_zero hno
    linarith
  have hrest : ∑ i ∈ T.erase i0, (D.tile i).localAngle x = α - (D.tile i0).localAngle x := by
    have := Finset.add_sum_erase T (fun i => (D.tile i).localAngle x) hi0T
    linarith
  obtain ⟨X, Y, Z, hXYZ⟩ := Erdos634.PinPlumbing.sum_of_values_real (T.erase i0) (fun i => (D.tile i).localAngle x)
    α (Real.pi - 3 * α) (2 * α) (fun i hi => hcases i (Finset.mem_of_mem_erase hi))
  rw [hrest] at hXYZ
  rcases hcases i0 hi0T with h0 | hαv | hβv | hγv
  · exact absurd h0 hi0
  · -- the residue tile is i0 and everything else vanishes
    refine ⟨i0, ?_, hαv, ?_⟩
    · exact (Finset.mem_sdiff.mp hi0T).2
    · intro i hiS hne
      have hiT : i ∈ T.erase i0 := Finset.mem_erase.mpr ⟨hne, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiS⟩⟩
      have hz : ∑ m ∈ T.erase i0, (D.tile m).localAngle x = 0 := by rw [hrest, hαv]; ring
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => hnn m)).mp hz i hiT
  · exfalso
    rw [hβv] at hXYZ
    have := cnt_eq α hirr X Y Z 4 (-1) (by push_cast; linarith)
    omega
  · exfalso
    rw [hγv] at hXYZ
    have := cnt_eq α hirr X Y Z (-1) 0 (by push_cast; linarith)
    omega

#print axioms residue_alpha
#print axioms residue_alpha_total
#print axioms residue_beta_total
end Erdos634.Draft.ThmDRun
