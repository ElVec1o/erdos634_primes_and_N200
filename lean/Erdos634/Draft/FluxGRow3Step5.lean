-- Draft/FluxGRow3Step5.lean — Proposition RP, Step 5: the boundary sum `Tri.flux (gaussWeight α θ₀ X)`
-- evaluated on the target `targetIso`, per grid degree `X`, combining the `BC` edge class against the
-- `CA`+`AB` edge class. Not imported into All.lean.
--
-- Step 5 of the argument: traverse `B → C → A` counterclockwise. `BC` sits at `(0,0)`,
-- `CA = BC + (π − α)` sits at `(−1, 2)`, `AB = CA + 2α` sits at `(1, 2)`, so
-- `Σ_X z^X Φ_X = 2λb − λc(z + z⁻¹)`. Here `Φ_X(∂ABC)` is the boundary-side counterpart of
-- `Σ_tiles C_X(t)` (the cancellation `lem:cancel` applied to `f_X`), i.e. `Tri.flux (gaussWeight α θ₀ X)`
-- evaluated at the target. The normalisation is the one of `FluxGRow3TargetCoords.lean`: hypotenuse
-- `c = 1`, `b = cos α`. The identity is read coefficientwise in `X`; no formal Laurent variable `z` is
-- introduced.
--
-- Main statement `targetIso_flux_gauss`: for `targetIso α lam` with the direction of `BC`
-- (`leftUnit 0`) assumed on the grid (hypothesis `hgridBC`), for every `X : ℤ`,
--   `Tri.flux (gaussWeight α θ₀ X) targetIso
--     = I^j * ( (if k = X then 2λcosα else 0) − (if k − 1 = X then λ else 0)
--                − (if k + 1 = X then λ else 0) )`,
-- with `(k, j)` the grid degree of `BC`. The prefactor `I^j` also occurs in the tile-side values of
-- `FluxGRow3Cancel.lean`. The proof composes the definition of `Tri.flux`, the three side lengths of
-- `targetIso`, the turn steps `targetIso_turn_CA`/`_AB`, and `gaussWeightA_shift`.
--
-- Not done here:
--   - `hgridBC` is a hypothesis, as in `FluxGRow3TargetDirs.lean`; the grid membership of `BC` is a
--     placement fact about a real dissection.
--   - No connection to the tile side via `Dissection.flux_cancel` on a real `CongruentDissection`
--     (see `FluxGRow3Step3N2Final` for an instance).
--   - Step 6's identity and Step 7's arithmetic (`Erdos634.Geometry.Row3.step7_even`, `FluxGRow3.lean`).
--
-- The theorem needs `hairr : Irrational (α/π)`, which fails at `α = π/4`, so `witness_step5` uses
-- `α = Real.arctan (1/2)` with `hgridBC` witnessed by `k = j = 0` (taking `θ₀` to be the angle of `BC`
-- itself); `hairr` remains a hypothesis of `witness_step5`.
import Erdos634.Draft.FluxGRow3TargetDirs

open scoped Classical

namespace Erdos634.Geometry.Row3

open Real Erdos634.Geometry

/-! ## Step 5, proper: the target's own flux, per grid degree

`Tri.flux (gaussWeight α θ₀ X)` unfolds over `targetIso`'s three edges `B→C`, `C→A`, `A→B`, using
`Tri.flux`'s definition (`FluxCore.lean`) exactly as `FluxGRow3Cancel.lean`'s `Tri.flux_gauss_direct`
already unfolds it for a tile. -/

section BoundarySum

variable {α θ₀ lam : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)

/-- **Step 5's boundary polynomial, coefficientwise.** With `(k, j)` the grid degree of `BC`'s own
direction (`hgridBC`), the target's flux at grid degree `X` is `i^j` times
`2λ cos α · [k=X] − λ · [k−1=X] − λ · [k+1=X]`, i.e.
`Σ_X z^X Φ_X(∂ABC) = 2λb − λc(z+z⁻¹)` on the `c=1` convention (`b = cos α`), read at one grid degree
`X` at a time, exactly as `Tri.flux_gauss_direct`/`_reflected` already read the tile side. -/
theorem targetIso_flux_gauss (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)
    (hairr : Irrational (α / Real.pi))
    (hgridBC : IsGridA α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) (X : ℤ) :
    (targetIso α lam hα hα2 hlam).flux (gaussWeight α θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) *
        ((if gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle = X
            then (2 * lam * Real.cos α : ℂ) else 0)
          - (if gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle - 1 = X
              then (lam : ℂ) else 0)
          - (if gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + 1 = X
              then (lam : ℂ) else 0)) := by
  set T := targetIso α lam hα hα2 hlam with hT
  set k := gridK α θ₀ (T.leftUnit 0).angle with hk_def
  set j := gridJ α θ₀ (T.leftUnit 0).angle with hj_def
  -- The two turn steps, converted to grid shifts exactly as `targetIso_grid_CA`/`_AB` do.
  have hturnCA := targetIso_turn_CA α lam hα hα2 hlam
  have hturnAB := targetIso_turn_AB α lam hα hα2 hlam
  have hshiftCA : (Real.pi - α : ℝ) = (((-1:ℤ):ℝ) * α + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    push_cast; ring
  have hshiftAB : (Real.pi + α : ℝ) = (((1:ℤ):ℝ) * α + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    push_cast; ring
  rw [hshiftCA] at hturnCA
  rw [hshiftAB] at hturnAB
  -- The three edge weights, read off via `gaussWeightA_shift` exactly as
  -- `Tri.flux_gauss_direct`/`_reflected` do for a tile.
  have hgw0 : gaussWeight α θ₀ X (T.leftUnit 0) = if k = X then (Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight gaussWeightA
    rw [dif_pos hgridBC]
  have hgw1 : gaussWeight α θ₀ X (T.leftUnit 1)
      = if k - 1 = X then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hairr hgridBC (-1) 2 X
    rw [hturnCA, hshift]
    unfold gaussWeightA
    rw [dif_pos hgridBC]
    by_cases hX : k = X - (-1)
    · rw [if_pos hX, if_pos (by omega : k - 1 = X)]
      have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]; simp [Complex.I_sq]
      rw [hI2]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k - 1 = X), mul_zero]
  have hgw2 : gaussWeight α θ₀ X (T.leftUnit 2)
      = if k + 1 = X then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hairr hgridBC 1 2 X
    rw [hturnAB, hshift]
    unfold gaussWeightA
    rw [dif_pos hgridBC]
    by_cases hX : k = X - 1
    · rw [if_pos hX, if_pos (by omega : k + 1 = X)]
      have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]; simp [Complex.I_sq]
      rw [hI2]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k + 1 = X), mul_zero]
  -- Unfold `Tri.flux` over the three edges: `dist(pts0,pts1) = 2λcosα`, `dist(pts1,pts2) = λ`,
  -- `dist(pts2,pts0) = λ` (`targetIso_dist01/_dist12/_dist02`).
  have hd01 : dist (T.pts 0) (T.pts 1) = 2 * lam * Real.cos α := targetIso_dist01 α lam hα hα2 hlam
  have hd12 : dist (T.pts 1) (T.pts 2) = lam := targetIso_dist12 α lam hα hα2 hlam
  have hd20 : dist (T.pts 2) (T.pts 0) = lam := by
    rw [dist_comm]; exact targetIso_dist02 α lam hα hα2 hlam
  have hflux : T.flux (gaussWeight α θ₀ X)
      = (dist (T.pts 0) (T.pts 1) : ℝ) • gaussWeight α θ₀ X (T.leftUnit 0)
        + (dist (T.pts 1) (T.pts 2) : ℝ) • gaussWeight α θ₀ X (T.leftUnit 1)
        + (dist (T.pts 2) (T.pts 0) : ℝ) • gaussWeight α θ₀ X (T.leftUnit 2) := by
    unfold Tri.flux
    rw [Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl]
  rw [hflux, hd01, hd12, hd20, hgw0, hgw1, hgw2,
    Complex.real_smul, Complex.real_smul, Complex.real_smul]
  by_cases h1 : k = X
  · have h2 : ¬ k - 1 = X := by omega
    have h3 : ¬ k + 1 = X := by omega
    simp only [if_pos h1, if_neg h2, if_neg h3]
    push_cast
    ring
  · by_cases h2 : k - 1 = X
    · have h3 : ¬ k + 1 = X := by omega
      simp only [if_neg h1, if_pos h2, if_neg h3]
      push_cast
      ring
    · by_cases h3 : k + 1 = X
      · simp only [if_neg h1, if_neg h2, if_pos h3]
        push_cast
        ring
      · simp only [if_neg h1, if_neg h2, if_neg h3]
        push_cast
        ring

end BoundarySum

/-! ## Non-vacuity witness

Grid membership `hgridBC` is witnessed TRIVIALLY, for ANY `α, lam`, by taking `θ₀` to be `BC`'s own
`leftUnit 0` angle: then `k = 0, j = 0` works by `rfl`-style unfolding of `IsGridA`. This shows
`hgridBC` is a genuinely satisfiable hypothesis (not vacuous), independent of irrationality — exactly
as `FluxGRow3TargetDirs.lean`'s own witness section already established for `targetIso_grid_CA`/`_AB`.
`hairr` (`α / π` irrational) is NOT discharged: no concrete `α` with a proved-irrational `α/π` is
exhibited anywhere in this Draft corpus (the existing witnesses, `α = π/4`, are all rational-over-`π`
sanity checks that deliberately do NOT satisfy `hairr`). So `witness_step5` below witnesses `hgridBC`
concretely, but still carries `hairr` as a genuine unclosed hypothesis — stated honestly, not hidden. -/

-- `θ₀` must be a real number (`IsGridA`'s second argument), not a `Real.Angle`. We take
-- `θ₀ := (leftUnit 0).angle.toReal`, the canonical real representative
-- (`Real.Angle.toReal : Real.Angle → ℝ`, with `Real.Angle.coe_toReal : (θ.toReal : Real.Angle) = θ`
-- for every `θ`), so `hgridBC` is witnessed at `(k, j) = (0, 0)` by that coercion identity alone, for
-- ANY `α, lam` — no irrationality needed for this part.
theorem hgridBC_witness (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    IsGridA α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
      ((targetIso α lam hα hα2 hlam).leftUnit 0).angle :=
  ⟨0, 0, by push_cast; simp [Real.Angle.coe_toReal]⟩

theorem witness_step5 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)
    (hairr : Irrational (α / Real.pi)) (X : ℤ) :
    (targetIso α lam hα hα2 hlam).flux
        (gaussWeight α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal X)
      = (Complex.I : ℂ) ^
          (gridJ α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
            ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) *
        ((if gridK α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
              ((targetIso α lam hα hα2 hlam).leftUnit 0).angle = X
            then (2 * lam * Real.cos α : ℂ) else 0)
          - (if gridK α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
                ((targetIso α lam hα hα2 hlam).leftUnit 0).angle - 1 = X
              then (lam : ℂ) else 0)
          - (if gridK α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
                ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + 1 = X
              then (lam : ℂ) else 0)) :=
  targetIso_flux_gauss hα hα2 hlam hairr (hgridBC_witness α lam hα hα2 hlam) X

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.targetIso_flux_gauss
#print axioms Erdos634.Geometry.Row3.hgridBC_witness
#print axioms Erdos634.Geometry.Row3.witness_step5
