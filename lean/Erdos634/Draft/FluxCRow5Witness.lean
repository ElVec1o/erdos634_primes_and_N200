-- Draft/FluxCRow5Witness.lean: partial witnesses for Draft/FluxCRow5.lean (Theorem E, steps E1 to
-- E7).  Imported by `All`.
--
-- The joint hypothesis of `Row5.theoremE_twoPiThree` / `Row5.theoremE_sixty` /
-- `Row5.equilateral_boundary` / `Row5.area` is a `CongruentDissection` of an equilateral target by a
-- `2π/3` or `π/3` tile with `α ∉ ℚπ`.  Such tilings exist (e.g. Herdt's `N = 1944` by `(3,8,7)`), but
-- none is certified in Lean, so those theorems are conditionals.  What is exhibited:
-- * the tile hypotheses: `FluxPaperWitness.data357` (`(3,5,7)`, `2π/3`) and `data387` below
--   (`(3,8,7)`, `π/3`), both with the same irrational `α` (`cos α = 13/14`, `α357_irr`);
-- * the target hypothesis `∀ k, angleAt k = π/3` on an explicit equilateral `Tri` (`E2_angles`);
-- * `Row5.prime_pin` at `N = 5`, and a check that at the composite `N = 8` the pinning fails
--   (`s·t = 24`, `(s,t) = (4,6)`), so primality is needed there.
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxPaperWitness

open scoped Classical

namespace Erdos634.Draft.FluxCRow5Witness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.FluxPaperWitness

/-! ## The `(3,8,7)` tile: a `π/3` tile with `cos α = 13/14` -/

theorem det387 : det3 4 (4 * Real.sqrt 3) 3 0 0 0 ≠ 0 := by
  rw [show det3 4 (4 * Real.sqrt 3) 3 0 0 0 = -12 * Real.sqrt 3 by unfold det3; ring]
  have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  linarith

/-- The `(3,8,7)` triangle: `A = (4, 4√3)` (angle `α`), `B = (3, 0)` (angle `2π/3 − α`),
`C = (0, 0)` (angle `π/3`). -/
noncomputable def T387 : Tri := mkTri 4 (4 * Real.sqrt 3) 3 0 0 0 det387

theorem e01 : dist (T387.pts 0) (T387.pts 1) = 7 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 4 (4 * Real.sqrt 3)) (mkPt 3 0) ^ 2 = 7 ^ 2
  rw [dist_sq_mkPt]
  nlinarith [s3]

theorem e12 : dist (T387.pts 1) (T387.pts 2) = 3 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 3 0) (mkPt 0 0) ^ 2 = 3 ^ 2
  rw [dist_sq_mkPt]
  norm_num

theorem e20 : dist (T387.pts 2) (T387.pts 0) = 8 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 4 (4 * Real.sqrt 3)) ^ 2 = 8 ^ 2
  rw [dist_sq_mkPt]
  nlinarith [s3]

theorem angle0_387 : T387.angleAt 0 = α357 := by
  have hcos : Real.cos (T387.angleAt 0) = 13 / 14 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle' (ne_of_dist' e01 (by norm_num)).symm (ne_of_dist' e20 (by norm_num)),
      dist_comm (T387.pts 1) (T387.pts 0), e01, e20, e12]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) (cornerAngle_mem' _ _ _)
    (hcos.trans cos_α357.symm)

theorem angle2_387 : T387.angleAt 2 = Real.pi / 3 := by
  have hcos : Real.cos (T387.angleAt 2) = 1 / 2 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle' (ne_of_dist' e20 (by norm_num)).symm (ne_of_dist' e12 (by norm_num)),
      dist_comm (T387.pts 0) (T387.pts 2), e20, e12, e01]
    norm_num
  have hpi := Real.pi_pos
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩
    (hcos.trans Real.cos_pi_div_three.symm)

theorem angle1_387 : T387.angleAt 1 = 2 * Real.pi / 3 - α357 := by
  have h := T387.angleAt_sum
  rw [angle0_387, angle2_387] at h
  linarith

theorem opp_387 : T387.oppLen 0 = 3 ∧ T387.oppLen 1 = 8 ∧ T387.oppLen 2 = 7 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨e12, e20, e01⟩

/-- **The tile hypothesis of `Row5.theoremE_sixty` is satisfiable** (with `α ∉ ℚπ`). -/
theorem data387 : T387.SixtyData α357 3 8 7 :=
  ⟨Equiv.refl _, angle0_387, opp_387.1, angle1_387, opp_387.2.1, angle2_387, opp_387.2.2⟩

/-- Its tile values: `w₁ = −(a+b−c) = −4`, `w₂ = a+b+c = 18`. -/
theorem tileValues_387 :
    (wAt α357 α357_irr 0 0).tileValue T387 = -4 ∧ (wAt α357 α357_irr 1 0).tileValue T387 = 18 := by
  rw [sixty_tileValue_one T387 α357_irr data387, sixty_tileValue_two T387 α357_irr data387]
  norm_num

/-! ## An equilateral `Tri` -/

theorem detE : det3 0 0 2 0 1 (Real.sqrt 3) ≠ 0 := by
  rw [show det3 0 0 2 0 1 (Real.sqrt 3) = 2 * Real.sqrt 3 by unfold det3; ring]
  have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  positivity

noncomputable def E2 : Tri := mkTri 0 0 2 0 1 (Real.sqrt 3) detE

theorem f01 : dist (E2.pts 0) (E2.pts 1) = 2 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 2 0) ^ 2 = 2 ^ 2
  rw [dist_sq_mkPt]; norm_num

theorem f12 : dist (E2.pts 1) (E2.pts 2) = 2 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 2 0) (mkPt 1 (Real.sqrt 3)) ^ 2 = 2 ^ 2
  rw [dist_sq_mkPt]; nlinarith [s3]

theorem f20 : dist (E2.pts 2) (E2.pts 0) = 2 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 1 (Real.sqrt 3)) (mkPt 0 0) ^ 2 = 2 ^ 2
  rw [dist_sq_mkPt]; nlinarith [s3]

/-- **The target hypothesis `∀ k, angleAt k = π/3` is satisfiable.** -/
theorem E2_angles : ∀ k, E2.angleAt k = Real.pi / 3 := by
  have hpi := Real.pi_pos
  have key : ∀ k, Real.cos (E2.angleAt k) = 1 / 2 := by
    intro k
    fin_cases k
    · show Real.cos (E2.angleAt 0) = 1 / 2
      unfold Tri.angleAt
      simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
      rw [cos_cornerAngle' (ne_of_dist' f01 (by norm_num)).symm (ne_of_dist' f20 (by norm_num)),
        dist_comm (E2.pts 1) (E2.pts 0), f01, f20, f12]
      norm_num
    · show Real.cos (E2.angleAt 1) = 1 / 2
      unfold Tri.angleAt
      simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
      rw [cos_cornerAngle' (ne_of_dist' f12 (by norm_num)).symm (ne_of_dist' f01 (by norm_num)),
        dist_comm (E2.pts 2) (E2.pts 1), f12, f01, f20]
      norm_num
    · show Real.cos (E2.angleAt 2) = 1 / 2
      unfold Tri.angleAt
      simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
      rw [cos_cornerAngle' (ne_of_dist' f20 (by norm_num)).symm (ne_of_dist' f12 (by norm_num)),
        dist_comm (E2.pts 0) (E2.pts 2), f20, f12, f01]
      norm_num
  intro k
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩
    ((key k).trans Real.cos_pi_div_three.symm)

/-! ## E7 arithmetic: witness and a composite counterexample -/

/-- `Row5.prime_pin` at `N = 5`, `(s, t) = (3, 5)`. -/
theorem prime_pin_5 : ((3 : ℤ) = 3 ∧ (5 : ℤ) = (5 : ℕ)) ∨ ((3 : ℤ) = (5 : ℕ) ∧ (5 : ℤ) = 3) :=
  Row5.prime_pin (N := 5) (by norm_num) 3 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **Primality is needed.**  At `N = 8`, `(s, t) = (4, 6)` satisfies
`1 ≤ s, t ≤ N` and `s·t = 3N`, but `{s, t} ≠ {3, N}`. -/
theorem prime_pin_needs_prime :
    ∃ s t : ℤ, 1 ≤ s ∧ s ≤ (8 : ℕ) ∧ 1 ≤ t ∧ t ≤ (8 : ℕ) ∧ s * t = 3 * (8 : ℕ) ∧
      ¬ ((s = 3 ∧ t = (8 : ℕ)) ∨ (s = (8 : ℕ) ∧ t = 3)) :=
  ⟨4, 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos634.Draft.FluxCRow5Witness

#print axioms Erdos634.Draft.FluxCRow5Witness.data387
#print axioms Erdos634.Draft.FluxCRow5Witness.tileValues_387
#print axioms Erdos634.Draft.FluxCRow5Witness.E2_angles
#print axioms Erdos634.Draft.FluxCRow5Witness.prime_pin_5
#print axioms Erdos634.Draft.FluxCRow5Witness.prime_pin_needs_prime
