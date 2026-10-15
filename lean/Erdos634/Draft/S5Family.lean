/-
Draft/S5Family.lean -- the S5 family `(2, k, k+1)` has no tiling, for every `k ≥ 1`, stated from side lengths only.

`s5inst_of_no_word2`: an S5 instance `(t, e, f)` (isosceles target with legs `t f (f²−e²)` and base `t e (f²−e²)`, tile
`(e f, f²−e², f²)`, `0 < e < f` coprime) whose base has no word `P·ef + Q·(f²−e²) + R·f²` with `R ≥ 2` has no dissection.
The angle data (`3α + 2β = π`, `α/π` irrational, base angles `α + β`) are derived from the sides (`BADAngles.tile_angles`,
law of cosines), then `RATrap2.s5_base_two` applies.

`s5_family_2k`: `S5Inst 2 k (k+1)` for every `k ≥ 1`; `s5_family_2k_hasSides`: the same with target and tile given by
their side lengths in any vertex order.

Composite tile counts (`N = 4(2k+1)`).  No sorry, no native_decide.
-/
import Erdos634.Draft.RATrap2
import Erdos634.BADAngles
import Erdos634.Draft.HasSidesPerm

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.BADL2 Erdos634.Draft.FDBBaseBetaE1

namespace Erdos634.Draft.NSQM

/-- **Angle data of an S5 instance from its side lengths**: `α/π` irrational, `3α + 2β = π`, the model data, and the
base angles `α + β` of the target (`BADAngles.tile_angles` and the law of cosines). -/
theorem s5_angles {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f)
    {N : ℕ} (D : CongruentDissection N)
    (h0 : D.target.oppLen 0 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (h1 : D.target.oppLen 1 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (h2 : D.target.oppLen 2 = (t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (σ : Equiv.Perm (Fin 3)) (hm0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (hm1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (hm2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2) :
    IrrPi (D.model.angleAt (σ 0)) ∧
    3 * D.model.angleAt (σ 0) + 2 * D.model.angleAt (σ 1) = Real.pi ∧
    D.model.ThreeAlphaData (D.model.angleAt (σ 0)) (D.model.angleAt (σ 1))
      ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∧
    D.target.angleAt 0 = D.model.angleAt (σ 0) + D.model.angleAt (σ 1) ∧
    D.target.angleAt 1 = D.model.angleAt (σ 0) + D.model.angleAt (σ 1) := by
  obtain ⟨-, hrel, hγ, hirr⟩ := tile_angles D.model σ e f he hef hm0 hm1 hm2
  obtain ⟨-, -, c2⟩ := cos_laws_perm D.model σ _ _ _ hm0 hm1 hm2
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hfR : (0 : ℝ) < f := by exact_mod_cast lt_trans he hef
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  obtain ⟨α0, α1⟩ := ang_bounds D.model (σ 0)
  obtain ⟨β0, β1⟩ := ang_bounds D.model (σ 1)
  obtain ⟨γ0, γ1⟩ := ang_bounds D.model (σ 2)
  -- `cos (α + β) = e / (2 f)`
  have hcab : Real.cos (D.model.angleAt (σ 0) + D.model.angleAt (σ 1)) = (e : ℝ) / (2 * f) := by
    have h3 : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) = Real.pi - D.model.angleAt (σ 2) := by linarith
    rw [h3, Real.cos_pi_sub, eq_div_iff (by positivity)]
    have hpos : (0 : ℝ) < 2 * ((e : ℝ) * f) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
    apply mul_left_cancel₀ hpos.ne'
    linear_combination (-(2 * (f : ℝ))) * c2
  -- the base angles of the target
  obtain ⟨t0, t1, -⟩ := cos_laws D.target
  rw [h0, h1, h2] at t0 t1
  have hpos : (0 : ℝ) < 2 * ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * ((t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    positivity
  have hT0 : Real.cos (D.target.angleAt 0) = (e : ℝ) / (2 * f) := by
    rw [eq_div_iff (by positivity)]
    apply mul_left_cancel₀ hpos.ne'
    linear_combination (2 * (f : ℝ)) * t0
  have hT1 : Real.cos (D.target.angleAt 1) = (e : ℝ) / (2 * f) := by
    rw [eq_div_iff (by positivity)]
    apply mul_left_cancel₀ hpos.ne'
    linear_combination (2 * (f : ℝ)) * t1
  have hmem : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by linarith, by linarith⟩
  exact ⟨hirr, hrel, ⟨σ, rfl, hm0, rfl, hm1, by rw [hγ]; linarith, hm2⟩,
    Real.injOn_cos ⟨(ang_bounds D.target 0).1, (ang_bounds D.target 0).2⟩ hmem (hT0.trans hcab.symm),
    Real.injOn_cos ⟨(ang_bounds D.target 1).1, (ang_bounds D.target 1).2⟩ hmem (hT1.trans hcab.symm)⟩

/-- **The base of a dissected S5 target has a word with two `c`-edges** (side-length form of `s5_base_two`). -/
theorem s5_base_word2 {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    {N : ℕ} (D : CongruentDissection N)
    (h0 : D.target.oppLen 0 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (h1 : D.target.oppLen 1 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (h2 : D.target.oppLen 2 = (t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hm : ∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2) :
    S5Word2 t e f := by
  obtain ⟨σ, hm0, hm1, hm2⟩ := hm
  obtain ⟨hirr, hrel, hmod, hP0, hP1⟩ := s5_angles ht he hef D h0 h1 h2 σ hm0 hm1 hm2
  have hwa : ∀ x y z : ℕ, (e : ℝ) * f = x * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 →
      x + y + z = 1 := by
    intro x y z h
    apply Erdos634.Draft.S5PinArith.word_a_single he hef hcop x y z
    exact_mod_cast h.symm
  have hwb : ∀ x y z : ℕ, (f : ℝ) ^ 2 - (e : ℝ) ^ 2
        = x * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 → x + y + z = 1 := by
    intro x y z h
    apply Erdos634.Draft.S5PinArith.word_b_single he hef hcop x y z
    exact_mod_cast h.symm
  obtain ⟨P, Q, R, hR, hw⟩ := s5_base_two (by have := D.pos; omega) D hirr hrel hmod hP0 hP1 hwa hwb
  refine ⟨P, Q, R, hR, ?_⟩
  rw [h2] at hw
  exact_mod_cast hw

/-- **An S5 instance whose base has no word with two `c`-edges has no dissection.** -/
theorem s5inst_of_no_word2 {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    (hno : ¬ S5Word2 t e f) : S5Inst t e f :=
  fun D h0 h1 h2 hm => hno (s5_base_word2 ht he hef hcop D h0 h1 h2 hm)

/-- **Theorem**: for every `k ≥ 1`, the isosceles triangle with legs `2(k+1)(2k+1)` and base `2k(2k+1)`
has no dissection into triangles congruent to the triangle with sides `k(k+1)`, `2k+1`, `(k+1)²`
(any number of tiles; reflections allowed). -/
theorem s5_family_2k {k : ℤ} (hk : 1 ≤ k) : S5Inst 2 k (k + 1) :=
  s5inst_of_no_word2 (by norm_num) (by omega) (by omega) ⟨-1, 1, by ring⟩ (s5word2_k hk)

open Erdos634.Geometry.GapE120Dis in
/-- an S5 instance, with target and tile given by their side lengths in any vertex order -/
theorem s5inst_hasSides {t e f : ℤ} (h : S5Inst t e f) {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      ((t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hM : HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : False := by
  obtain ⟨τ, a1, a2, a3⟩ := hT
  obtain ⟨σ, m1, m2, m3⟩ := hM
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  exact h (D.relabelTarget' τ) a1 a2 a3
    ⟨σ, s1.symm.trans m1, s2.symm.trans ((dist_comm _ _).trans m2), s3.symm.trans m3⟩

open Erdos634.Geometry.GapE120Dis in
/-- `s5_base_word2`, with target and tile given by their side lengths in any vertex order -/
theorem s5_base_word2_hasSides {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      ((t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hM : HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : S5Word2 t e f := by
  obtain ⟨τ, a1, a2, a3⟩ := hT
  obtain ⟨σ, m1, m2, m3⟩ := hM
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  exact s5_base_word2 ht he hef hcop (D.relabelTarget' τ) a1 a2 a3
    ⟨σ, s1.symm.trans m1, s2.symm.trans ((dist_comm _ _).trans m2), s3.symm.trans m3⟩

/-- **Theorem 1, side-length form.**  `k ≥ 1`: no triangle with sides `2(k+1)(2k+1)`, `2(k+1)(2k+1)`, `2k(2k+1)` is
dissected into triangles with sides `k(k+1)`, `2k+1`, `(k+1)²`. -/
theorem s5_family_2k_hasSides {k : ℕ} (hk : 1 ≤ k) {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target (2 * ((k : ℝ) + 1) * (2 * k + 1)) (2 * ((k : ℝ) + 1) * (2 * k + 1))
      (2 * (k : ℝ) * (2 * k + 1)))
    (hM : HasSides D.model ((k : ℝ) * (k + 1)) (2 * k + 1) (((k : ℝ) + 1) ^ 2)) : False := by
  have h : S5Inst 2 (k : ℤ) ((k : ℤ) + 1) := s5_family_2k (by exact_mod_cast hk)
  refine s5inst_hasSides h D ?_ ?_
  · convert hT using 1 <;> push_cast <;> ring
  · convert hM using 1 <;> push_cast <;> ring

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.s5inst_of_no_word2
#print axioms Erdos634.Draft.NSQM.s5_family_2k
#print axioms Erdos634.Draft.NSQM.s5_family_2k_hasSides
#print axioms Erdos634.Draft.NSQM.s5_base_word2_hasSides
