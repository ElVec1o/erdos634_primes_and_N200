/-
Draft/ThetaKill.lean  In `AllThreshold`.

**Kill set of the isosceles targets `θ_t(e, f)`** (apex `α`, legs `t f b`, base `t e b`, base angles `α + β`, `b = f² − e²`).
* Form 1 (`theta_te_ge`): if `θ_t(e,f)` is tiled (a `CongruentDissection` of a triangle with sides `t f b, t f b, t e b` by the tile `(ef, b, f²)`, any number of tiles), then `t e ≥ 2 f`.
  The proof: `SideRunGThetaMain.theta_word_hasSides` gives a base word `t e b = x (ef) + y b + z f²` with `z ≥ f` (`S5WordF`); the arithmetic (`s5wordF_ge`): reduce mod `b`: `b ∣ x e + z f`, `x e + z f ≥ f² > b`, so
  `x e + z f = j b` with `j ≥ 2`, and `t e = f j + y ≥ 2 f`.  (The existing `AtomShape.s5word_te` has `z ≥ 1` and gives `f ≤ t e`.)
* Form 2, the thick closed form (`theta_thick`): for `e = f − 1` a tiling needs `t ≥ f + 2` (`s5wordF_thick`: mod `f`, `x ≡ m`, where `x e + z f = m b`, `m = (t e − y)/f`; if `m < f` then `x ≥ m` and `z f ≤ m f`, so `z < f`; hence `m ≥ f` and `t (f − 1) ≥ f²`).
* The instance form: `s5inst_of_te_lt_2f` (`t e < 2 f ⟹ S5Inst t e f`) and `s5inst_thick_lt` (`e = f − 1`, `t < f + 2 ⟹ S5Inst t e f`).
* Instances (no search, no certificate): `s5inst_2_4_7`, `s5inst_2_5_8` (form 1), `s5inst_3_7_8`, `s5inst_3_9_10` (form 2), and `(2,1,4)`, `(3,1,4)` (form 1), `(2,7,8)`, `(2,9,10)`, `(2,11,12)` (form 2).
  They are the statements of `OpenReductionsNsq.s5inst_2_4_7`, `N156Red.s5inst_2_5_8`, `N135Red.s5inst_3_7_8`, `N171.s5inst_3_9_10`, `N566076.s5inst_2_1_4`, `N135Red.s5inst_3_1_4`, `N566076.s5inst_2_7_8`, `N566076.s5inst_2_9_10`, `N92.s5inst_2_11_12`,
  which are certified one at a time; this file does not import them (their import closures contain hundreds of certificate modules).
* `theta_e1`: on every `θ` target of the members `(1, f)`: a tiling of `θ_t(1,f)` has `t ≥ 2 f`, hence its longest side `t f (f² − 1) ≥ 2 f² (f² − 1) ≥ f⁴ = c²`.  The shape of the target (apex `α`, legs `t f b`, base `t e b` in the units of the tile) is the shape
  step `NSQM.s5_shape`, `atom_shape_te`; here the target is given by its side lengths.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGThetaMain
import Erdos634.Draft.S5Family

open scoped Classical

namespace Erdos634.Draft.ThetaKill

open Erdos634.Geometry Erdos634.Draft.NSQM
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.Draft.UniformThreshold (hasSides_congr)

/-! ## 1. The arithmetic -/

/-- a base word `t e b = P (ef) + Q b + R f²` with at least `f` edges `c` -/
def S5WordF (t e f : ℤ) : Prop :=
  ∃ P Q R : ℕ, f ≤ R ∧ t * e * (f ^ 2 - e ^ 2) = P * (e * f) + Q * (f ^ 2 - e ^ 2) + R * f ^ 2

/-- **S8, the arithmetic**: a base word with at least `f` edges `c` forces `2 f ≤ t e`. -/
theorem s5wordF_ge {t e f : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (h : S5WordF t e f) :
    2 * f ≤ t * e := by
  obtain ⟨P, Q, R, hR, hw⟩ := h
  have hP0 : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg _
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
  have hf : 0 < f := by linarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hRf : f ≤ (R : ℤ) := hR
  have hc : IsCoprime (f ^ 2 - e ^ 2) f :=
    ((Erdos634.Draft.S5PinArith.coprime_ab hcop).of_mul_left_right).symm
  have hdvd : (f ^ 2 - e ^ 2) ∣ ((P : ℤ) * e + R * f) := by
    have h1 : (f ^ 2 - e ^ 2) ∣ ((P : ℤ) * e + R * f) * f := ⟨t * e - Q, by linear_combination -hw⟩
    exact hc.dvd_of_dvd_mul_right h1
  obtain ⟨j, hj⟩ := hdvd
  have hpos : f * f ≤ (P : ℤ) * e + R * f := by
    have h1 := mul_nonneg hP0 he.le
    have h2 := mul_le_mul_of_nonneg_right hRf hf.le
    linarith
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hj1 : j ≤ 1 := by omega
    have h1 := mul_le_mul_of_nonneg_left hj1 hb.le
    nlinarith [sq_pos_of_pos he]
  have hfj : f * j + Q = t * e := by
    have h2 : (f * j + Q - t * e) * (f ^ 2 - e ^ 2) = 0 := by
      have h3 : ((P : ℤ) * e + R * f) * f = (f ^ 2 - e ^ 2) * j * f := by rw [hj]
      linear_combination -hw - h3
    have := (mul_eq_zero.mp h2).resolve_right hb.ne'
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hj2 hf.le]

/-- **S8, the thick closed form, arithmetic**: for `e = f − 1` a base word with at least `f` edges `c` forces `t ≥ f + 2`. -/
theorem s5wordF_thick {t f : ℤ} (hf : 2 ≤ f) (h : S5WordF t (f - 1) f) : f + 2 ≤ t := by
  obtain ⟨P, Q, R, hR, hw⟩ := h
  have hP0 : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg _
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
  have hRf : f ≤ (R : ℤ) := hR
  have hf0 : 0 < f := by linarith
  have hb : f ^ 2 - (f - 1) ^ 2 = 2 * f - 1 := by ring
  rw [hb] at hw
  have hc : IsCoprime (2 * f - 1) f := ⟨-1, 2, by ring⟩
  have hd : f ∣ (t * (f - 1) - Q) * (2 * f - 1) :=
    ⟨(P : ℤ) * (f - 1) + R * f, by linear_combination hw⟩
  obtain ⟨m, hm⟩ : f ∣ t * (f - 1) - Q := hc.symm.dvd_of_dvd_mul_right hd
  -- `P (f − 1) + R f = m (2 f − 1)`
  have hPR : (P : ℤ) * (f - 1) + R * f = m * (2 * f - 1) := by
    have h1 : f * ((P : ℤ) * (f - 1) + R * f - m * (2 * f - 1)) = 0 := by
      linear_combination -hw + (2 * f - 1) * hm
    have := (mul_eq_zero.mp h1).resolve_left hf0.ne'
    linarith
  have hQm : f * m ≤ t * (f - 1) := by linarith
  -- `m ≥ f`
  have hmf : f ≤ m := by
    by_contra hlt
    have hm1 : m < f := by omega
    have hm0 : 0 < m := by
      by_contra hle
      have hle' : m ≤ 0 := by omega
      have h1 : 0 ≤ (P : ℤ) * (f - 1) := mul_nonneg hP0 (by linarith)
      have h2 : f * f ≤ (R : ℤ) * f := mul_le_mul_of_nonneg_right hRf hf0.le
      have h3 : m * (2 * f - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle' (by linarith)
      linarith [mul_pos hf0 hf0]
    -- `P - m = f (P + R - 2 m)`
    have hn : (P : ℤ) - m = f * ((P : ℤ) + R - 2 * m) := by linear_combination (-1 : ℤ) * hPR
    have hn0 : 0 ≤ (P : ℤ) + R - 2 * m := by
      by_contra hneg
      have hneg' : (P : ℤ) + R - 2 * m ≤ -1 := by omega
      have := mul_le_mul_of_nonneg_left hneg' hf0.le
      linarith
    have hPm : m ≤ (P : ℤ) := by linarith [mul_nonneg hf0.le hn0]
    -- `R f = m (2 f − 1) − P (f − 1) ≤ m f`
    have hRm : (R : ℤ) ≤ m := by
      have h0 := mul_le_mul_of_nonneg_right hPm (by linarith : (0 : ℤ) ≤ f - 1)
      have h1 : (R : ℤ) * f ≤ m * f := by linarith
      exact le_of_mul_le_mul_right h1 hf0
    linarith
  by_contra hlt
  have ht1 : t ≤ f + 1 := by omega
  nlinarith [mul_le_mul_of_nonneg_right ht1 (by linarith : (0 : ℤ) ≤ f - 1), mul_le_mul_of_nonneg_left hmf hf0.le]

/-! ## 2. The base word of a dissection of `θ_t(e, f)` -/

/-- **S7 in integer form**: a dissection of `θ_t(e, f)` has a base word with at least `f` edges `c`. -/
theorem theta_word {N : ℕ} (D : CongruentDissection N) {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f)
    (hT : HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      ((t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hM : HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : S5WordF t e f := by
  have hf0 : 0 ≤ f := by linarith
  lift e to ℕ using he.le
  lift f to ℕ using hf0
  have he1 : 1 ≤ e := by exact_mod_cast he
  have hef' : e < f := by exact_mod_cast hef
  have hco : Nat.Coprime e f := Nat.isCoprime_iff_coprime.mp hcop
  have hs : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hT' := hT
  push_cast at hT'
  have hM' := hM
  push_cast at hM'
  obtain ⟨x, y, z, hxyz, hz⟩ := Erdos634.Draft.SideRunGT.theta_word_hasSides e f he1 hef' hco hs D
    (hasSides_congr hT' (by ring) (by ring) (by ring)) hM'
  refine ⟨x, y, z, by exact_mod_cast hz, ?_⟩
  have h2 : ((t * (e : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) : ℤ) : ℝ)
      = (((x : ℤ) * ((e : ℤ) * (f : ℤ)) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z : ℤ) * (f : ℤ) ^ 2 : ℤ) : ℝ) := by
    push_cast
    linear_combination -hxyz
  exact_mod_cast h2

/-! ## 3. S8 -/

/-- **S8, form 1**: if `θ_t(e, f)` is tiled (a congruent dissection of the triangle with sides `t f b, t f b, t e b` by the tile `(ef, b, f²)`; any number of tiles, reflections allowed), then `t e ≥ 2 f`. -/
theorem theta_te_ge {N : ℕ} (D : CongruentDissection N) {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f)
    (hT : HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      ((t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hM : HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : 2 * f ≤ t * e :=
  s5wordF_ge he hef hcop (theta_word D ht he hef hcop hT hM)

/-- **S8, form 2 (thick members)**: for `e = f − 1`, if `θ_t(f − 1, f)` is tiled then `t ≥ f + 2`. -/
theorem theta_thick {N : ℕ} (D : CongruentDissection N) {t f : ℤ} (hf : 2 ≤ f) (ht : 0 < t)
    (hT : HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - ((f - 1 : ℤ) : ℝ) ^ 2))
      ((t : ℝ) * f * ((f : ℝ) ^ 2 - ((f - 1 : ℤ) : ℝ) ^ 2)) ((t : ℝ) * ((f - 1 : ℤ) : ℝ) * ((f : ℝ) ^ 2 - ((f - 1 : ℤ) : ℝ) ^ 2)))
    (hM : HasSides D.model (((f - 1 : ℤ) : ℝ) * f) ((f : ℝ) ^ 2 - ((f - 1 : ℤ) : ℝ) ^ 2) ((f : ℝ) ^ 2)) : f + 2 ≤ t :=
  s5wordF_thick hf (theta_word D ht (by linarith) (by linarith) ⟨-1, 1, by ring⟩ hT hM)

/-! ## 4. The instance form, and the regression -/

/-- the hypotheses of `S5Inst` as `HasSides` -/
theorem s5_hyps_to_hasSides {N : ℕ} (D : CongruentDissection N) {t e f : ℤ}
    (h0 : D.target.oppLen 0 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (h1 : D.target.oppLen 1 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (h2 : D.target.oppLen 2 = (t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hm : ∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2) :
    HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      ((t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
    HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  obtain ⟨σ, m0, m1, m2⟩ := hm
  obtain ⟨s1, s2, s3⟩ := Erdos634.Geometry.GapE120Dis.sides_of_perm D.model σ
  refine ⟨⟨Equiv.refl _, ?_, ?_, ?_⟩, ⟨σ, s1.trans m0, (dist_comm _ _).trans (s2.trans m1), s3.trans m2⟩⟩
  · simp only [Equiv.refl_apply]; exact h0
  · simp only [Equiv.refl_apply]; exact h1
  · simp only [Equiv.refl_apply]; exact h2

/-- **S8, form 1, as an S5 instance**: `t e < 2 f` gives `S5Inst t e f`. -/
theorem s5inst_of_te_lt_2f {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    (hlt : t * e < 2 * f) : S5Inst t e f := by
  intro N D h0 h1 h2 hm
  obtain ⟨hT, hM⟩ := s5_hyps_to_hasSides D h0 h1 h2 hm
  have := theta_te_ge D ht he hef hcop hT hM
  linarith

/-- **S8, form 2, as an S5 instance**: `e = f − 1`, `t < f + 2` gives `S5Inst t e f`. -/
theorem s5inst_thick_lt {t e f : ℤ} (hf : 2 ≤ f) (ht : 0 < t) (he : e = f - 1) (hlt : t < f + 2) :
    S5Inst t e f := by
  subst he
  intro N D h0 h1 h2 hm
  obtain ⟨hT, hM⟩ := s5_hyps_to_hasSides D h0 h1 h2 hm
  have := theta_thick D hf ht hT hM
  linarith

/-- the nine instances, decided without search and without certificate -/
theorem s5inst_2_4_7 : S5Inst 2 4 7 :=
  s5inst_of_te_lt_2f (by norm_num) (by norm_num) (by norm_num) ⟨2, -1, by norm_num⟩ (by norm_num)
theorem s5inst_2_5_8 : S5Inst 2 5 8 :=
  s5inst_of_te_lt_2f (by norm_num) (by norm_num) (by norm_num) ⟨5, -3, by norm_num⟩ (by norm_num)
theorem s5inst_2_1_4 : S5Inst 2 1 4 :=
  s5inst_of_te_lt_2f (by norm_num) (by norm_num) (by norm_num) ⟨1, 0, by norm_num⟩ (by norm_num)
theorem s5inst_3_1_4 : S5Inst 3 1 4 :=
  s5inst_of_te_lt_2f (by norm_num) (by norm_num) (by norm_num) ⟨1, 0, by norm_num⟩ (by norm_num)
theorem s5inst_3_7_8 : S5Inst 3 7 8 := s5inst_thick_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem s5inst_3_9_10 : S5Inst 3 9 10 := s5inst_thick_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem s5inst_2_7_8 : S5Inst 2 7 8 := s5inst_thick_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem s5inst_2_9_10 : S5Inst 2 9 10 := s5inst_thick_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem s5inst_2_11_12 : S5Inst 2 11 12 := s5inst_thick_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## 5. S9: R1 on the `θ` targets of the members `(1, f)` -/

/-- **S9**: a tiling of `θ_t(1, f)` (the triangle with sides `t f (f² − 1)`, `t f (f² − 1)`, `t (f² − 1)`, by the tile `(f, f² − 1, f²)`; any number of tiles, reflections allowed) has `t ≥ 2 f`, hence its longest side `t f (f² − 1)` is at least
`2 f² (f² − 1) ≥ f⁴ = c²` (`c = f²` the longest side of the tile). -/
theorem theta_e1 {N : ℕ} (D : CongruentDissection N) {t f : ℤ} (hf : 2 ≤ f) (ht : 0 < t)
    (hT : HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - 1)) ((t : ℝ) * f * ((f : ℝ) ^ 2 - 1))
      ((t : ℝ) * ((f : ℝ) ^ 2 - 1)))
    (hM : HasSides D.model (f : ℝ) ((f : ℝ) ^ 2 - 1) ((f : ℝ) ^ 2)) :
    2 * f ≤ t ∧ (f : ℝ) ^ 4 ≤ (t : ℝ) * f * ((f : ℝ) ^ 2 - 1) := by
  have h2 : 2 * f ≤ t * 1 := theta_te_ge D ht one_pos (by linarith) isCoprime_one_left
    (hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring))
    (hasSides_congr hM (by push_cast; ring) (by push_cast; ring) (by ring))
  have h2' : 2 * f ≤ t := by linarith
  refine ⟨h2', ?_⟩
  have hfR : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have htR : (2 : ℝ) * f ≤ t := by exact_mod_cast h2'
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - 1 := by nlinarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hf2 : (4 : ℝ) ≤ (f : ℝ) ^ 2 := by nlinarith
  have h4 : (f : ℝ) ^ 4 ≤ 2 * (f : ℝ) ^ 2 * ((f : ℝ) ^ 2 - 1) := by
    nlinarith [mul_nonneg (sq_nonneg (f : ℝ)) (by linarith : (0 : ℝ) ≤ (f : ℝ) ^ 2 - 2)]
  have hpos := mul_pos hf0 hb
  calc (f : ℝ) ^ 4 ≤ 2 * (f : ℝ) ^ 2 * ((f : ℝ) ^ 2 - 1) := h4
    _ = (2 * f) * ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) := by ring
    _ ≤ (t : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) := mul_le_mul_of_nonneg_right htR hpos.le
    _ = (t : ℝ) * f * ((f : ℝ) ^ 2 - 1) := by ring

/-- **S9 as an S5 instance**: `S5Inst t 1 f` for `t < 2 f`. -/
theorem s5inst_e1_lt {t f : ℤ} (ht : 0 < t) (hf : 2 ≤ f) (hlt : t < 2 * f) : S5Inst t 1 f :=
  s5inst_of_te_lt_2f ht one_pos (by linarith) isCoprime_one_left (by linarith)

end Erdos634.Draft.ThetaKill

#print axioms Erdos634.Draft.ThetaKill.s5wordF_ge
#print axioms Erdos634.Draft.ThetaKill.s5wordF_thick
#print axioms Erdos634.Draft.ThetaKill.theta_word
#print axioms Erdos634.Draft.ThetaKill.theta_te_ge
#print axioms Erdos634.Draft.ThetaKill.theta_thick
#print axioms Erdos634.Draft.ThetaKill.s5inst_of_te_lt_2f
#print axioms Erdos634.Draft.ThetaKill.s5inst_thick_lt
#print axioms Erdos634.Draft.ThetaKill.s5inst_2_4_7
#print axioms Erdos634.Draft.ThetaKill.s5inst_2_5_8
#print axioms Erdos634.Draft.ThetaKill.s5inst_3_7_8
#print axioms Erdos634.Draft.ThetaKill.s5inst_3_9_10
#print axioms Erdos634.Draft.ThetaKill.theta_e1
